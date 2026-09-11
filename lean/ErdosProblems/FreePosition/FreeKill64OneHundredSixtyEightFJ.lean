import Erdos249257.DiagonalPincerCertificatesT64

/- Kernel-checked off-diagonal certificate at a freely chosen position. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def oneHundredSixtyEightFJFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem oneHundredSixtyEightFJFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : oneHundredSixtyEightFJFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [oneHundredSixtyEightFJFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [oneHundredSixtyEightFJFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then oneHundredSixtyEightFJFastPow a n * oneHundredSixtyEightFJFastPow a n * a else oneHundredSixtyEightFJFastPow a n * oneHundredSixtyEightFJFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_oneHundredSixtyEightFJ_2 : Nat.Prime 2 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_3 : Nat.Prime 3 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_5 : Nat.Prime 5 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_7 : Nat.Prime 7 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_11 : Nat.Prime 11 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_13 : Nat.Prime 13 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_17 : Nat.Prime 17 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_19 : Nat.Prime 19 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_23 : Nat.Prime 23 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_29 : Nat.Prime 29 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_31 : Nat.Prime 31 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_37 : Nat.Prime 37 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_41 : Nat.Prime 41 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_43 : Nat.Prime 43 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_47 : Nat.Prime 47 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_53 : Nat.Prime 53 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_59 : Nat.Prime 59 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_61 : Nat.Prime 61 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_67 : Nat.Prime 67 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_71 : Nat.Prime 71 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_73 : Nat.Prime 73 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_79 : Nat.Prime 79 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_83 : Nat.Prime 83 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_89 : Nat.Prime 89 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_97 : Nat.Prime 97 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_101 : Nat.Prime 101 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_103 : Nat.Prime 103 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_107 : Nat.Prime 107 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_109 : Nat.Prime 109 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_113 : Nat.Prime 113 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_127 : Nat.Prime 127 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_131 : Nat.Prime 131 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_137 : Nat.Prime 137 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_139 : Nat.Prime 139 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_149 : Nat.Prime 149 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_151 : Nat.Prime 151 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_157 : Nat.Prime 157 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_163 : Nat.Prime 163 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_167 : Nat.Prime 167 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_179 : Nat.Prime 179 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_181 : Nat.Prime 181 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_191 : Nat.Prime 191 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_193 : Nat.Prime 193 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_197 : Nat.Prime 197 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_199 : Nat.Prime 199 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_211 : Nat.Prime 211 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_223 : Nat.Prime 223 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_229 : Nat.Prime 229 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_233 : Nat.Prime 233 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_251 : Nat.Prime 251 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_257 : Nat.Prime 257 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_263 : Nat.Prime 263 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_269 : Nat.Prime 269 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_271 : Nat.Prime 271 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_277 : Nat.Prime 277 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_283 : Nat.Prime 283 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_293 : Nat.Prime 293 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_307 : Nat.Prime 307 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_311 : Nat.Prime 311 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_313 : Nat.Prime 313 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_331 : Nat.Prime 331 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_337 : Nat.Prime 337 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_347 : Nat.Prime 347 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_353 : Nat.Prime 353 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_359 : Nat.Prime 359 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_367 : Nat.Prime 367 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_373 : Nat.Prime 373 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_379 : Nat.Prime 379 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_383 : Nat.Prime 383 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_397 : Nat.Prime 397 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_419 : Nat.Prime 419 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_431 : Nat.Prime 431 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_443 : Nat.Prime 443 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_449 : Nat.Prime 449 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_457 : Nat.Prime 457 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_461 : Nat.Prime 461 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_463 : Nat.Prime 463 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_467 : Nat.Prime 467 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_479 : Nat.Prime 479 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_503 : Nat.Prime 503 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_541 : Nat.Prime 541 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_547 : Nat.Prime 547 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_557 : Nat.Prime 557 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_569 : Nat.Prime 569 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_577 : Nat.Prime 577 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_617 : Nat.Prime 617 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_647 : Nat.Prime 647 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_653 : Nat.Prime 653 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_673 : Nat.Prime 673 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_701 : Nat.Prime 701 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_709 : Nat.Prime 709 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_719 : Nat.Prime 719 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_727 : Nat.Prime 727 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_739 : Nat.Prime 739 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_751 : Nat.Prime 751 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_757 : Nat.Prime 757 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_761 : Nat.Prime 761 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_773 : Nat.Prime 773 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_787 : Nat.Prime 787 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_797 : Nat.Prime 797 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_809 : Nat.Prime 809 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_821 : Nat.Prime 821 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_829 : Nat.Prime 829 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_853 : Nat.Prime 853 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_859 : Nat.Prime 859 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_863 : Nat.Prime 863 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_881 : Nat.Prime 881 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_887 : Nat.Prime 887 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_907 : Nat.Prime 907 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_967 : Nat.Prime 967 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_983 : Nat.Prime 983 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_1051 : Nat.Prime 1051 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_1109 : Nat.Prime 1109 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_1129 : Nat.Prime 1129 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_1151 : Nat.Prime 1151 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_1153 : Nat.Prime 1153 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_1171 : Nat.Prime 1171 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_1193 : Nat.Prime 1193 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_1217 : Nat.Prime 1217 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_1231 : Nat.Prime 1231 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_1237 : Nat.Prime 1237 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_1259 : Nat.Prime 1259 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_1283 : Nat.Prime 1283 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_1289 : Nat.Prime 1289 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_1301 : Nat.Prime 1301 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_1319 : Nat.Prime 1319 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_1321 : Nat.Prime 1321 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_1399 : Nat.Prime 1399 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_1427 : Nat.Prime 1427 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_1559 : Nat.Prime 1559 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_1583 : Nat.Prime 1583 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_1621 : Nat.Prime 1621 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_1627 : Nat.Prime 1627 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_1667 : Nat.Prime 1667 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_1709 : Nat.Prime 1709 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_1733 : Nat.Prime 1733 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_1777 : Nat.Prime 1777 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_1811 : Nat.Prime 1811 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_1861 : Nat.Prime 1861 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_1933 : Nat.Prime 1933 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_1949 : Nat.Prime 1949 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_1951 : Nat.Prime 1951 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_1987 : Nat.Prime 1987 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_2029 : Nat.Prime 2029 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_2131 : Nat.Prime 2131 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_2143 : Nat.Prime 2143 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_2179 : Nat.Prime 2179 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_2269 : Nat.Prime 2269 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_2311 : Nat.Prime 2311 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_2351 : Nat.Prime 2351 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_2521 : Nat.Prime 2521 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_2551 : Nat.Prime 2551 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_2689 : Nat.Prime 2689 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_2803 : Nat.Prime 2803 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_2971 : Nat.Prime 2971 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_3011 : Nat.Prime 3011 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_3163 : Nat.Prime 3163 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_3169 : Nat.Prime 3169 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_3229 : Nat.Prime 3229 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_3347 : Nat.Prime 3347 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_3433 : Nat.Prime 3433 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_3623 : Nat.Prime 3623 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_3637 : Nat.Prime 3637 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_3779 : Nat.Prime 3779 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_3931 : Nat.Prime 3931 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_3967 : Nat.Prime 3967 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_4027 : Nat.Prime 4027 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_4241 : Nat.Prime 4241 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_4253 : Nat.Prime 4253 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_4273 : Nat.Prime 4273 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_4483 : Nat.Prime 4483 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_4519 : Nat.Prime 4519 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_4733 : Nat.Prime 4733 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_4759 : Nat.Prime 4759 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_4871 : Nat.Prime 4871 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_5147 : Nat.Prime 5147 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_5153 : Nat.Prime 5153 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_5189 : Nat.Prime 5189 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_5507 : Nat.Prime 5507 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_5521 : Nat.Prime 5521 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_5651 : Nat.Prime 5651 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_5711 : Nat.Prime 5711 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_5843 : Nat.Prime 5843 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_5981 : Nat.Prime 5981 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_6323 : Nat.Prime 6323 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_6691 : Nat.Prime 6691 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_6863 : Nat.Prime 6863 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_6991 : Nat.Prime 6991 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_7237 : Nat.Prime 7237 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_7297 : Nat.Prime 7297 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_7517 : Nat.Prime 7517 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_7561 : Nat.Prime 7561 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_7717 : Nat.Prime 7717 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_7883 : Nat.Prime 7883 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_8243 : Nat.Prime 8243 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_8273 : Nat.Prime 8273 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_8689 : Nat.Prime 8689 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_8693 : Nat.Prime 8693 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_9769 : Nat.Prime 9769 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_9781 : Nat.Prime 9781 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_10061 : Nat.Prime 10061 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_10303 : Nat.Prime 10303 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_10781 : Nat.Prime 10781 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_10789 : Nat.Prime 10789 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_11069 : Nat.Prime 11069 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_11717 : Nat.Prime 11717 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_12409 : Nat.Prime 12409 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_12413 : Nat.Prime 12413 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_12721 : Nat.Prime 12721 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_12823 : Nat.Prime 12823 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_13109 : Nat.Prime 13109 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_13147 : Nat.Prime 13147 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_14737 : Nat.Prime 14737 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_15173 : Nat.Prime 15173 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_15493 : Nat.Prime 15493 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_15787 : Nat.Prime 15787 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_16139 : Nat.Prime 16139 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_16339 : Nat.Prime 16339 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_16661 : Nat.Prime 16661 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_17203 : Nat.Prime 17203 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_17207 : Nat.Prime 17207 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_17257 : Nat.Prime 17257 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_17509 : Nat.Prime 17509 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_17627 : Nat.Prime 17627 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_17881 : Nat.Prime 17881 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_18061 : Nat.Prime 18061 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_20479 : Nat.Prime 20479 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_20753 : Nat.Prime 20753 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_21247 : Nat.Prime 21247 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_21617 : Nat.Prime 21617 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_22699 : Nat.Prime 22699 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_23459 : Nat.Prime 23459 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_24841 : Nat.Prime 24841 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_25117 : Nat.Prime 25117 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_25243 : Nat.Prime 25243 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_25339 : Nat.Prime 25339 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_25919 : Nat.Prime 25919 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_26083 : Nat.Prime 26083 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_27487 : Nat.Prime 27487 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_27647 : Nat.Prime 27647 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_27799 : Nat.Prime 27799 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_29251 : Nat.Prime 29251 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_29327 : Nat.Prime 29327 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_30517 : Nat.Prime 30517 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_31151 : Nat.Prime 31151 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_31177 : Nat.Prime 31177 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_31333 : Nat.Prime 31333 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_33023 : Nat.Prime 33023 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_33617 : Nat.Prime 33617 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_35531 : Nat.Prime 35531 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_36469 : Nat.Prime 36469 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_36541 : Nat.Prime 36541 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_36929 : Nat.Prime 36929 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_41681 : Nat.Prime 41681 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_42089 : Nat.Prime 42089 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_42943 : Nat.Prime 42943 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_44797 : Nat.Prime 44797 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_44893 : Nat.Prime 44893 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_46381 : Nat.Prime 46381 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_47581 : Nat.Prime 47581 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_47981 : Nat.Prime 47981 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_48017 : Nat.Prime 48017 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_48491 : Nat.Prime 48491 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_49333 : Nat.Prime 49333 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_55343 : Nat.Prime 55343 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_56843 : Nat.Prime 56843 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_60679 : Nat.Prime 60679 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_63347 : Nat.Prime 63347 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_65033 : Nat.Prime 65033 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_69877 : Nat.Prime 69877 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_69997 : Nat.Prime 69997 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_70379 : Nat.Prime 70379 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_72613 : Nat.Prime 72613 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_74231 : Nat.Prime 74231 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_76163 : Nat.Prime 76163 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_80039 : Nat.Prime 80039 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_80279 : Nat.Prime 80279 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_84787 : Nat.Prime 84787 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_86627 : Nat.Prime 86627 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_88873 : Nat.Prime 88873 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_89659 : Nat.Prime 89659 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_91541 : Nat.Prime 91541 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_92369 : Nat.Prime 92369 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_97453 : Nat.Prime 97453 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_100801 : Nat.Prime 100801 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_103573 : Nat.Prime 103573 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_103981 : Nat.Prime 103981 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_105323 : Nat.Prime 105323 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_106861 : Nat.Prime 106861 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_113357 : Nat.Prime 113357 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_121661 : Nat.Prime 121661 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_124297 : Nat.Prime 124297 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_124601 : Nat.Prime 124601 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_125287 : Nat.Prime 125287 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_130073 : Nat.Prime 130073 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_130279 : Nat.Prime 130279 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_131627 : Nat.Prime 131627 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_141667 : Nat.Prime 141667 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_143107 : Nat.Prime 143107 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_145829 : Nat.Prime 145829 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_151009 : Nat.Prime 151009 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_151787 : Nat.Prime 151787 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_153259 : Nat.Prime 153259 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_170603 : Nat.Prime 170603 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_171401 : Nat.Prime 171401 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_178889 : Nat.Prime 178889 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_189859 : Nat.Prime 189859 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_192263 : Nat.Prime 192263 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_198127 : Nat.Prime 198127 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_200789 : Nat.Prime 200789 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_225781 : Nat.Prime 225781 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_229253 : Nat.Prime 229253 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_230551 : Nat.Prime 230551 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_242989 : Nat.Prime 242989 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_245299 : Nat.Prime 245299 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_249397 : Nat.Prime 249397 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_256643 : Nat.Prime 256643 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_261127 : Nat.Prime 261127 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_262519 : Nat.Prime 262519 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_267811 : Nat.Prime 267811 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_271163 : Nat.Prime 271163 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_272809 : Nat.Prime 272809 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_277577 : Nat.Prime 277577 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_296489 : Nat.Prime 296489 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_317189 : Nat.Prime 317189 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_329863 : Nat.Prime 329863 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_360823 : Nat.Prime 360823 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_362027 : Nat.Prime 362027 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_364979 : Nat.Prime 364979 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_367457 : Nat.Prime 367457 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_399181 : Nat.Prime 399181 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_403499 : Nat.Prime 403499 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_447439 : Nat.Prime 447439 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_460711 : Nat.Prime 460711 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_468359 : Nat.Prime 468359 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_512593 : Nat.Prime 512593 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_547999 : Nat.Prime 547999 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_553601 : Nat.Prime 553601 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_570881 : Nat.Prime 570881 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_580871 : Nat.Prime 580871 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_600833 : Nat.Prime 600833 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_653647 : Nat.Prime 653647 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_660661 : Nat.Prime 660661 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_670853 : Nat.Prime 670853 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_694979 : Nat.Prime 694979 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_701957 : Nat.Prime 701957 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_734087 : Nat.Prime 734087 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_773693 : Nat.Prime 773693 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_822011 : Nat.Prime 822011 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_839269 : Nat.Prime 839269 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_880007 : Nat.Prime 880007 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_937331 : Nat.Prime 937331 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_940619 : Nat.Prime 940619 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_1025839 : Nat.Prime 1025839 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_1036307 : Nat.Prime 1036307 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_1126649 : Nat.Prime 1126649 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_1297477 : Nat.Prime 1297477 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_1331251 : Nat.Prime 1331251 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_1442173 : Nat.Prime 1442173 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_1445569 : Nat.Prime 1445569 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_1508063 : Nat.Prime 1508063 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_1526297 : Nat.Prime 1526297 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_1591813 : Nat.Prime 1591813 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_1592737 : Nat.Prime 1592737 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_1901651 : Nat.Prime 1901651 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_2054753 : Nat.Prime 2054753 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_2102497 : Nat.Prime 2102497 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_2126771 : Nat.Prime 2126771 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_2286437 : Nat.Prime 2286437 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_2489909 : Nat.Prime 2489909 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_2506583 : Nat.Prime 2506583 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_2585293 : Nat.Prime 2585293 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_2609083 : Nat.Prime 2609083 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_2755243 : Nat.Prime 2755243 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_2928421 : Nat.Prime 2928421 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_3062881 : Nat.Prime 3062881 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_3171089 : Nat.Prime 3171089 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_3247513 : Nat.Prime 3247513 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_3249863 : Nat.Prime 3249863 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_3384179 : Nat.Prime 3384179 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_3594403 : Nat.Prime 3594403 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_3756671 : Nat.Prime 3756671 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_3861241 : Nat.Prime 3861241 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_3935629 : Nat.Prime 3935629 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_4282273 : Nat.Prime 4282273 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_4438201 : Nat.Prime 4438201 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_4474849 : Nat.Prime 4474849 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_4517543 : Nat.Prime 4517543 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_4560713 : Nat.Prime 4560713 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_4562083 : Nat.Prime 4562083 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_5506091 : Nat.Prime 5506091 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_5770649 : Nat.Prime 5770649 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_6198307 : Nat.Prime 6198307 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_6314617 : Nat.Prime 6314617 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_6336347 : Nat.Prime 6336347 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_7062287 : Nat.Prime 7062287 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_7306177 : Nat.Prime 7306177 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_7592203 : Nat.Prime 7592203 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_8014381 : Nat.Prime 8014381 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_8084771 : Nat.Prime 8084771 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_8141093 : Nat.Prime 8141093 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_8233613 : Nat.Prime 8233613 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_8751781 : Nat.Prime 8751781 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_8914481 : Nat.Prime 8914481 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_9487187 : Nat.Prime 9487187 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_9877709 : Nat.Prime 9877709 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_10820141 : Nat.Prime 10820141 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_11088251 : Nat.Prime 11088251 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_12767401 : Nat.Prime 12767401 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_12983963 : Nat.Prime 12983963 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_13727981 : Nat.Prime 13727981 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_14201963 : Nat.Prime 14201963 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_15826513 : Nat.Prime 15826513 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_15971843 : Nat.Prime 15971843 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_16380781 : Nat.Prime 16380781 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_16727479 : Nat.Prime 16727479 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_17343101 : Nat.Prime 17343101 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_18114361 : Nat.Prime 18114361 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_18262633 : Nat.Prime 18262633 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_19038707 : Nat.Prime 19038707 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_19351279 : Nat.Prime 19351279 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_19597931 : Nat.Prime 19597931 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_20838439 : Nat.Prime 20838439 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_20943863 : Nat.Prime 20943863 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_25256003 : Nat.Prime 25256003 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_25512737 : Nat.Prime 25512737 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_25863419 : Nat.Prime 25863419 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_26544449 : Nat.Prime 26544449 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_26662087 : Nat.Prime 26662087 := by
  norm_num

private theorem prime_oneHundredSixtyEightFJ_31969337 : Nat.Prime 31969337 := by
  apply lucas_primality 31969337 (3 : ZMod 31969337)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (570881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (570881, 1)] : List FactorBlock).map factorBlockValue).prod) = 31969337 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_7
      · exact prime_oneHundredSixtyEightFJ_570881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 31969337) ^ 15984668 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 31969337) ^ 4567048 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 31969337) ^ 56 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_32701811 : Nat.Prime 32701811 := by
  apply lucas_primality 32701811 (2 : ZMod 32701811)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (73, 1), (44797, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (73, 1), (44797, 1)] : List FactorBlock).map factorBlockValue).prod) = 32701811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_5
      · exact prime_oneHundredSixtyEightFJ_73
      · exact prime_oneHundredSixtyEightFJ_44797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 32701811) ^ 16350905 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 32701811) ^ 6540362 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 32701811) ^ 447970 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 32701811) ^ 730 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_34858727 : Nat.Prime 34858727 := by
  apply lucas_primality 34858727 (7 : ZMod 34858727)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (2489909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (2489909, 1)] : List FactorBlock).map factorBlockValue).prod) = 34858727 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_7
      · exact prime_oneHundredSixtyEightFJ_2489909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 34858727) ^ 17429363 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (7 : ZMod 34858727) ^ 4979818 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (7 : ZMod 34858727) ^ 14 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_37721171 : Nat.Prime 37721171 := by
  apply lucas_primality 37721171 (2 : ZMod 37721171)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (29, 1), (130073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (29, 1), (130073, 1)] : List FactorBlock).map factorBlockValue).prod) = 37721171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_5
      · exact prime_oneHundredSixtyEightFJ_29
      · exact prime_oneHundredSixtyEightFJ_130073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 37721171) ^ 18860585 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 37721171) ^ 7544234 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 37721171) ^ 1300730 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 37721171) ^ 290 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_39374633 : Nat.Prime 39374633 := by
  apply lucas_primality 39374633 (3 : ZMod 39374633)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (447439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (447439, 1)] : List FactorBlock).map factorBlockValue).prod) = 39374633 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_11
      · exact prime_oneHundredSixtyEightFJ_447439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 39374633) ^ 19687316 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 39374633) ^ 3579512 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 39374633) ^ 88 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_40674451 : Nat.Prime 40674451 := by
  apply lucas_primality 40674451 (2 : ZMod 40674451)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (271163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (271163, 1)] : List FactorBlock).map factorBlockValue).prod) = 40674451 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_5
      · exact prime_oneHundredSixtyEightFJ_271163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 40674451) ^ 20337225 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 40674451) ^ 13558150 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 40674451) ^ 8134890 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 40674451) ^ 150 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_41822713 : Nat.Prime 41822713 := by
  apply lucas_primality 41822713 (5 : ZMod 41822713)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (580871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (580871, 1)] : List FactorBlock).map factorBlockValue).prod) = 41822713 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_580871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 41822713) ^ 20911356 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 41822713) ^ 13940904 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 41822713) ^ 72 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_45133343 : Nat.Prime 45133343 := by
  apply lucas_primality 45133343 (5 : ZMod 45133343)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (397, 1), (56843, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (397, 1), (56843, 1)] : List FactorBlock).map factorBlockValue).prod) = 45133343 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_397
      · exact prime_oneHundredSixtyEightFJ_56843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 45133343) ^ 22566671 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 45133343) ^ 113686 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 45133343) ^ 794 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_46291519 : Nat.Prime 46291519 := by
  apply lucas_primality 46291519 (3 : ZMod 46291519)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (13, 1), (59, 1), (479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (13, 1), (59, 1), (479, 1)] : List FactorBlock).map factorBlockValue).prod) = 46291519 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_7
      · exact prime_oneHundredSixtyEightFJ_13
      · exact prime_oneHundredSixtyEightFJ_59
      · exact prime_oneHundredSixtyEightFJ_479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 46291519) ^ 23145759 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 46291519) ^ 15430506 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 46291519) ^ 6613074 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 46291519) ^ 3560886 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 46291519) ^ 784602 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 46291519) ^ 96642 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_50390149 : Nat.Prime 50390149 := by
  apply lucas_primality 50390149 (2 : ZMod 50390149)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (23, 1), (41, 1), (61, 1), (73, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (23, 1), (41, 1), (61, 1), (73, 1)] : List FactorBlock).map factorBlockValue).prod) = 50390149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_23
      · exact prime_oneHundredSixtyEightFJ_41
      · exact prime_oneHundredSixtyEightFJ_61
      · exact prime_oneHundredSixtyEightFJ_73
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 50390149) ^ 25195074 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 50390149) ^ 16796716 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 50390149) ^ 2190876 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 50390149) ^ 1229028 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 50390149) ^ 826068 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 50390149) ^ 690276 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_52510687 : Nat.Prime 52510687 := by
  apply lucas_primality 52510687 (5 : ZMod 52510687)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (8751781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (8751781, 1)] : List FactorBlock).map factorBlockValue).prod) = 52510687 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_8751781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 52510687) ^ 26255343 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 52510687) ^ 17503562 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 52510687) ^ 6 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_58121429 : Nat.Prime 58121429 := by
  apply lucas_primality 58121429 (2 : ZMod 58121429)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (67, 1), (137, 1), (1583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (67, 1), (137, 1), (1583, 1)] : List FactorBlock).map factorBlockValue).prod) = 58121429 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_67
      · exact prime_oneHundredSixtyEightFJ_137
      · exact prime_oneHundredSixtyEightFJ_1583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 58121429) ^ 29060714 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 58121429) ^ 867484 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 58121429) ^ 424244 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 58121429) ^ 36716 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_59929613 : Nat.Prime 59929613 := by
  apply lucas_primality 59929613 (2 : ZMod 59929613)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1811, 1), (8273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1811, 1), (8273, 1)] : List FactorBlock).map factorBlockValue).prod) = 59929613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_1811
      · exact prime_oneHundredSixtyEightFJ_8273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 59929613) ^ 29964806 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 59929613) ^ 33092 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 59929613) ^ 7244 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_63849983 : Nat.Prime 63849983 := by
  apply lucas_primality 63849983 (5 : ZMod 63849983)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (4560713, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (4560713, 1)] : List FactorBlock).map factorBlockValue).prod) = 63849983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_7
      · exact prime_oneHundredSixtyEightFJ_4560713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 63849983) ^ 31924991 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 63849983) ^ 9121426 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 63849983) ^ 14 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_66909917 : Nat.Prime 66909917 := by
  apply lucas_primality 66909917 (2 : ZMod 66909917)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (16727479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (16727479, 1)] : List FactorBlock).map factorBlockValue).prod) = 66909917 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_16727479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 66909917) ^ 33454958 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 66909917) ^ 4 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_76730309 : Nat.Prime 76730309 := by
  apply lucas_primality 76730309 (2 : ZMod 76730309)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1733, 1), (11069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1733, 1), (11069, 1)] : List FactorBlock).map factorBlockValue).prod) = 76730309 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_1733
      · exact prime_oneHundredSixtyEightFJ_11069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 76730309) ^ 38365154 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 76730309) ^ 44276 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 76730309) ^ 6932 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_79763389 : Nat.Prime 79763389 := by
  apply lucas_primality 79763389 (2 : ZMod 79763389)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (71, 1), (5507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (71, 1), (5507, 1)] : List FactorBlock).map factorBlockValue).prod) = 79763389 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_17
      · exact prime_oneHundredSixtyEightFJ_71
      · exact prime_oneHundredSixtyEightFJ_5507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 79763389) ^ 39881694 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 79763389) ^ 26587796 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 79763389) ^ 4691964 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 79763389) ^ 1123428 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 79763389) ^ 14484 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_79900273 : Nat.Prime 79900273 := by
  apply lucas_primality 79900273 (5 : ZMod 79900273)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (17, 1), (127, 1), (257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (17, 1), (127, 1), (257, 1)] : List FactorBlock).map factorBlockValue).prod) = 79900273 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_17
      · exact prime_oneHundredSixtyEightFJ_127
      · exact prime_oneHundredSixtyEightFJ_257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 79900273) ^ 39950136 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 79900273) ^ 26633424 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 79900273) ^ 4700016 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 79900273) ^ 629136 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 79900273) ^ 310896 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_87819821 : Nat.Prime 87819821 := by
  apply lucas_primality 87819821 (2 : ZMod 87819821)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (11, 1), (399181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (11, 1), (399181, 1)] : List FactorBlock).map factorBlockValue).prod) = 87819821 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_5
      · exact prime_oneHundredSixtyEightFJ_11
      · exact prime_oneHundredSixtyEightFJ_399181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 87819821) ^ 43909910 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 87819821) ^ 17563964 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 87819821) ^ 7983620 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 87819821) ^ 220 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_92103133 : Nat.Prime 92103133 := by
  apply lucas_primality 92103133 (5 : ZMod 92103133)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (23, 2), (1319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (23, 2), (1319, 1)] : List FactorBlock).map factorBlockValue).prod) = 92103133 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_11
      · exact prime_oneHundredSixtyEightFJ_23
      · exact prime_oneHundredSixtyEightFJ_1319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 92103133) ^ 46051566 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 92103133) ^ 30701044 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 92103133) ^ 8373012 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 92103133) ^ 4004484 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 92103133) ^ 69828 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_98958901 : Nat.Prime 98958901 := by
  apply lucas_primality 98958901 (6 : ZMod 98958901)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (329863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (329863, 1)] : List FactorBlock).map factorBlockValue).prod) = 98958901 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_5
      · exact prime_oneHundredSixtyEightFJ_329863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 98958901) ^ 49479450 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (6 : ZMod 98958901) ^ 32986300 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (6 : ZMod 98958901) ^ 19791780 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (6 : ZMod 98958901) ^ 300 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_102534983 : Nat.Prime 102534983 := by
  apply lucas_primality 102534983 (5 : ZMod 102534983)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (19, 1), (245299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (19, 1), (245299, 1)] : List FactorBlock).map factorBlockValue).prod) = 102534983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_11
      · exact prime_oneHundredSixtyEightFJ_19
      · exact prime_oneHundredSixtyEightFJ_245299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 102534983) ^ 51267491 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 102534983) ^ 9321362 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 102534983) ^ 5396578 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 102534983) ^ 418 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_131511187 : Nat.Prime 131511187 := by
  apply lucas_primality 131511187 (2 : ZMod 131511187)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7306177, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7306177, 1)] : List FactorBlock).map factorBlockValue).prod) = 131511187 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_7306177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 131511187) ^ 65755593 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 131511187) ^ 43837062 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 131511187) ^ 18 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_148903877 : Nat.Prime 148903877 := by
  apply lucas_primality 148903877 (2 : ZMod 148903877)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (3384179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (3384179, 1)] : List FactorBlock).map factorBlockValue).prod) = 148903877 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_11
      · exact prime_oneHundredSixtyEightFJ_3384179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 148903877) ^ 74451938 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 148903877) ^ 13536716 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 148903877) ^ 44 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_158265131 : Nat.Prime 158265131 := by
  apply lucas_primality 158265131 (2 : ZMod 158265131)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (15826513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (15826513, 1)] : List FactorBlock).map factorBlockValue).prod) = 158265131 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_5
      · exact prime_oneHundredSixtyEightFJ_15826513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 158265131) ^ 79132565 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 158265131) ^ 31653026 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 158265131) ^ 10 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_159972523 : Nat.Prime 159972523 := by
  apply lucas_primality 159972523 (3 : ZMod 159972523)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (26662087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (26662087, 1)] : List FactorBlock).map factorBlockValue).prod) = 159972523 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_26662087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 159972523) ^ 79986261 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 159972523) ^ 53324174 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 159972523) ^ 6 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_164472251 : Nat.Prime 164472251 := by
  apply lucas_primality 164472251 (2 : ZMod 164472251)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 3), (53, 1), (12413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 3), (53, 1), (12413, 1)] : List FactorBlock).map factorBlockValue).prod) = 164472251 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_5
      · exact prime_oneHundredSixtyEightFJ_53
      · exact prime_oneHundredSixtyEightFJ_12413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 164472251) ^ 82236125 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 164472251) ^ 32894450 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 164472251) ^ 3103250 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 164472251) ^ 13250 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_213150073 : Nat.Prime 213150073 := by
  apply lucas_primality 213150073 (5 : ZMod 213150073)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (73, 1), (121661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (73, 1), (121661, 1)] : List FactorBlock).map factorBlockValue).prod) = 213150073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_73
      · exact prime_oneHundredSixtyEightFJ_121661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 213150073) ^ 106575036 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 213150073) ^ 71050024 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 213150073) ^ 2919864 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 213150073) ^ 1752 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_224682253 : Nat.Prime 224682253 := by
  apply lucas_primality 224682253 (2 : ZMod 224682253)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1861, 1), (10061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1861, 1), (10061, 1)] : List FactorBlock).map factorBlockValue).prod) = 224682253 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_1861
      · exact prime_oneHundredSixtyEightFJ_10061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 224682253) ^ 112341126 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 224682253) ^ 74894084 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 224682253) ^ 120732 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 224682253) ^ 22332 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_233952713 : Nat.Prime 233952713 := by
  apply lucas_primality 233952713 (3 : ZMod 233952713)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (1777, 1), (2351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (1777, 1), (2351, 1)] : List FactorBlock).map factorBlockValue).prod) = 233952713 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_7
      · exact prime_oneHundredSixtyEightFJ_1777
      · exact prime_oneHundredSixtyEightFJ_2351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 233952713) ^ 116976356 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 233952713) ^ 33421816 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 233952713) ^ 131656 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 233952713) ^ 99512 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_240217849 : Nat.Prime 240217849 := by
  apply lucas_primality 240217849 (19 : ZMod 240217849)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (13, 1), (256643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (13, 1), (256643, 1)] : List FactorBlock).map factorBlockValue).prod) = 240217849 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_13
      · exact prime_oneHundredSixtyEightFJ_256643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 240217849) ^ 120108924 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (19 : ZMod 240217849) ^ 80072616 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (19 : ZMod 240217849) ^ 18478296 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (19 : ZMod 240217849) ^ 936 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_241815373 : Nat.Prime 241815373 := by
  apply lucas_primality 241815373 (2 : ZMod 241815373)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (859, 1), (23459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (859, 1), (23459, 1)] : List FactorBlock).map factorBlockValue).prod) = 241815373 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_859
      · exact prime_oneHundredSixtyEightFJ_23459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 241815373) ^ 120907686 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 241815373) ^ 80605124 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 241815373) ^ 281508 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 241815373) ^ 10308 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_249474187 : Nat.Prime 249474187 := by
  apply lucas_primality 249474187 (3 : ZMod 249474187)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (109, 1), (9781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (109, 1), (9781, 1)] : List FactorBlock).map factorBlockValue).prod) = 249474187 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_13
      · exact prime_oneHundredSixtyEightFJ_109
      · exact prime_oneHundredSixtyEightFJ_9781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 249474187) ^ 124737093 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 249474187) ^ 83158062 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 249474187) ^ 19190322 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 249474187) ^ 2288754 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 249474187) ^ 25506 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_282923783 : Nat.Prime 282923783 := by
  apply lucas_primality 282923783 (5 : ZMod 282923783)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (71, 1), (86627, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (71, 1), (86627, 1)] : List FactorBlock).map factorBlockValue).prod) = 282923783 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_23
      · exact prime_oneHundredSixtyEightFJ_71
      · exact prime_oneHundredSixtyEightFJ_86627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 282923783) ^ 141461891 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 282923783) ^ 12301034 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 282923783) ^ 3984842 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 282923783) ^ 3266 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_286581829 : Nat.Prime 286581829 := by
  apply lucas_primality 286581829 (6 : ZMod 286581829)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (29, 1), (63347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (29, 1), (63347, 1)] : List FactorBlock).map factorBlockValue).prod) = 286581829 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_13
      · exact prime_oneHundredSixtyEightFJ_29
      · exact prime_oneHundredSixtyEightFJ_63347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 286581829) ^ 143290914 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (6 : ZMod 286581829) ^ 95527276 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (6 : ZMod 286581829) ^ 22044756 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (6 : ZMod 286581829) ^ 9882132 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (6 : ZMod 286581829) ^ 4524 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_292202129 : Nat.Prime 292202129 := by
  apply lucas_primality 292202129 (3 : ZMod 292202129)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (18262633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (18262633, 1)] : List FactorBlock).map factorBlockValue).prod) = 292202129 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_18262633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 292202129) ^ 146101064 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 292202129) ^ 16 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_319053557 : Nat.Prime 319053557 := by
  apply lucas_primality 319053557 (2 : ZMod 319053557)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (79763389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (79763389, 1)] : List FactorBlock).map factorBlockValue).prod) = 319053557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_79763389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 319053557) ^ 159526778 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 319053557) ^ 4 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_332647531 : Nat.Prime 332647531 := by
  apply lucas_primality 332647531 (3 : ZMod 332647531)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11088251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11088251, 1)] : List FactorBlock).map factorBlockValue).prod) = 332647531 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_5
      · exact prime_oneHundredSixtyEightFJ_11088251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 332647531) ^ 166323765 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 332647531) ^ 110882510 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 332647531) ^ 66529506 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 332647531) ^ 30 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_337303277 : Nat.Prime 337303277 := by
  apply lucas_primality 337303277 (2 : ZMod 337303277)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (4438201, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (4438201, 1)] : List FactorBlock).map factorBlockValue).prod) = 337303277 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_19
      · exact prime_oneHundredSixtyEightFJ_4438201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 337303277) ^ 168651638 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 337303277) ^ 17752804 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 337303277) ^ 76 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_343207099 : Nat.Prime 343207099 := by
  apply lucas_primality 343207099 (2 : ZMod 343207099)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (13, 1), (67, 1), (7297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (13, 1), (67, 1), (7297, 1)] : List FactorBlock).map factorBlockValue).prod) = 343207099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_13
      · exact prime_oneHundredSixtyEightFJ_67
      · exact prime_oneHundredSixtyEightFJ_7297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 343207099) ^ 171603549 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 343207099) ^ 114402366 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 343207099) ^ 26400546 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 343207099) ^ 5122494 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 343207099) ^ 47034 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_353497423 : Nat.Prime 353497423 := by
  apply lucas_primality 353497423 (5 : ZMod 353497423)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (1151, 1), (3011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (1151, 1), (3011, 1)] : List FactorBlock).map factorBlockValue).prod) = 353497423 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_17
      · exact prime_oneHundredSixtyEightFJ_1151
      · exact prime_oneHundredSixtyEightFJ_3011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 353497423) ^ 176748711 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 353497423) ^ 117832474 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 353497423) ^ 20793966 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 353497423) ^ 307122 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 353497423) ^ 117402 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_455056513 : Nat.Prime 455056513 := by
  apply lucas_primality 455056513 (15 : ZMod 455056513)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (367, 1), (3229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (367, 1), (3229, 1)] : List FactorBlock).map factorBlockValue).prod) = 455056513 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_367
      · exact prime_oneHundredSixtyEightFJ_3229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (15 : ZMod 455056513) ^ 227528256 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (15 : ZMod 455056513) ^ 151685504 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (15 : ZMod 455056513) ^ 1239936 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (15 : ZMod 455056513) ^ 140928 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_544718633 : Nat.Prime 544718633 := by
  apply lucas_primality 544718633 (3 : ZMod 544718633)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (97, 1), (701957, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (97, 1), (701957, 1)] : List FactorBlock).map factorBlockValue).prod) = 544718633 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_97
      · exact prime_oneHundredSixtyEightFJ_701957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 544718633) ^ 272359316 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 544718633) ^ 5615656 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 544718633) ^ 776 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_545326447 : Nat.Prime 545326447 := by
  apply lucas_primality 545326447 (6 : ZMod 545326447)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (12983963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (12983963, 1)] : List FactorBlock).map factorBlockValue).prod) = 545326447 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_7
      · exact prime_oneHundredSixtyEightFJ_12983963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 545326447) ^ 272663223 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (6 : ZMod 545326447) ^ 181775482 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (6 : ZMod 545326447) ^ 77903778 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (6 : ZMod 545326447) ^ 42 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_552745337 : Nat.Prime 552745337 := by
  apply lucas_primality 552745337 (3 : ZMod 552745337)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (13, 1), (29, 1), (16661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (13, 1), (29, 1), (16661, 1)] : List FactorBlock).map factorBlockValue).prod) = 552745337 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_11
      · exact prime_oneHundredSixtyEightFJ_13
      · exact prime_oneHundredSixtyEightFJ_29
      · exact prime_oneHundredSixtyEightFJ_16661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 552745337) ^ 276372668 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 552745337) ^ 50249576 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 552745337) ^ 42518872 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 552745337) ^ 19060184 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 552745337) ^ 33176 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_559319647 : Nat.Prime 559319647 := by
  apply lucas_primality 559319647 (3 : ZMod 559319647)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (47, 1), (59, 1), (33617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (47, 1), (59, 1), (33617, 1)] : List FactorBlock).map factorBlockValue).prod) = 559319647 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_47
      · exact prime_oneHundredSixtyEightFJ_59
      · exact prime_oneHundredSixtyEightFJ_33617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 559319647) ^ 279659823 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 559319647) ^ 186439882 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 559319647) ^ 11900418 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 559319647) ^ 9479994 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 559319647) ^ 16638 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_619623397 : Nat.Prime 619623397 := by
  apply lucas_primality 619623397 (2 : ZMod 619623397)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (29, 1), (84787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (29, 1), (84787, 1)] : List FactorBlock).map factorBlockValue).prod) = 619623397 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_7
      · exact prime_oneHundredSixtyEightFJ_29
      · exact prime_oneHundredSixtyEightFJ_84787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 619623397) ^ 309811698 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 619623397) ^ 206541132 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 619623397) ^ 88517628 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 619623397) ^ 21366324 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 619623397) ^ 7308 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_640433267 : Nat.Prime 640433267 := by
  apply lucas_primality 640433267 (2 : ZMod 640433267)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (19, 1), (61, 1), (25117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (19, 1), (61, 1), (25117, 1)] : List FactorBlock).map factorBlockValue).prod) = 640433267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_11
      · exact prime_oneHundredSixtyEightFJ_19
      · exact prime_oneHundredSixtyEightFJ_61
      · exact prime_oneHundredSixtyEightFJ_25117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 640433267) ^ 320216633 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 58221206 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 33707014 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 10498906 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 25498 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_657020543 : Nat.Prime 657020543 := by
  apply lucas_primality 657020543 (5 : ZMod 657020543)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (53, 1), (6198307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (53, 1), (6198307, 1)] : List FactorBlock).map factorBlockValue).prod) = 657020543 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_53
      · exact prime_oneHundredSixtyEightFJ_6198307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 657020543) ^ 328510271 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 657020543) ^ 12396614 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 657020543) ^ 106 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_695290307 : Nat.Prime 695290307 := by
  apply lucas_primality 695290307 (2 : ZMod 695290307)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 1), (8084771, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 1), (8084771, 1)] : List FactorBlock).map factorBlockValue).prod) = 695290307 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_43
      · exact prime_oneHundredSixtyEightFJ_8084771
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 695290307) ^ 347645153 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 695290307) ^ 16169542 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 695290307) ^ 86 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_714027719 : Nat.Prime 714027719 := by
  apply lucas_primality 714027719 (11 : ZMod 714027719)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) = 714027719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_17203
      · exact prime_oneHundredSixtyEightFJ_20753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 714027719) ^ 357013859 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 41506 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 34406 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_894423209 : Nat.Prime 894423209 := by
  apply lucas_primality 894423209 (3 : ZMod 894423209)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (15971843, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (15971843, 1)] : List FactorBlock).map factorBlockValue).prod) = 894423209 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_7
      · exact prime_oneHundredSixtyEightFJ_15971843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 894423209) ^ 447211604 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 894423209) ^ 127774744 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 894423209) ^ 56 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_1057169473 : Nat.Prime 1057169473 := by
  apply lucas_primality 1057169473 (7 : ZMod 1057169473)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (5506091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (5506091, 1)] : List FactorBlock).map factorBlockValue).prod) = 1057169473 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_5506091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 1057169473) ^ 528584736 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (7 : ZMod 1057169473) ^ 352389824 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (7 : ZMod 1057169473) ^ 192 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_1101126877 : Nat.Prime 1101126877 := by
  apply lucas_primality 1101126877 (2 : ZMod 1101126877)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (457, 1), (200789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (457, 1), (200789, 1)] : List FactorBlock).map factorBlockValue).prod) = 1101126877 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_457
      · exact prime_oneHundredSixtyEightFJ_200789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1101126877) ^ 550563438 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1101126877) ^ 367042292 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1101126877) ^ 2409468 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1101126877) ^ 5484 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_1299989947 : Nat.Prime 1299989947 := by
  apply lucas_primality 1299989947 (2 : ZMod 1299989947)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (1667, 1), (5651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (1667, 1), (5651, 1)] : List FactorBlock).map factorBlockValue).prod) = 1299989947 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_23
      · exact prime_oneHundredSixtyEightFJ_1667
      · exact prime_oneHundredSixtyEightFJ_5651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1299989947) ^ 649994973 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1299989947) ^ 433329982 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1299989947) ^ 56521302 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1299989947) ^ 779838 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1299989947) ^ 230046 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_1432155623 : Nat.Prime 1432155623 := by
  apply lucas_primality 1432155623 (5 : ZMod 1432155623)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (181, 1), (311, 1), (12721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (181, 1), (311, 1), (12721, 1)] : List FactorBlock).map factorBlockValue).prod) = 1432155623 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_181
      · exact prime_oneHundredSixtyEightFJ_311
      · exact prime_oneHundredSixtyEightFJ_12721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1432155623) ^ 716077811 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 1432155623) ^ 7912462 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 1432155623) ^ 4605002 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 1432155623) ^ 112582 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_1528638619 : Nat.Prime 1528638619 := by
  apply lucas_primality 1528638619 (3 : ZMod 1528638619)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (19597931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (19597931, 1)] : List FactorBlock).map factorBlockValue).prod) = 1528638619 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_13
      · exact prime_oneHundredSixtyEightFJ_19597931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1528638619) ^ 764319309 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1528638619) ^ 509546206 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1528638619) ^ 117587586 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1528638619) ^ 78 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_1678038433 : Nat.Prime 1678038433 := by
  apply lucas_primality 1678038433 (5 : ZMod 1678038433)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (7, 1), (31, 1), (109, 1), (739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (7, 1), (31, 1), (109, 1), (739, 1)] : List FactorBlock).map factorBlockValue).prod) = 1678038433 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_7
      · exact prime_oneHundredSixtyEightFJ_31
      · exact prime_oneHundredSixtyEightFJ_109
      · exact prime_oneHundredSixtyEightFJ_739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1678038433) ^ 839019216 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 1678038433) ^ 559346144 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 1678038433) ^ 239719776 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 1678038433) ^ 54130272 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 1678038433) ^ 15394848 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 1678038433) ^ 2270688 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_1769124349 : Nat.Prime 1769124349 := by
  apply lucas_primality 1769124349 (2 : ZMod 1769124349)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (16380781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (16380781, 1)] : List FactorBlock).map factorBlockValue).prod) = 1769124349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_16380781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1769124349) ^ 884562174 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1769124349) ^ 589708116 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1769124349) ^ 108 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_1815083779 : Nat.Prime 1815083779 := by
  apply lucas_primality 1815083779 (3 : ZMod 1815083779)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (23, 1), (773693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (23, 1), (773693, 1)] : List FactorBlock).map factorBlockValue).prod) = 1815083779 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_17
      · exact prime_oneHundredSixtyEightFJ_23
      · exact prime_oneHundredSixtyEightFJ_773693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1815083779) ^ 907541889 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1815083779) ^ 605027926 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1815083779) ^ 106769634 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1815083779) ^ 78916686 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1815083779) ^ 2346 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_1946792983 : Nat.Prime 1946792983 := by
  apply lucas_primality 1946792983 (3 : ZMod 1946792983)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1301, 1), (249397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1301, 1), (249397, 1)] : List FactorBlock).map factorBlockValue).prod) = 1946792983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_1301
      · exact prime_oneHundredSixtyEightFJ_249397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1946792983) ^ 973396491 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1946792983) ^ 648930994 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1946792983) ^ 1496382 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1946792983) ^ 7806 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_2016230959 : Nat.Prime 2016230959 := by
  apply lucas_primality 2016230959 (3 : ZMod 2016230959)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (229, 1), (69877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (229, 1), (69877, 1)] : List FactorBlock).map factorBlockValue).prod) = 2016230959 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_7
      · exact prime_oneHundredSixtyEightFJ_229
      · exact prime_oneHundredSixtyEightFJ_69877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2016230959) ^ 1008115479 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2016230959) ^ 672076986 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2016230959) ^ 288032994 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2016230959) ^ 8804502 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2016230959) ^ 28854 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_2158825607 : Nat.Prime 2158825607 := by
  apply lucas_primality 2158825607 (5 : ZMod 2158825607)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (37, 1), (269, 1), (15493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (37, 1), (269, 1), (15493, 1)] : List FactorBlock).map factorBlockValue).prod) = 2158825607 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_7
      · exact prime_oneHundredSixtyEightFJ_37
      · exact prime_oneHundredSixtyEightFJ_269
      · exact prime_oneHundredSixtyEightFJ_15493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2158825607) ^ 1079412803 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 2158825607) ^ 308403658 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 2158825607) ^ 58346638 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 2158825607) ^ 8025374 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 2158825607) ^ 139342 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_2165692049 : Nat.Prime 2165692049 := by
  apply lucas_primality 2165692049 (3 : ZMod 2165692049)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (13, 1), (19, 1), (547999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (13, 1), (19, 1), (547999, 1)] : List FactorBlock).map factorBlockValue).prod) = 2165692049 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_13
      · exact prime_oneHundredSixtyEightFJ_19
      · exact prime_oneHundredSixtyEightFJ_547999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2165692049) ^ 1082846024 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2165692049) ^ 166591696 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2165692049) ^ 113983792 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2165692049) ^ 3952 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_2416168199 : Nat.Prime 2416168199 := by
  apply lucas_primality 2416168199 (7 : ZMod 2416168199)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (71, 1), (362027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (71, 1), (362027, 1)] : List FactorBlock).map factorBlockValue).prod) = 2416168199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_47
      · exact prime_oneHundredSixtyEightFJ_71
      · exact prime_oneHundredSixtyEightFJ_362027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 2416168199) ^ 1208084099 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (7 : ZMod 2416168199) ^ 51407834 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (7 : ZMod 2416168199) ^ 34030538 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (7 : ZMod 2416168199) ^ 6674 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_2505296251 : Nat.Prime 2505296251 := by
  apply lucas_primality 2505296251 (3 : ZMod 2505296251)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 4), (74231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 4), (74231, 1)] : List FactorBlock).map factorBlockValue).prod) = 2505296251 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_5
      · exact prime_oneHundredSixtyEightFJ_74231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2505296251) ^ 1252648125 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2505296251) ^ 835098750 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2505296251) ^ 501059250 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2505296251) ^ 33750 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_3337153199 : Nat.Prime 3337153199 := by
  apply lucas_primality 3337153199 (14 : ZMod 3337153199)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (87819821, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (87819821, 1)] : List FactorBlock).map factorBlockValue).prod) = 3337153199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_19
      · exact prime_oneHundredSixtyEightFJ_87819821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (14 : ZMod 3337153199) ^ 1668576599 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (14 : ZMod 3337153199) ^ 175639642 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (14 : ZMod 3337153199) ^ 38 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_4000122587 : Nat.Prime 4000122587 := by
  apply lucas_primality 4000122587 (2 : ZMod 4000122587)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (653, 1), (3062881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (653, 1), (3062881, 1)] : List FactorBlock).map factorBlockValue).prod) = 4000122587 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_653
      · exact prime_oneHundredSixtyEightFJ_3062881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4000122587) ^ 2000061293 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4000122587) ^ 6125762 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4000122587) ^ 1306 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_4276278527 : Nat.Prime 4276278527 := by
  apply lucas_primality 4276278527 (5 : ZMod 4276278527)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (164472251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (164472251, 1)] : List FactorBlock).map factorBlockValue).prod) = 4276278527 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_13
      · exact prime_oneHundredSixtyEightFJ_164472251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 4276278527) ^ 2138139263 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 4276278527) ^ 328944502 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 4276278527) ^ 26 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_4449030959 : Nat.Prime 4449030959 := by
  apply lucas_primality 4449030959 (7 : ZMod 4449030959)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (293, 1), (7592203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (293, 1), (7592203, 1)] : List FactorBlock).map factorBlockValue).prod) = 4449030959 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_293
      · exact prime_oneHundredSixtyEightFJ_7592203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 4449030959) ^ 2224515479 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (7 : ZMod 4449030959) ^ 15184406 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (7 : ZMod 4449030959) ^ 586 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_4506446297 : Nat.Prime 4506446297 := by
  apply lucas_primality 4506446297 (3 : ZMod 4506446297)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (19, 1), (79, 1), (109, 1), (313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (19, 1), (79, 1), (109, 1), (313, 1)] : List FactorBlock).map factorBlockValue).prod) = 4506446297 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_11
      · exact prime_oneHundredSixtyEightFJ_19
      · exact prime_oneHundredSixtyEightFJ_79
      · exact prime_oneHundredSixtyEightFJ_109
      · exact prime_oneHundredSixtyEightFJ_313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4506446297) ^ 2253223148 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 4506446297) ^ 409676936 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 4506446297) ^ 237181384 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 4506446297) ^ 57043624 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 4506446297) ^ 41343544 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 4506446297) ^ 14397592 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_4725961831 : Nat.Prime 4725961831 := by
  apply lucas_primality 4725961831 (3 : ZMod 4725961831)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (52510687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (52510687, 1)] : List FactorBlock).map factorBlockValue).prod) = 4725961831 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_5
      · exact prime_oneHundredSixtyEightFJ_52510687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4725961831) ^ 2362980915 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 4725961831) ^ 1575320610 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 4725961831) ^ 945192366 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 4725961831) ^ 90 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_4916643301 : Nat.Prime 4916643301 := by
  apply lucas_primality 4916643301 (2 : ZMod 4916643301)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 5), (5, 2), (19, 1), (23, 1), (463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 5), (5, 2), (19, 1), (23, 1), (463, 1)] : List FactorBlock).map factorBlockValue).prod) = 4916643301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_5
      · exact prime_oneHundredSixtyEightFJ_19
      · exact prime_oneHundredSixtyEightFJ_23
      · exact prime_oneHundredSixtyEightFJ_463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4916643301) ^ 2458321650 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4916643301) ^ 1638881100 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4916643301) ^ 983328660 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4916643301) ^ 258770700 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4916643301) ^ 213767100 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4916643301) ^ 10619100 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_4980897683 : Nat.Prime 4980897683 := by
  apply lucas_primality 4980897683 (2 : ZMod 4980897683)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1171, 1), (2126771, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1171, 1), (2126771, 1)] : List FactorBlock).map factorBlockValue).prod) = 4980897683 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_1171
      · exact prime_oneHundredSixtyEightFJ_2126771
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4980897683) ^ 2490448841 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4980897683) ^ 4253542 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4980897683) ^ 2342 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_5260447481 : Nat.Prime 5260447481 := by
  apply lucas_primality 5260447481 (3 : ZMod 5260447481)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (131511187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (131511187, 1)] : List FactorBlock).map factorBlockValue).prod) = 5260447481 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_5
      · exact prime_oneHundredSixtyEightFJ_131511187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 5260447481) ^ 2630223740 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 5260447481) ^ 1052089496 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 5260447481) ^ 40 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_5276183617 : Nat.Prime 5276183617 := by
  apply lucas_primality 5276183617 (7 : ZMod 5276183617)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (11, 1), (277577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (11, 1), (277577, 1)] : List FactorBlock).map factorBlockValue).prod) = 5276183617 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_11
      · exact prime_oneHundredSixtyEightFJ_277577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 5276183617) ^ 2638091808 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (7 : ZMod 5276183617) ^ 1758727872 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (7 : ZMod 5276183617) ^ 479653056 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (7 : ZMod 5276183617) ^ 19008 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_5319938207 : Nat.Prime 5319938207 := by
  apply lucas_primality 5319938207 (5 : ZMod 5319938207)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (241815373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (241815373, 1)] : List FactorBlock).map factorBlockValue).prod) = 5319938207 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_11
      · exact prime_oneHundredSixtyEightFJ_241815373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 5319938207) ^ 2659969103 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 5319938207) ^ 483630746 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 5319938207) ^ 22 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_5371602329 : Nat.Prime 5371602329 := by
  apply lucas_primality 5371602329 (3 : ZMod 5371602329)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (19, 1), (4483, 1), (7883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (19, 1), (4483, 1), (7883, 1)] : List FactorBlock).map factorBlockValue).prod) = 5371602329 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_19
      · exact prime_oneHundredSixtyEightFJ_4483
      · exact prime_oneHundredSixtyEightFJ_7883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 5371602329) ^ 2685801164 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 5371602329) ^ 282715912 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 5371602329) ^ 1198216 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 5371602329) ^ 681416 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_5886061981 : Nat.Prime 5886061981 := by
  apply lucas_primality 5886061981 (18 : ZMod 5886061981)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (17, 1), (5770649, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (17, 1), (5770649, 1)] : List FactorBlock).map factorBlockValue).prod) = 5886061981 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_5
      · exact prime_oneHundredSixtyEightFJ_17
      · exact prime_oneHundredSixtyEightFJ_5770649
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (18 : ZMod 5886061981) ^ 2943030990 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (18 : ZMod 5886061981) ^ 1962020660 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (18 : ZMod 5886061981) ^ 1177212396 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (18 : ZMod 5886061981) ^ 346238940 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (18 : ZMod 5886061981) ^ 1020 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_6037638679 : Nat.Prime 6037638679 := by
  apply lucas_primality 6037638679 (3 : ZMod 6037638679)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) = 6037638679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_31
      · exact prime_oneHundredSixtyEightFJ_10820141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6037638679) ^ 3018819339 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 2012546226 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 194762538 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 558 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_6114554477 : Nat.Prime 6114554477 := by
  apply lucas_primality 6114554477 (2 : ZMod 6114554477)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1528638619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1528638619, 1)] : List FactorBlock).map factorBlockValue).prod) = 6114554477 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_1528638619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 6114554477) ^ 3057277238 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 6114554477) ^ 4 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_6393737663 : Nat.Prime 6393737663 := by
  apply lucas_primality 6393737663 (5 : ZMod 6393737663)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (23, 1), (31, 1), (311, 1), (1109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (23, 1), (31, 1), (311, 1), (1109, 1)] : List FactorBlock).map factorBlockValue).prod) = 6393737663 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_13
      · exact prime_oneHundredSixtyEightFJ_23
      · exact prime_oneHundredSixtyEightFJ_31
      · exact prime_oneHundredSixtyEightFJ_311
      · exact prime_oneHundredSixtyEightFJ_1109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 6393737663) ^ 3196868831 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 6393737663) ^ 491825974 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 6393737663) ^ 277988594 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 6393737663) ^ 206249602 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 6393737663) ^ 20558642 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 6393737663) ^ 5765318 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_7076497397 : Nat.Prime 7076497397 := by
  apply lucas_primality 7076497397 (2 : ZMod 7076497397)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1769124349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1769124349, 1)] : List FactorBlock).map factorBlockValue).prod) = 7076497397 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_1769124349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 7076497397) ^ 3538248698 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 7076497397) ^ 4 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_7982699411 : Nat.Prime 7982699411 := by
  apply lucas_primality 7982699411 (2 : ZMod 7982699411)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (53, 1), (59, 1), (36469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (53, 1), (59, 1), (36469, 1)] : List FactorBlock).map factorBlockValue).prod) = 7982699411 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_5
      · exact prime_oneHundredSixtyEightFJ_7
      · exact prime_oneHundredSixtyEightFJ_53
      · exact prime_oneHundredSixtyEightFJ_59
      · exact prime_oneHundredSixtyEightFJ_36469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7982699411) ^ 3991349705 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 7982699411) ^ 1596539882 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 7982699411) ^ 1140385630 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 7982699411) ^ 150616970 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 7982699411) ^ 135299990 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 7982699411) ^ 218890 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_8126659771 : Nat.Prime 8126659771 := by
  apply lucas_primality 8126659771 (3 : ZMod 8126659771)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (17, 2), (937331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (17, 2), (937331, 1)] : List FactorBlock).map factorBlockValue).prod) = 8126659771 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_5
      · exact prime_oneHundredSixtyEightFJ_17
      · exact prime_oneHundredSixtyEightFJ_937331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 8126659771) ^ 4063329885 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 8126659771) ^ 2708886590 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 8126659771) ^ 1625331954 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 8126659771) ^ 478038810 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 8126659771) ^ 8670 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_9299447551 : Nat.Prime 9299447551 := by
  apply lucas_primality 9299447551 (3 : ZMod 9299447551)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (157, 1), (131627, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (157, 1), (131627, 1)] : List FactorBlock).map factorBlockValue).prod) = 9299447551 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_5
      · exact prime_oneHundredSixtyEightFJ_157
      · exact prime_oneHundredSixtyEightFJ_131627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 9299447551) ^ 4649723775 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 9299447551) ^ 3099815850 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 9299447551) ^ 1859889510 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 9299447551) ^ 59232150 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 9299447551) ^ 70650 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_10021666103 : Nat.Prime 10021666103 := by
  apply lucas_primality 10021666103 (5 : ZMod 10021666103)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (67, 1), (1526297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (67, 1), (1526297, 1)] : List FactorBlock).map factorBlockValue).prod) = 10021666103 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_7
      · exact prime_oneHundredSixtyEightFJ_67
      · exact prime_oneHundredSixtyEightFJ_1526297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 10021666103) ^ 5010833051 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 10021666103) ^ 1431666586 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 10021666103) ^ 149577106 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 10021666103) ^ 6566 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_10089149659 : Nat.Prime 10089149659 := by
  apply lucas_primality 10089149659 (3 : ZMod 10089149659)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (240217849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (240217849, 1)] : List FactorBlock).map factorBlockValue).prod) = 10089149659 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_7
      · exact prime_oneHundredSixtyEightFJ_240217849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 10089149659) ^ 5044574829 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 10089149659) ^ 3363049886 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 10089149659) ^ 1441307094 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 10089149659) ^ 42 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_11905824439 : Nat.Prime 11905824439 := by
  apply lucas_primality 11905824439 (3 : ZMod 11905824439)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (17, 1), (149, 1), (261127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (17, 1), (149, 1), (261127, 1)] : List FactorBlock).map factorBlockValue).prod) = 11905824439 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_17
      · exact prime_oneHundredSixtyEightFJ_149
      · exact prime_oneHundredSixtyEightFJ_261127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 11905824439) ^ 5952912219 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 11905824439) ^ 3968608146 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 11905824439) ^ 700342614 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 11905824439) ^ 79904862 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 11905824439) ^ 45594 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_14026408709 : Nat.Prime 14026408709 := by
  apply lucas_primality 14026408709 (2 : ZMod 14026408709)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (83, 1), (3249863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (83, 1), (3249863, 1)] : List FactorBlock).map factorBlockValue).prod) = 14026408709 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_13
      · exact prime_oneHundredSixtyEightFJ_83
      · exact prime_oneHundredSixtyEightFJ_3249863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 14026408709) ^ 7013204354 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 14026408709) ^ 1078954516 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 14026408709) ^ 168992876 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 14026408709) ^ 4316 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_14046543779 : Nat.Prime 14046543779 := by
  apply lucas_primality 14046543779 (2 : ZMod 14046543779)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (853, 1), (8233613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (853, 1), (8233613, 1)] : List FactorBlock).map factorBlockValue).prod) = 14046543779 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_853
      · exact prime_oneHundredSixtyEightFJ_8233613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 14046543779) ^ 7023271889 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 14046543779) ^ 16467226 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 14046543779) ^ 1706 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_14757462491 : Nat.Prime 14757462491 := by
  apply lucas_primality 14757462491 (2 : ZMod 14757462491)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (101, 1), (809, 1), (18061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (101, 1), (809, 1), (18061, 1)] : List FactorBlock).map factorBlockValue).prod) = 14757462491 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_5
      · exact prime_oneHundredSixtyEightFJ_101
      · exact prime_oneHundredSixtyEightFJ_809
      · exact prime_oneHundredSixtyEightFJ_18061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 14757462491) ^ 7378731245 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 14757462491) ^ 2951492498 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 14757462491) ^ 146113490 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 14757462491) ^ 18241610 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 14757462491) ^ 817090 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_15031777507 : Nat.Prime 15031777507 := by
  apply lucas_primality 15031777507 (2 : ZMod 15031777507)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2505296251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2505296251, 1)] : List FactorBlock).map factorBlockValue).prod) = 15031777507 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_2505296251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 15031777507) ^ 7515888753 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 15031777507) ^ 5010592502 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 15031777507) ^ 6 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_19744281793 : Nat.Prime 19744281793 := by
  apply lucas_primality 19744281793 (5 : ZMod 19744281793)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (43, 1), (467, 1), (569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (43, 1), (467, 1), (569, 1)] : List FactorBlock).map factorBlockValue).prod) = 19744281793 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_43
      · exact prime_oneHundredSixtyEightFJ_467
      · exact prime_oneHundredSixtyEightFJ_569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 19744281793) ^ 9872140896 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 19744281793) ^ 6581427264 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 19744281793) ^ 459169344 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 19744281793) ^ 42278976 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 19744281793) ^ 34699968 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_23765597773 : Nat.Prime 23765597773 := by
  apply lucas_primality 23765597773 (2 : ZMod 23765597773)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (282923783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (282923783, 1)] : List FactorBlock).map factorBlockValue).prod) = 23765597773 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_7
      · exact prime_oneHundredSixtyEightFJ_282923783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 23765597773) ^ 11882798886 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 23765597773) ^ 7921865924 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 23765597773) ^ 3395085396 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 23765597773) ^ 84 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_24024496931 : Nat.Prime 24024496931 := by
  apply lucas_primality 24024496931 (6 : ZMod 24024496931)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (343207099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (343207099, 1)] : List FactorBlock).map factorBlockValue).prod) = 24024496931 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_5
      · exact prime_oneHundredSixtyEightFJ_7
      · exact prime_oneHundredSixtyEightFJ_343207099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 24024496931) ^ 12012248465 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (6 : ZMod 24024496931) ^ 4804899386 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (6 : ZMod 24024496931) ^ 3432070990 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (6 : ZMod 24024496931) ^ 70 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_24570248051 : Nat.Prime 24570248051 := by
  apply lucas_primality 24570248051 (10 : ZMod 24570248051)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (19, 1), (25863419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (19, 1), (25863419, 1)] : List FactorBlock).map factorBlockValue).prod) = 24570248051 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_5
      · exact prime_oneHundredSixtyEightFJ_19
      · exact prime_oneHundredSixtyEightFJ_25863419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 24570248051) ^ 12285124025 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (10 : ZMod 24570248051) ^ 4914049610 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (10 : ZMod 24570248051) ^ 1293170950 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (10 : ZMod 24570248051) ^ 950 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_25734798431 : Nat.Prime 25734798431 := by
  apply lucas_primality 25734798431 (17 : ZMod 25734798431)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (233952713, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (233952713, 1)] : List FactorBlock).map factorBlockValue).prod) = 25734798431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_5
      · exact prime_oneHundredSixtyEightFJ_11
      · exact prime_oneHundredSixtyEightFJ_233952713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 25734798431) ^ 12867399215 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (17 : ZMod 25734798431) ^ 5146959686 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (17 : ZMod 25734798431) ^ 2339527130 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (17 : ZMod 25734798431) ^ 110 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_26846491729 : Nat.Prime 26846491729 := by
  apply lucas_primality 26846491729 (11 : ZMod 26846491729)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (7, 1), (79900273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (7, 1), (79900273, 1)] : List FactorBlock).map factorBlockValue).prod) = 26846491729 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_7
      · exact prime_oneHundredSixtyEightFJ_79900273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 26846491729) ^ 13423245864 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (11 : ZMod 26846491729) ^ 8948830576 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (11 : ZMod 26846491729) ^ 3835213104 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (11 : ZMod 26846491729) ^ 336 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_27210680461 : Nat.Prime 27210680461 := by
  apply lucas_primality 27210680461 (2 : ZMod 27210680461)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 1), (50390149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 1), (50390149, 1)] : List FactorBlock).map factorBlockValue).prod) = 27210680461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_5
      · exact prime_oneHundredSixtyEightFJ_50390149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 27210680461) ^ 13605340230 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 27210680461) ^ 9070226820 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 27210680461) ^ 5442136092 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 27210680461) ^ 540 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_27637266851 : Nat.Prime 27637266851 := by
  apply lucas_primality 27637266851 (6 : ZMod 27637266851)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (552745337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (552745337, 1)] : List FactorBlock).map factorBlockValue).prod) = 27637266851 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_5
      · exact prime_oneHundredSixtyEightFJ_552745337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 27637266851) ^ 13818633425 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (6 : ZMod 27637266851) ^ 5527453370 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (6 : ZMod 27637266851) ^ 50 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_28089823441 : Nat.Prime 28089823441 := by
  apply lucas_primality 28089823441 (17 : ZMod 28089823441)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (7, 1), (19, 1), (880007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (7, 1), (19, 1), (880007, 1)] : List FactorBlock).map factorBlockValue).prod) = 28089823441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_5
      · exact prime_oneHundredSixtyEightFJ_7
      · exact prime_oneHundredSixtyEightFJ_19
      · exact prime_oneHundredSixtyEightFJ_880007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 28089823441) ^ 14044911720 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (17 : ZMod 28089823441) ^ 9363274480 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (17 : ZMod 28089823441) ^ 5617964688 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (17 : ZMod 28089823441) ^ 4012831920 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (17 : ZMod 28089823441) ^ 1478411760 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (17 : ZMod 28089823441) ^ 31920 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_31343373377 : Nat.Prime 31343373377 := by
  apply lucas_primality 31343373377 (3 : ZMod 31343373377)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (7, 1), (1153, 1), (60679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (7, 1), (1153, 1), (60679, 1)] : List FactorBlock).map factorBlockValue).prod) = 31343373377 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_7
      · exact prime_oneHundredSixtyEightFJ_1153
      · exact prime_oneHundredSixtyEightFJ_60679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 31343373377) ^ 15671686688 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 31343373377) ^ 4477624768 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 31343373377) ^ 27184192 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 31343373377) ^ 516544 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_32680945391 : Nat.Prime 32680945391 := by
  apply lucas_primality 32680945391 (17 : ZMod 32680945391)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (83, 1), (39374633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (83, 1), (39374633, 1)] : List FactorBlock).map factorBlockValue).prod) = 32680945391 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_5
      · exact prime_oneHundredSixtyEightFJ_83
      · exact prime_oneHundredSixtyEightFJ_39374633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 32680945391) ^ 16340472695 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (17 : ZMod 32680945391) ^ 6536189078 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (17 : ZMod 32680945391) ^ 393746330 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (17 : ZMod 32680945391) ^ 830 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_33237310643 : Nat.Prime 33237310643 := by
  apply lucas_primality 33237310643 (2 : ZMod 33237310643)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (359, 1), (46291519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (359, 1), (46291519, 1)] : List FactorBlock).map factorBlockValue).prod) = 33237310643 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_359
      · exact prime_oneHundredSixtyEightFJ_46291519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 33237310643) ^ 16618655321 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 33237310643) ^ 92583038 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 33237310643) ^ 718 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_35264271901 : Nat.Prime 35264271901 := by
  apply lucas_primality 35264271901 (7 : ZMod 35264271901)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (11, 1), (13, 1), (822011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (11, 1), (13, 1), (822011, 1)] : List FactorBlock).map factorBlockValue).prod) = 35264271901 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_5
      · exact prime_oneHundredSixtyEightFJ_11
      · exact prime_oneHundredSixtyEightFJ_13
      · exact prime_oneHundredSixtyEightFJ_822011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 35264271901) ^ 17632135950 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (7 : ZMod 35264271901) ^ 11754757300 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (7 : ZMod 35264271901) ^ 7052854380 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (7 : ZMod 35264271901) ^ 3205842900 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (7 : ZMod 35264271901) ^ 2712636300 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (7 : ZMod 35264271901) ^ 42900 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_39616332661 : Nat.Prime 39616332661 := by
  apply lucas_primality 39616332661 (2 : ZMod 39616332661)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 1), (19, 1), (3861241, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 1), (19, 1), (3861241, 1)] : List FactorBlock).map factorBlockValue).prod) = 39616332661 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_5
      · exact prime_oneHundredSixtyEightFJ_19
      · exact prime_oneHundredSixtyEightFJ_3861241
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 39616332661) ^ 19808166330 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 39616332661) ^ 13205444220 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 39616332661) ^ 7923266532 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 39616332661) ^ 2085070140 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 39616332661) ^ 10260 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_44985986047 : Nat.Prime 44985986047 := by
  apply lucas_primality 44985986047 (3 : ZMod 44985986047)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (43, 1), (58121429, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (43, 1), (58121429, 1)] : List FactorBlock).map factorBlockValue).prod) = 44985986047 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_43
      · exact prime_oneHundredSixtyEightFJ_58121429
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 44985986047) ^ 22492993023 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 44985986047) ^ 14995328682 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 44985986047) ^ 1046185722 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 44985986047) ^ 774 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_45636734023 : Nat.Prime 45636734023 := by
  apply lucas_primality 45636734023 (6 : ZMod 45636734023)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (17, 1), (40674451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (17, 1), (40674451, 1)] : List FactorBlock).map factorBlockValue).prod) = 45636734023 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_11
      · exact prime_oneHundredSixtyEightFJ_17
      · exact prime_oneHundredSixtyEightFJ_40674451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 45636734023) ^ 22818367011 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (6 : ZMod 45636734023) ^ 15212244674 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (6 : ZMod 45636734023) ^ 4148794002 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (6 : ZMod 45636734023) ^ 2684513766 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (6 : ZMod 45636734023) ^ 1122 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_51811814569 : Nat.Prime 51811814569 := by
  apply lucas_primality 51811814569 (26 : ZMod 51811814569)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (2158825607, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (2158825607, 1)] : List FactorBlock).map factorBlockValue).prod) = 51811814569 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_2158825607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (26 : ZMod 51811814569) ^ 25905907284 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (26 : ZMod 51811814569) ^ 17270604856 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (26 : ZMod 51811814569) ^ 24 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_56235048587 : Nat.Prime 56235048587 := by
  apply lucas_primality 56235048587 (2 : ZMod 56235048587)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (27487, 1), (27647, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (27487, 1), (27647, 1)] : List FactorBlock).map factorBlockValue).prod) = 56235048587 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_37
      · exact prime_oneHundredSixtyEightFJ_27487
      · exact prime_oneHundredSixtyEightFJ_27647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 56235048587) ^ 28117524293 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 56235048587) ^ 1519866178 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 56235048587) ^ 2045878 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 56235048587) ^ 2034038 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_62385401941 : Nat.Prime 62385401941 := by
  apply lucas_primality 62385401941 (2 : ZMod 62385401941)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (23, 1), (347, 1), (130279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (23, 1), (347, 1), (130279, 1)] : List FactorBlock).map factorBlockValue).prod) = 62385401941 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_5
      · exact prime_oneHundredSixtyEightFJ_23
      · exact prime_oneHundredSixtyEightFJ_347
      · exact prime_oneHundredSixtyEightFJ_130279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 62385401941) ^ 31192700970 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 62385401941) ^ 20795133980 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 62385401941) ^ 12477080388 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 62385401941) ^ 2712408780 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 62385401941) ^ 179785020 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 62385401941) ^ 478860 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_64404419549 : Nat.Prime 64404419549 := by
  apply lucas_primality 64404419549 (2 : ZMod 64404419549)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (19, 1), (3967, 1), (30517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (19, 1), (3967, 1), (30517, 1)] : List FactorBlock).map factorBlockValue).prod) = 64404419549 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_7
      · exact prime_oneHundredSixtyEightFJ_19
      · exact prime_oneHundredSixtyEightFJ_3967
      · exact prime_oneHundredSixtyEightFJ_30517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 64404419549) ^ 32202209774 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 64404419549) ^ 9200631364 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 64404419549) ^ 3389706292 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 64404419549) ^ 16235044 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 64404419549) ^ 2110444 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_95520658789 : Nat.Prime 95520658789 := by
  apply lucas_primality 95520658789 (6 : ZMod 95520658789)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (36541, 1), (72613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (36541, 1), (72613, 1)] : List FactorBlock).map factorBlockValue).prod) = 95520658789 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_36541
      · exact prime_oneHundredSixtyEightFJ_72613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 95520658789) ^ 47760329394 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (6 : ZMod 95520658789) ^ 31840219596 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (6 : ZMod 95520658789) ^ 2614068 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (6 : ZMod 95520658789) ^ 1315476 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_107278344443 : Nat.Prime 107278344443 := by
  apply lucas_primality 107278344443 (2 : ZMod 107278344443)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (83, 1), (199, 1), (3247513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (83, 1), (199, 1), (3247513, 1)] : List FactorBlock).map factorBlockValue).prod) = 107278344443 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_83
      · exact prime_oneHundredSixtyEightFJ_199
      · exact prime_oneHundredSixtyEightFJ_3247513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 107278344443) ^ 53639172221 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 107278344443) ^ 1292510174 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 107278344443) ^ 539087158 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 107278344443) ^ 33034 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_109736033929 : Nat.Prime 109736033929 := by
  apply lucas_primality 109736033929 (13 : ZMod 109736033929)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (3163, 1), (1445569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (3163, 1), (1445569, 1)] : List FactorBlock).map factorBlockValue).prod) = 109736033929 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_3163
      · exact prime_oneHundredSixtyEightFJ_1445569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 109736033929) ^ 54868016964 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (13 : ZMod 109736033929) ^ 36578677976 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (13 : ZMod 109736033929) ^ 34693656 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (13 : ZMod 109736033929) ^ 75912 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_113168924711 : Nat.Prime 113168924711 := by
  apply lucas_primality 113168924711 (13 : ZMod 113168924711)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (251, 1), (5189, 1), (8689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (251, 1), (5189, 1), (8689, 1)] : List FactorBlock).map factorBlockValue).prod) = 113168924711 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_5
      · exact prime_oneHundredSixtyEightFJ_251
      · exact prime_oneHundredSixtyEightFJ_5189
      · exact prime_oneHundredSixtyEightFJ_8689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 113168924711) ^ 56584462355 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (13 : ZMod 113168924711) ^ 22633784942 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (13 : ZMod 113168924711) ^ 450872210 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (13 : ZMod 113168924711) ^ 21809390 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (13 : ZMod 113168924711) ^ 13024390 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_127411913641 : Nat.Prime 127411913641 := by
  apply lucas_primality 127411913641 (7 : ZMod 127411913641)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (11, 1), (59, 1), (73, 2), (307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (11, 1), (59, 1), (73, 2), (307, 1)] : List FactorBlock).map factorBlockValue).prod) = 127411913641 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_5
      · exact prime_oneHundredSixtyEightFJ_11
      · exact prime_oneHundredSixtyEightFJ_59
      · exact prime_oneHundredSixtyEightFJ_73
      · exact prime_oneHundredSixtyEightFJ_307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 127411913641) ^ 63705956820 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (7 : ZMod 127411913641) ^ 42470637880 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (7 : ZMod 127411913641) ^ 25482382728 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (7 : ZMod 127411913641) ^ 11582901240 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (7 : ZMod 127411913641) ^ 2159523960 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (7 : ZMod 127411913641) ^ 1745368680 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (7 : ZMod 127411913641) ^ 415022520 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_155440836073 : Nat.Prime 155440836073 := by
  apply lucas_primality 155440836073 (5 : ZMod 155440836073)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (89, 1), (373, 1), (65033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (89, 1), (373, 1), (65033, 1)] : List FactorBlock).map factorBlockValue).prod) = 155440836073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_89
      · exact prime_oneHundredSixtyEightFJ_373
      · exact prime_oneHundredSixtyEightFJ_65033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 155440836073) ^ 77720418036 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 155440836073) ^ 51813612024 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 155440836073) ^ 1746526248 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 155440836073) ^ 416731464 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 155440836073) ^ 2390184 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_204046262249 : Nat.Prime 204046262249 := by
  apply lucas_primality 204046262249 (3 : ZMod 204046262249)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (89, 1), (286581829, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (89, 1), (286581829, 1)] : List FactorBlock).map factorBlockValue).prod) = 204046262249 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_89
      · exact prime_oneHundredSixtyEightFJ_286581829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 204046262249) ^ 102023131124 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 204046262249) ^ 2292654632 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 204046262249) ^ 712 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_243364641461 : Nat.Prime 243364641461 := by
  apply lucas_primality 243364641461 (2 : ZMod 243364641461)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (19, 1), (640433267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (19, 1), (640433267, 1)] : List FactorBlock).map factorBlockValue).prod) = 243364641461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_5
      · exact prime_oneHundredSixtyEightFJ_19
      · exact prime_oneHundredSixtyEightFJ_640433267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 243364641461) ^ 121682320730 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 243364641461) ^ 48672928292 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 243364641461) ^ 12808665340 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 243364641461) ^ 380 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_243420692987 : Nat.Prime 243420692987 := by
  apply lucas_primality 243420692987 (2 : ZMod 243420692987)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1283, 1), (3637, 1), (26083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1283, 1), (3637, 1), (26083, 1)] : List FactorBlock).map factorBlockValue).prod) = 243420692987 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_1283
      · exact prime_oneHundredSixtyEightFJ_3637
      · exact prime_oneHundredSixtyEightFJ_26083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 243420692987) ^ 121710346493 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 243420692987) ^ 189727742 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 243420692987) ^ 66928978 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 243420692987) ^ 9332542 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_283126078831 : Nat.Prime 283126078831 := by
  apply lucas_primality 283126078831 (7 : ZMod 283126078831)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (19, 1), (463, 1), (153259, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (19, 1), (463, 1), (153259, 1)] : List FactorBlock).map factorBlockValue).prod) = 283126078831 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_5
      · exact prime_oneHundredSixtyEightFJ_7
      · exact prime_oneHundredSixtyEightFJ_19
      · exact prime_oneHundredSixtyEightFJ_463
      · exact prime_oneHundredSixtyEightFJ_153259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 283126078831) ^ 141563039415 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (7 : ZMod 283126078831) ^ 94375359610 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (7 : ZMod 283126078831) ^ 56625215766 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (7 : ZMod 283126078831) ^ 40446582690 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (7 : ZMod 283126078831) ^ 14901372570 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (7 : ZMod 283126078831) ^ 611503410 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (7 : ZMod 283126078831) ^ 1847370 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_300752680831 : Nat.Prime 300752680831 := by
  apply lucas_primality 300752680831 (3 : ZMod 300752680831)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (1432155623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (1432155623, 1)] : List FactorBlock).map factorBlockValue).prod) = 300752680831 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_5
      · exact prime_oneHundredSixtyEightFJ_7
      · exact prime_oneHundredSixtyEightFJ_1432155623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 300752680831) ^ 150376340415 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 300752680831) ^ 100250893610 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 300752680831) ^ 60150536166 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 300752680831) ^ 42964668690 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 300752680831) ^ 210 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_340078141943 : Nat.Prime 340078141943 := by
  apply lucas_primality 340078141943 (5 : ZMod 340078141943)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 1), (881, 1), (2506583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 1), (881, 1), (2506583, 1)] : List FactorBlock).map factorBlockValue).prod) = 340078141943 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_7
      · exact prime_oneHundredSixtyEightFJ_11
      · exact prime_oneHundredSixtyEightFJ_881
      · exact prime_oneHundredSixtyEightFJ_2506583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 340078141943) ^ 170039070971 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 340078141943) ^ 48582591706 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 340078141943) ^ 30916194722 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 340078141943) ^ 386013782 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 340078141943) ^ 135674 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_343588771969 : Nat.Prime 343588771969 := by
  apply lucas_primality 343588771969 (31 : ZMod 343588771969)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (13, 1), (3931, 1), (17509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (13, 1), (3931, 1), (17509, 1)] : List FactorBlock).map factorBlockValue).prod) = 343588771969 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_13
      · exact prime_oneHundredSixtyEightFJ_3931
      · exact prime_oneHundredSixtyEightFJ_17509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (31 : ZMod 343588771969) ^ 171794385984 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (31 : ZMod 343588771969) ^ 114529590656 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (31 : ZMod 343588771969) ^ 26429905536 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (31 : ZMod 343588771969) ^ 87404928 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (31 : ZMod 343588771969) ^ 19623552 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_350800075411 : Nat.Prime 350800075411 := by
  apply lucas_primality 350800075411 (3 : ZMod 350800075411)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (59, 1), (1399, 1), (141667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (59, 1), (1399, 1), (141667, 1)] : List FactorBlock).map factorBlockValue).prod) = 350800075411 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_5
      · exact prime_oneHundredSixtyEightFJ_59
      · exact prime_oneHundredSixtyEightFJ_1399
      · exact prime_oneHundredSixtyEightFJ_141667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 350800075411) ^ 175400037705 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 350800075411) ^ 116933358470 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 350800075411) ^ 70160015082 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 350800075411) ^ 5945763990 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 350800075411) ^ 250750590 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 350800075411) ^ 2476230 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_362172069821 : Nat.Prime 362172069821 := by
  apply lucas_primality 362172069821 (2 : ZMod 362172069821)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (11, 1), (79, 1), (20838439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (11, 1), (79, 1), (20838439, 1)] : List FactorBlock).map factorBlockValue).prod) = 362172069821 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_5
      · exact prime_oneHundredSixtyEightFJ_11
      · exact prime_oneHundredSixtyEightFJ_79
      · exact prime_oneHundredSixtyEightFJ_20838439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 362172069821) ^ 181086034910 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 362172069821) ^ 72434413964 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 362172069821) ^ 32924733620 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 362172069821) ^ 4584456580 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 362172069821) ^ 17380 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_389524068949 : Nat.Prime 389524068949 := by
  apply lucas_primality 389524068949 (6 : ZMod 389524068949)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (89, 1), (271, 1), (192263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (89, 1), (271, 1), (192263, 1)] : List FactorBlock).map factorBlockValue).prod) = 389524068949 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_7
      · exact prime_oneHundredSixtyEightFJ_89
      · exact prime_oneHundredSixtyEightFJ_271
      · exact prime_oneHundredSixtyEightFJ_192263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 389524068949) ^ 194762034474 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (6 : ZMod 389524068949) ^ 129841356316 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (6 : ZMod 389524068949) ^ 55646295564 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (6 : ZMod 389524068949) ^ 4376674932 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (6 : ZMod 389524068949) ^ 1437358188 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (6 : ZMod 389524068949) ^ 2025996 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_391209657403 : Nat.Prime 391209657403 := by
  apply lucas_primality 391209657403 (2 : ZMod 391209657403)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1559, 1), (41822713, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1559, 1), (41822713, 1)] : List FactorBlock).map factorBlockValue).prod) = 391209657403 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_1559
      · exact prime_oneHundredSixtyEightFJ_41822713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 391209657403) ^ 195604828701 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 391209657403) ^ 130403219134 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 391209657403) ^ 250936278 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 391209657403) ^ 9354 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_532717155151 : Nat.Prime 532717155151 := by
  apply lucas_primality 532717155151 (3 : ZMod 532717155151)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (37, 1), (43, 1), (109, 1), (20479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (37, 1), (43, 1), (109, 1), (20479, 1)] : List FactorBlock).map factorBlockValue).prod) = 532717155151 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_5
      · exact prime_oneHundredSixtyEightFJ_37
      · exact prime_oneHundredSixtyEightFJ_43
      · exact prime_oneHundredSixtyEightFJ_109
      · exact prime_oneHundredSixtyEightFJ_20479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 532717155151) ^ 266358577575 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 532717155151) ^ 177572385050 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 532717155151) ^ 106543431030 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 532717155151) ^ 14397760950 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 532717155151) ^ 12388771050 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 532717155151) ^ 4887313350 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 532717155151) ^ 26012850 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_626696252953 : Nat.Prime 626696252953 := by
  apply lucas_primality 626696252953 (5 : ZMod 626696252953)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 2), (11, 1), (43, 1), (1126649, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 2), (11, 1), (43, 1), (1126649, 1)] : List FactorBlock).map factorBlockValue).prod) = 626696252953 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_7
      · exact prime_oneHundredSixtyEightFJ_11
      · exact prime_oneHundredSixtyEightFJ_43
      · exact prime_oneHundredSixtyEightFJ_1126649
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 626696252953) ^ 313348126476 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 626696252953) ^ 208898750984 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 626696252953) ^ 89528036136 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 626696252953) ^ 56972386632 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 626696252953) ^ 14574331464 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 626696252953) ^ 556248 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_674756143339 : Nat.Prime 674756143339 := by
  apply lucas_primality 674756143339 (3 : ZMod 674756143339)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (67, 2), (313, 1), (80039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (67, 2), (313, 1), (80039, 1)] : List FactorBlock).map factorBlockValue).prod) = 674756143339 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_67
      · exact prime_oneHundredSixtyEightFJ_313
      · exact prime_oneHundredSixtyEightFJ_80039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 674756143339) ^ 337378071669 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 674756143339) ^ 224918714446 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 674756143339) ^ 10070987214 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 674756143339) ^ 2155770426 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 674756143339) ^ 8430342 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_705028111211 : Nat.Prime 705028111211 := by
  apply lucas_primality 705028111211 (2 : ZMod 705028111211)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (67, 1), (149, 1), (7062287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (67, 1), (149, 1), (7062287, 1)] : List FactorBlock).map factorBlockValue).prod) = 705028111211 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_5
      · exact prime_oneHundredSixtyEightFJ_67
      · exact prime_oneHundredSixtyEightFJ_149
      · exact prime_oneHundredSixtyEightFJ_7062287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 705028111211) ^ 352514055605 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 705028111211) ^ 141005622242 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 705028111211) ^ 10522807630 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 705028111211) ^ 4731732290 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 705028111211) ^ 99830 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_720734907931 : Nat.Prime 720734907931 := by
  apply lucas_primality 720734907931 (2 : ZMod 720734907931)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (24024496931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (24024496931, 1)] : List FactorBlock).map factorBlockValue).prod) = 720734907931 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_5
      · exact prime_oneHundredSixtyEightFJ_24024496931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 720734907931) ^ 360367453965 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 720734907931) ^ 240244969310 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 720734907931) ^ 144146981586 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 720734907931) ^ 30 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_749523766273 : Nat.Prime 749523766273 := by
  apply lucas_primality 749523766273 (5 : ZMod 749523766273)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 10), (3, 1), (47, 1), (821, 1), (6323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 10), (3, 1), (47, 1), (821, 1), (6323, 1)] : List FactorBlock).map factorBlockValue).prod) = 749523766273 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_47
      · exact prime_oneHundredSixtyEightFJ_821
      · exact prime_oneHundredSixtyEightFJ_6323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 749523766273) ^ 374761883136 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 749523766273) ^ 249841255424 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 749523766273) ^ 15947314176 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 749523766273) ^ 912940032 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 749523766273) ^ 118539264 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_819350299919 : Nat.Prime 819350299919 := by
  apply lucas_primality 819350299919 (7 : ZMod 819350299919)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (67, 1), (6114554477, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (67, 1), (6114554477, 1)] : List FactorBlock).map factorBlockValue).prod) = 819350299919 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_67
      · exact prime_oneHundredSixtyEightFJ_6114554477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 819350299919) ^ 409675149959 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (7 : ZMod 819350299919) ^ 12229108954 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (7 : ZMod 819350299919) ^ 134 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_1255505416853 : Nat.Prime 1255505416853 := by
  apply lucas_primality 1255505416853 (2 : ZMod 1255505416853)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (59, 1), (5319938207, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (59, 1), (5319938207, 1)] : List FactorBlock).map factorBlockValue).prod) = 1255505416853 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_59
      · exact prime_oneHundredSixtyEightFJ_5319938207
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1255505416853) ^ 627752708426 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1255505416853) ^ 21279752828 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1255505416853) ^ 236 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_1801134966187 : Nat.Prime 1801134966187 := by
  apply lucas_primality 1801134966187 (2 : ZMod 1801134966187)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (17, 1), (5886061981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (17, 1), (5886061981, 1)] : List FactorBlock).map factorBlockValue).prod) = 1801134966187 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_17
      · exact prime_oneHundredSixtyEightFJ_5886061981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1801134966187) ^ 900567483093 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1801134966187) ^ 600378322062 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1801134966187) ^ 105949115658 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1801134966187) ^ 306 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_1932132586471 : Nat.Prime 1932132586471 := by
  apply lucas_primality 1932132586471 (3 : ZMod 1932132586471)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (64404419549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (64404419549, 1)] : List FactorBlock).map factorBlockValue).prod) = 1932132586471 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_5
      · exact prime_oneHundredSixtyEightFJ_64404419549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1932132586471) ^ 966066293235 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1932132586471) ^ 644044195490 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1932132586471) ^ 386426517294 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1932132586471) ^ 30 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_1959168993193 : Nat.Prime 1959168993193 := by
  apply lucas_primality 1959168993193 (7 : ZMod 1959168993193)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (27210680461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (27210680461, 1)] : List FactorBlock).map factorBlockValue).prod) = 1959168993193 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_27210680461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 1959168993193) ^ 979584496596 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (7 : ZMod 1959168993193) ^ 653056331064 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (7 : ZMod 1959168993193) ^ 72 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_2466717089059 : Nat.Prime 2466717089059 := by
  apply lucas_primality 2466717089059 (2 : ZMod 2466717089059)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (37, 1), (5521, 1), (670853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (37, 1), (5521, 1), (670853, 1)] : List FactorBlock).map factorBlockValue).prod) = 2466717089059 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_37
      · exact prime_oneHundredSixtyEightFJ_5521
      · exact prime_oneHundredSixtyEightFJ_670853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2466717089059) ^ 1233358544529 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2466717089059) ^ 822239029686 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2466717089059) ^ 66668029434 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2466717089059) ^ 446788098 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2466717089059) ^ 3676986 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_2784189228833 : Nat.Prime 2784189228833 := by
  apply lucas_primality 2784189228833 (3 : ZMod 2784189228833)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (11, 1), (37, 1), (109, 1), (271, 1), (7237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (11, 1), (37, 1), (109, 1), (271, 1), (7237, 1)] : List FactorBlock).map factorBlockValue).prod) = 2784189228833 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_11
      · exact prime_oneHundredSixtyEightFJ_37
      · exact prime_oneHundredSixtyEightFJ_109
      · exact prime_oneHundredSixtyEightFJ_271
      · exact prime_oneHundredSixtyEightFJ_7237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2784189228833) ^ 1392094614416 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2784189228833) ^ 253108111712 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2784189228833) ^ 75248357536 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2784189228833) ^ 25543020448 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2784189228833) ^ 10273760992 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2784189228833) ^ 384715936 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_3150736886257 : Nat.Prime 3150736886257 := by
  apply lucas_primality 3150736886257 (5 : ZMod 3150736886257)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (23, 1), (113, 1), (25256003, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (23, 1), (113, 1), (25256003, 1)] : List FactorBlock).map factorBlockValue).prod) = 3150736886257 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_23
      · exact prime_oneHundredSixtyEightFJ_113
      · exact prime_oneHundredSixtyEightFJ_25256003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 3150736886257) ^ 1575368443128 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 3150736886257) ^ 1050245628752 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 3150736886257) ^ 136988560272 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 3150736886257) ^ 27882627312 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 3150736886257) ^ 124752 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_3353735554207 : Nat.Prime 3353735554207 := by
  apply lucas_primality 3353735554207 (3 : ZMod 3353735554207)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (757, 1), (25243, 1), (29251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (757, 1), (25243, 1), (29251, 1)] : List FactorBlock).map factorBlockValue).prod) = 3353735554207 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_757
      · exact prime_oneHundredSixtyEightFJ_25243
      · exact prime_oneHundredSixtyEightFJ_29251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3353735554207) ^ 1676867777103 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 3353735554207) ^ 1117911851402 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 3353735554207) ^ 4430297958 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 3353735554207) ^ 132858042 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 3353735554207) ^ 114653706 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_3467396948839 : Nat.Prime 3467396948839 := by
  apply lucas_primality 3467396948839 (3 : ZMod 3467396948839)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (109, 1), (149, 1), (353, 1), (100801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (109, 1), (149, 1), (353, 1), (100801, 1)] : List FactorBlock).map factorBlockValue).prod) = 3467396948839 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_109
      · exact prime_oneHundredSixtyEightFJ_149
      · exact prime_oneHundredSixtyEightFJ_353
      · exact prime_oneHundredSixtyEightFJ_100801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3467396948839) ^ 1733698474419 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 3467396948839) ^ 1155798982946 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 3467396948839) ^ 31810981182 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 3467396948839) ^ 23271120462 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 3467396948839) ^ 9822654246 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 3467396948839) ^ 34398438 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_4014078193691 : Nat.Prime 4014078193691 := by
  apply lucas_primality 4014078193691 (2 : ZMod 4014078193691)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (829, 1), (1051, 1), (460711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (829, 1), (1051, 1), (460711, 1)] : List FactorBlock).map factorBlockValue).prod) = 4014078193691 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_5
      · exact prime_oneHundredSixtyEightFJ_829
      · exact prime_oneHundredSixtyEightFJ_1051
      · exact prime_oneHundredSixtyEightFJ_460711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4014078193691) ^ 2007039096845 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4014078193691) ^ 802815638738 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4014078193691) ^ 4842072610 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4014078193691) ^ 3819294190 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4014078193691) ^ 8712790 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_4375221181031 : Nat.Prime 4375221181031 := by
  apply lucas_primality 4375221181031 (14 : ZMod 4375221181031)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (31, 1), (2016230959, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (31, 1), (2016230959, 1)] : List FactorBlock).map factorBlockValue).prod) = 4375221181031 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_5
      · exact prime_oneHundredSixtyEightFJ_7
      · exact prime_oneHundredSixtyEightFJ_31
      · exact prime_oneHundredSixtyEightFJ_2016230959
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 4375221181031) ^ 2187610590515 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (14 : ZMod 4375221181031) ^ 875044236206 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (14 : ZMod 4375221181031) ^ 625031597290 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (14 : ZMod 4375221181031) ^ 141136167130 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (14 : ZMod 4375221181031) ^ 2170 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_4934642467331 : Nat.Prime 4934642467331 := by
  apply lucas_primality 4934642467331 (2 : ZMod 4934642467331)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (25919, 1), (19038707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (25919, 1), (19038707, 1)] : List FactorBlock).map factorBlockValue).prod) = 4934642467331 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_5
      · exact prime_oneHundredSixtyEightFJ_25919
      · exact prime_oneHundredSixtyEightFJ_19038707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4934642467331) ^ 2467321233665 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4934642467331) ^ 986928493466 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4934642467331) ^ 190387070 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4934642467331) ^ 259190 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_6653737764137 : Nat.Prime 6653737764137 := by
  apply lucas_primality 6653737764137 (3 : ZMod 6653737764137)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (31333, 1), (26544449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (31333, 1), (26544449, 1)] : List FactorBlock).map factorBlockValue).prod) = 6653737764137 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_31333
      · exact prime_oneHundredSixtyEightFJ_26544449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 6653737764137) ^ 3326868882068 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 6653737764137) ^ 212355592 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 6653737764137) ^ 250664 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_8097073720069 : Nat.Prime 8097073720069 := by
  apply lucas_primality 8097073720069 (2 : ZMod 8097073720069)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (674756143339, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (674756143339, 1)] : List FactorBlock).map factorBlockValue).prod) = 8097073720069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_674756143339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 8097073720069) ^ 4048536860034 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 8097073720069) ^ 2699024573356 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 8097073720069) ^ 12 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_10221013826539 : Nat.Prime 10221013826539 := by
  apply lucas_primality 10221013826539 (2 : ZMod 10221013826539)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (43, 1), (39616332661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (43, 1), (39616332661, 1)] : List FactorBlock).map factorBlockValue).prod) = 10221013826539 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_43
      · exact prime_oneHundredSixtyEightFJ_39616332661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 10221013826539) ^ 5110506913269 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 10221013826539) ^ 3407004608846 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 10221013826539) ^ 237697995966 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 10221013826539) ^ 258 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_10981426522441 : Nat.Prime 10981426522441 := by
  apply lucas_primality 10981426522441 (43 : ZMod 10981426522441)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (11, 1), (31, 1), (103, 1), (647, 1), (4027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (11, 1), (31, 1), (103, 1), (647, 1), (4027, 1)] : List FactorBlock).map factorBlockValue).prod) = 10981426522441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_5
      · exact prime_oneHundredSixtyEightFJ_11
      · exact prime_oneHundredSixtyEightFJ_31
      · exact prime_oneHundredSixtyEightFJ_103
      · exact prime_oneHundredSixtyEightFJ_647
      · exact prime_oneHundredSixtyEightFJ_4027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (43 : ZMod 10981426522441) ^ 5490713261220 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (43 : ZMod 10981426522441) ^ 3660475507480 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (43 : ZMod 10981426522441) ^ 2196285304488 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (43 : ZMod 10981426522441) ^ 998311502040 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (43 : ZMod 10981426522441) ^ 354239565240 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (43 : ZMod 10981426522441) ^ 106615791480 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (43 : ZMod 10981426522441) ^ 16972838520 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (43 : ZMod 10981426522441) ^ 2726949720 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_11333960240279 : Nat.Prime 11333960240279 := by
  apply lucas_primality 11333960240279 (17 : ZMod 11333960240279)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (29, 1), (15031777507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (29, 1), (15031777507, 1)] : List FactorBlock).map factorBlockValue).prod) = 11333960240279 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_13
      · exact prime_oneHundredSixtyEightFJ_29
      · exact prime_oneHundredSixtyEightFJ_15031777507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 11333960240279) ^ 5666980120139 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (17 : ZMod 11333960240279) ^ 871843095406 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (17 : ZMod 11333960240279) ^ 390826215182 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (17 : ZMod 11333960240279) ^ 754 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_13763311522591 : Nat.Prime 13763311522591 := by
  apply lucas_primality 13763311522591 (6 : ZMod 13763311522591)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (3779, 1), (17343101, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (3779, 1), (17343101, 1)] : List FactorBlock).map factorBlockValue).prod) = 13763311522591 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_5
      · exact prime_oneHundredSixtyEightFJ_7
      · exact prime_oneHundredSixtyEightFJ_3779
      · exact prime_oneHundredSixtyEightFJ_17343101
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 13763311522591) ^ 6881655761295 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (6 : ZMod 13763311522591) ^ 4587770507530 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (6 : ZMod 13763311522591) ^ 2752662304518 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (6 : ZMod 13763311522591) ^ 1966187360370 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (6 : ZMod 13763311522591) ^ 3642051210 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (6 : ZMod 13763311522591) ^ 793590 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_13971226936099 : Nat.Prime 13971226936099 := by
  apply lucas_primality 13971226936099 (2 : ZMod 13971226936099)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (21617, 1), (6336347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (21617, 1), (6336347, 1)] : List FactorBlock).map factorBlockValue).prod) = 13971226936099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_17
      · exact prime_oneHundredSixtyEightFJ_21617
      · exact prime_oneHundredSixtyEightFJ_6336347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 13971226936099) ^ 6985613468049 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 13971226936099) ^ 4657075645366 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 13971226936099) ^ 821836878594 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 13971226936099) ^ 646307394 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 13971226936099) ^ 2204934 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_15239370115789 : Nat.Prime 15239370115789 := by
  apply lucas_primality 15239370115789 (2 : ZMod 15239370115789)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (13, 1), (547, 1), (25512737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (13, 1), (547, 1), (25512737, 1)] : List FactorBlock).map factorBlockValue).prod) = 15239370115789 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_7
      · exact prime_oneHundredSixtyEightFJ_13
      · exact prime_oneHundredSixtyEightFJ_547
      · exact prime_oneHundredSixtyEightFJ_25512737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 15239370115789) ^ 7619685057894 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 15239370115789) ^ 5079790038596 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 15239370115789) ^ 2177052873684 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 15239370115789) ^ 1172259239676 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 15239370115789) ^ 27859908804 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 15239370115789) ^ 597324 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_17160791887493 : Nat.Prime 17160791887493 := by
  apply lucas_primality 17160791887493 (2 : ZMod 17160791887493)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (61, 1), (6393737663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (61, 1), (6393737663, 1)] : List FactorBlock).map factorBlockValue).prod) = 17160791887493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_11
      · exact prime_oneHundredSixtyEightFJ_61
      · exact prime_oneHundredSixtyEightFJ_6393737663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 17160791887493) ^ 8580395943746 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 17160791887493) ^ 1560071989772 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 17160791887493) ^ 281324457172 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 17160791887493) ^ 2684 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_19690644203179 : Nat.Prime 19690644203179 := by
  apply lucas_primality 19690644203179 (2 : ZMod 19690644203179)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (2551, 1), (98958901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (2551, 1), (98958901, 1)] : List FactorBlock).map factorBlockValue).prod) = 19690644203179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_13
      · exact prime_oneHundredSixtyEightFJ_2551
      · exact prime_oneHundredSixtyEightFJ_98958901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 19690644203179) ^ 9845322101589 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 19690644203179) ^ 6563548067726 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 19690644203179) ^ 1514664938706 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 19690644203179) ^ 7718794278 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 19690644203179) ^ 198978 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_23642614645087 : Nat.Prime 23642614645087 := by
  apply lucas_primality 23642614645087 (3 : ZMod 23642614645087)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (71, 1), (157, 1), (353497423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (71, 1), (157, 1), (353497423, 1)] : List FactorBlock).map factorBlockValue).prod) = 23642614645087 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_71
      · exact prime_oneHundredSixtyEightFJ_157
      · exact prime_oneHundredSixtyEightFJ_353497423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 23642614645087) ^ 11821307322543 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 23642614645087) ^ 7880871548362 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 23642614645087) ^ 332994572466 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 23642614645087) ^ 150589902198 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 23642614645087) ^ 66882 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_24251390888827 : Nat.Prime 24251390888827 := by
  apply lucas_primality 24251390888827 (2 : ZMod 24251390888827)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (4519, 1), (894423209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (4519, 1), (894423209, 1)] : List FactorBlock).map factorBlockValue).prod) = 24251390888827 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_4519
      · exact prime_oneHundredSixtyEightFJ_894423209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 24251390888827) ^ 12125695444413 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 24251390888827) ^ 8083796962942 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 24251390888827) ^ 5366539254 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 24251390888827) ^ 27114 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_27509450135411 : Nat.Prime 27509450135411 := by
  apply lucas_primality 27509450135411 (2 : ZMod 27509450135411)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (53, 1), (79, 1), (657020543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (53, 1), (79, 1), (657020543, 1)] : List FactorBlock).map factorBlockValue).prod) = 27509450135411 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_5
      · exact prime_oneHundredSixtyEightFJ_53
      · exact prime_oneHundredSixtyEightFJ_79
      · exact prime_oneHundredSixtyEightFJ_657020543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 27509450135411) ^ 13754725067705 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 27509450135411) ^ 5501890027082 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 27509450135411) ^ 519046228970 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 27509450135411) ^ 348220887790 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 27509450135411) ^ 41870 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_32027326483181 : Nat.Prime 32027326483181 := by
  apply lucas_primality 32027326483181 (2 : ZMod 32027326483181)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 2), (32680945391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 2), (32680945391, 1)] : List FactorBlock).map factorBlockValue).prod) = 32027326483181 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_5
      · exact prime_oneHundredSixtyEightFJ_7
      · exact prime_oneHundredSixtyEightFJ_32680945391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 32027326483181) ^ 16013663241590 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 32027326483181) ^ 6405465296636 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 32027326483181) ^ 4575332354740 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 32027326483181) ^ 980 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_32885892172379 : Nat.Prime 32885892172379 := by
  apply lucas_primality 32885892172379 (2 : ZMod 32885892172379)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (17, 1), (223, 1), (619623397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (17, 1), (223, 1), (619623397, 1)] : List FactorBlock).map factorBlockValue).prod) = 32885892172379 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_7
      · exact prime_oneHundredSixtyEightFJ_17
      · exact prime_oneHundredSixtyEightFJ_223
      · exact prime_oneHundredSixtyEightFJ_619623397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 32885892172379) ^ 16442946086189 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 32885892172379) ^ 4697984596054 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 32885892172379) ^ 1934464245434 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 32885892172379) ^ 147470368486 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 32885892172379) ^ 53074 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_33699022756921 : Nat.Prime 33699022756921 := by
  apply lucas_primality 33699022756921 (13 : ZMod 33699022756921)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (5, 1), (19, 1), (29, 1), (191, 1), (296489, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (5, 1), (19, 1), (29, 1), (191, 1), (296489, 1)] : List FactorBlock).map factorBlockValue).prod) = 33699022756921 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_5
      · exact prime_oneHundredSixtyEightFJ_19
      · exact prime_oneHundredSixtyEightFJ_29
      · exact prime_oneHundredSixtyEightFJ_191
      · exact prime_oneHundredSixtyEightFJ_296489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 33699022756921) ^ 16849511378460 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (13 : ZMod 33699022756921) ^ 11233007585640 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (13 : ZMod 33699022756921) ^ 6739804551384 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (13 : ZMod 33699022756921) ^ 1773632776680 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (13 : ZMod 33699022756921) ^ 1162035267480 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (13 : ZMod 33699022756921) ^ 176434674120 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (13 : ZMod 33699022756921) ^ 113660280 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_35208869166271 : Nat.Prime 35208869166271 := by
  apply lucas_primality 35208869166271 (3 : ZMod 35208869166271)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (391209657403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (391209657403, 1)] : List FactorBlock).map factorBlockValue).prod) = 35208869166271 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_5
      · exact prime_oneHundredSixtyEightFJ_391209657403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 35208869166271) ^ 17604434583135 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 35208869166271) ^ 11736289722090 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 35208869166271) ^ 7041773833254 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 35208869166271) ^ 90 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_45752552594669 : Nat.Prime 45752552594669 := by
  apply lucas_primality 45752552594669 (2 : ZMod 45752552594669)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (47, 1), (243364641461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (47, 1), (243364641461, 1)] : List FactorBlock).map factorBlockValue).prod) = 45752552594669 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_47
      · exact prime_oneHundredSixtyEightFJ_243364641461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 45752552594669) ^ 22876276297334 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 45752552594669) ^ 973458565844 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 45752552594669) ^ 188 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_54647127243493 : Nat.Prime 54647127243493 := by
  apply lucas_primality 54647127243493 (2 : ZMod 54647127243493)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (17, 1), (257, 1), (148903877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (17, 1), (257, 1), (148903877, 1)] : List FactorBlock).map factorBlockValue).prod) = 54647127243493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_7
      · exact prime_oneHundredSixtyEightFJ_17
      · exact prime_oneHundredSixtyEightFJ_257
      · exact prime_oneHundredSixtyEightFJ_148903877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 54647127243493) ^ 27323563621746 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 54647127243493) ^ 18215709081164 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 54647127243493) ^ 7806732463356 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 54647127243493) ^ 3214536896676 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 54647127243493) ^ 212634736356 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 54647127243493) ^ 366996 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_64507159604807 : Nat.Prime 64507159604807 := by
  apply lucas_primality 64507159604807 (5 : ZMod 64507159604807)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (307, 1), (13109, 1), (8014381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (307, 1), (13109, 1), (8014381, 1)] : List FactorBlock).map factorBlockValue).prod) = 64507159604807 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_307
      · exact prime_oneHundredSixtyEightFJ_13109
      · exact prime_oneHundredSixtyEightFJ_8014381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 64507159604807) ^ 32253579802403 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 64507159604807) ^ 210121041058 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 64507159604807) ^ 4920829934 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 64507159604807) ^ 8048926 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_104196394828751 : Nat.Prime 104196394828751 := by
  apply lucas_primality 104196394828751 (14 : ZMod 104196394828751)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 4), (7, 1), (53, 1), (224682253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 4), (7, 1), (53, 1), (224682253, 1)] : List FactorBlock).map factorBlockValue).prod) = 104196394828751 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_5
      · exact prime_oneHundredSixtyEightFJ_7
      · exact prime_oneHundredSixtyEightFJ_53
      · exact prime_oneHundredSixtyEightFJ_224682253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 104196394828751) ^ 52098197414375 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (14 : ZMod 104196394828751) ^ 20839278965750 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (14 : ZMod 104196394828751) ^ 14885199261250 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (14 : ZMod 104196394828751) ^ 1965969713750 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (14 : ZMod 104196394828751) ^ 463750 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_130417135331503 : Nat.Prime 130417135331503 := by
  apply lucas_primality 130417135331503 (3 : ZMod 130417135331503)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 1), (749523766273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 1), (749523766273, 1)] : List FactorBlock).map factorBlockValue).prod) = 130417135331503 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_29
      · exact prime_oneHundredSixtyEightFJ_749523766273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 130417135331503) ^ 65208567665751 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 130417135331503) ^ 43472378443834 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 130417135331503) ^ 4497142597638 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 130417135331503) ^ 174 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_170139791857879 : Nat.Prime 170139791857879 := by
  apply lucas_primality 170139791857879 (3 : ZMod 170139791857879)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (3150736886257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (3150736886257, 1)] : List FactorBlock).map factorBlockValue).prod) = 170139791857879 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_3150736886257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 170139791857879) ^ 85069895928939 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 170139791857879) ^ 56713263952626 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 170139791857879) ^ 54 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_171657507882011 : Nat.Prime 171657507882011 := by
  apply lucas_primality 171657507882011 (2 : ZMod 171657507882011)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (271, 1), (47581, 1), (1331251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (271, 1), (47581, 1), (1331251, 1)] : List FactorBlock).map factorBlockValue).prod) = 171657507882011 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_5
      · exact prime_oneHundredSixtyEightFJ_271
      · exact prime_oneHundredSixtyEightFJ_47581
      · exact prime_oneHundredSixtyEightFJ_1331251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 171657507882011) ^ 85828753941005 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 171657507882011) ^ 34331501576402 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 171657507882011) ^ 633422538310 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 171657507882011) ^ 3607690210 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 171657507882011) ^ 128944510 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_181040488126411 : Nat.Prime 181040488126411 := by
  apply lucas_primality 181040488126411 (3 : ZMod 181040488126411)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 2), (449, 1), (10303, 1), (10781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 2), (449, 1), (10303, 1), (10781, 1)] : List FactorBlock).map factorBlockValue).prod) = 181040488126411 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_5
      · exact prime_oneHundredSixtyEightFJ_11
      · exact prime_oneHundredSixtyEightFJ_449
      · exact prime_oneHundredSixtyEightFJ_10303
      · exact prime_oneHundredSixtyEightFJ_10781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 181040488126411) ^ 90520244063205 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 181040488126411) ^ 60346829375470 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 181040488126411) ^ 36208097625282 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 181040488126411) ^ 16458226193310 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 181040488126411) ^ 403208214090 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 181040488126411) ^ 17571628470 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 181040488126411) ^ 16792550610 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_198842527769411 : Nat.Prime 198842527769411 := by
  apply lucas_primality 198842527769411 (2 : ZMod 198842527769411)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (19, 1), (53, 1), (6991, 1), (403499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (19, 1), (53, 1), (6991, 1), (403499, 1)] : List FactorBlock).map factorBlockValue).prod) = 198842527769411 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_5
      · exact prime_oneHundredSixtyEightFJ_7
      · exact prime_oneHundredSixtyEightFJ_19
      · exact prime_oneHundredSixtyEightFJ_53
      · exact prime_oneHundredSixtyEightFJ_6991
      · exact prime_oneHundredSixtyEightFJ_403499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 198842527769411) ^ 99421263884705 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 198842527769411) ^ 39768505553882 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 198842527769411) ^ 28406075395630 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 198842527769411) ^ 10465396198390 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 198842527769411) ^ 3751745806970 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 198842527769411) ^ 28442644510 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 198842527769411) ^ 492795590 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_204285462728549 : Nat.Prime 204285462728549 := by
  apply lucas_primality 204285462728549 (2 : ZMod 204285462728549)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (46381, 1), (1101126877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (46381, 1), (1101126877, 1)] : List FactorBlock).map factorBlockValue).prod) = 204285462728549 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_46381
      · exact prime_oneHundredSixtyEightFJ_1101126877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 204285462728549) ^ 102142731364274 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 204285462728549) ^ 4404507508 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 204285462728549) ^ 185524 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_240844691621461 : Nat.Prime 240844691621461 := by
  apply lucas_primality 240844691621461 (2 : ZMod 240844691621461)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (4014078193691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (4014078193691, 1)] : List FactorBlock).map factorBlockValue).prod) = 240844691621461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_5
      · exact prime_oneHundredSixtyEightFJ_4014078193691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 240844691621461) ^ 120422345810730 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 240844691621461) ^ 80281563873820 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 240844691621461) ^ 48168938324292 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 240844691621461) ^ 60 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_258862483991359 : Nat.Prime 258862483991359 := by
  apply lucas_primality 258862483991359 (6 : ZMod 258862483991359)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (10789, 1), (102534983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (10789, 1), (102534983, 1)] : List FactorBlock).map factorBlockValue).prod) = 258862483991359 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_13
      · exact prime_oneHundredSixtyEightFJ_10789
      · exact prime_oneHundredSixtyEightFJ_102534983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 258862483991359) ^ 129431241995679 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (6 : ZMod 258862483991359) ^ 86287494663786 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (6 : ZMod 258862483991359) ^ 19912498768566 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (6 : ZMod 258862483991359) ^ 23993186022 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (6 : ZMod 258862483991359) ^ 2524626 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_366020420757353 : Nat.Prime 366020420757353 := by
  apply lucas_primality 366020420757353 (3 : ZMod 366020420757353)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (45752552594669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (45752552594669, 1)] : List FactorBlock).map factorBlockValue).prod) = 366020420757353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_45752552594669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 366020420757353) ^ 183010210378676 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 366020420757353) ^ 8 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_605401060944023 : Nat.Prime 605401060944023 := by
  apply lucas_primality 605401060944023 (5 : ZMod 605401060944023)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (701, 1), (9769, 1), (6314617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (701, 1), (9769, 1), (6314617, 1)] : List FactorBlock).map factorBlockValue).prod) = 605401060944023 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_7
      · exact prime_oneHundredSixtyEightFJ_701
      · exact prime_oneHundredSixtyEightFJ_9769
      · exact prime_oneHundredSixtyEightFJ_6314617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 605401060944023) ^ 302700530472011 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 605401060944023) ^ 86485865849146 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 605401060944023) ^ 863624908622 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 605401060944023) ^ 61971651238 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 605401060944023) ^ 95872966 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_621760403722501 : Nat.Prime 621760403722501 := by
  apply lucas_primality 621760403722501 (26 : ZMod 621760403722501)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 4), (7, 1), (59, 1), (66909917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 4), (7, 1), (59, 1), (66909917, 1)] : List FactorBlock).map factorBlockValue).prod) = 621760403722501 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_5
      · exact prime_oneHundredSixtyEightFJ_7
      · exact prime_oneHundredSixtyEightFJ_59
      · exact prime_oneHundredSixtyEightFJ_66909917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (26 : ZMod 621760403722501) ^ 310880201861250 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (26 : ZMod 621760403722501) ^ 207253467907500 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (26 : ZMod 621760403722501) ^ 124352080744500 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (26 : ZMod 621760403722501) ^ 88822914817500 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (26 : ZMod 621760403722501) ^ 10538311927500 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (26 : ZMod 621760403722501) ^ 9292500 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_808418374374301 : Nat.Prime 808418374374301 := by
  apply lucas_primality 808418374374301 (6 : ZMod 808418374374301)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (272809, 1), (9877709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (272809, 1), (9877709, 1)] : List FactorBlock).map factorBlockValue).prod) = 808418374374301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_5
      · exact prime_oneHundredSixtyEightFJ_272809
      · exact prime_oneHundredSixtyEightFJ_9877709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 808418374374301) ^ 404209187187150 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (6 : ZMod 808418374374301) ^ 269472791458100 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (6 : ZMod 808418374374301) ^ 161683674874860 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (6 : ZMod 808418374374301) ^ 2963312700 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (6 : ZMod 808418374374301) ^ 81842700 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_910008911973521 : Nat.Prime 910008911973521 := by
  apply lucas_primality 910008911973521 (3 : ZMod 910008911973521)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (5843, 1), (1946792983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (5843, 1), (1946792983, 1)] : List FactorBlock).map factorBlockValue).prod) = 910008911973521 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_5
      · exact prime_oneHundredSixtyEightFJ_5843
      · exact prime_oneHundredSixtyEightFJ_1946792983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 910008911973521) ^ 455004455986760 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 910008911973521) ^ 182001782394704 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 910008911973521) ^ 155743438640 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 910008911973521) ^ 467440 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_1029945047292067 : Nat.Prime 1029945047292067 := by
  apply lucas_primality 1029945047292067 (3 : ZMod 1029945047292067)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (171657507882011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (171657507882011, 1)] : List FactorBlock).map factorBlockValue).prod) = 1029945047292067 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_171657507882011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1029945047292067) ^ 514972523646033 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1029945047292067) ^ 343315015764022 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1029945047292067) ^ 6 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_1200138209940499 : Nat.Prime 1200138209940499 := by
  apply lucas_primality 1200138209940499 (2 : ZMod 1200138209940499)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (230551, 1), (37721171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (230551, 1), (37721171, 1)] : List FactorBlock).map factorBlockValue).prod) = 1200138209940499 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_23
      · exact prime_oneHundredSixtyEightFJ_230551
      · exact prime_oneHundredSixtyEightFJ_37721171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1200138209940499) ^ 600069104970249 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1200138209940499) ^ 400046069980166 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1200138209940499) ^ 52179922171326 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1200138209940499) ^ 5205521598 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1200138209940499) ^ 31816038 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_1221722587537021 : Nat.Prime 1221722587537021 := by
  apply lucas_primality 1221722587537021 (10 : ZMod 1221722587537021)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (131, 1), (51811814569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (131, 1), (51811814569, 1)] : List FactorBlock).map factorBlockValue).prod) = 1221722587537021 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_5
      · exact prime_oneHundredSixtyEightFJ_131
      · exact prime_oneHundredSixtyEightFJ_51811814569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 1221722587537021) ^ 610861293768510 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (10 : ZMod 1221722587537021) ^ 407240862512340 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (10 : ZMod 1221722587537021) ^ 244344517507404 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (10 : ZMod 1221722587537021) ^ 9326126622420 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (10 : ZMod 1221722587537021) ^ 23580 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_1297434865222957 : Nat.Prime 1297434865222957 := by
  apply lucas_primality 1297434865222957 (2 : ZMod 1297434865222957)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (37, 1), (41, 2), (83, 1), (20943863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (37, 1), (41, 2), (83, 1), (20943863, 1)] : List FactorBlock).map factorBlockValue).prod) = 1297434865222957 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_37
      · exact prime_oneHundredSixtyEightFJ_41
      · exact prime_oneHundredSixtyEightFJ_83
      · exact prime_oneHundredSixtyEightFJ_20943863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1297434865222957) ^ 648717432611478 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1297434865222957) ^ 432478288407652 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1297434865222957) ^ 35065807168188 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1297434865222957) ^ 31644752810316 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1297434865222957) ^ 15631745364132 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1297434865222957) ^ 61948212 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_1458405570906899 : Nat.Prime 1458405570906899 := by
  apply lucas_primality 1458405570906899 (2 : ZMod 1458405570906899)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (359, 1), (1129, 1), (1193, 1), (1508063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (359, 1), (1129, 1), (1193, 1), (1508063, 1)] : List FactorBlock).map factorBlockValue).prod) = 1458405570906899 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_359
      · exact prime_oneHundredSixtyEightFJ_1129
      · exact prime_oneHundredSixtyEightFJ_1193
      · exact prime_oneHundredSixtyEightFJ_1508063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1458405570906899) ^ 729202785453449 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1458405570906899) ^ 4062411061022 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1458405570906899) ^ 1291767556162 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1458405570906899) ^ 1222469045186 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 1458405570906899) ^ 967072046 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_2787704921362001 : Nat.Prime 2787704921362001 := by
  apply lucas_primality 2787704921362001 (3 : ZMod 2787704921362001)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 3), (907, 1), (31151, 1), (49333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 3), (907, 1), (31151, 1), (49333, 1)] : List FactorBlock).map factorBlockValue).prod) = 2787704921362001 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_5
      · exact prime_oneHundredSixtyEightFJ_907
      · exact prime_oneHundredSixtyEightFJ_31151
      · exact prime_oneHundredSixtyEightFJ_49333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2787704921362001) ^ 1393852460681000 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2787704921362001) ^ 557540984272400 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2787704921362001) ^ 3073544566000 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2787704921362001) ^ 89490062000 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2787704921362001) ^ 56507914000 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_3100802632301809 : Nat.Prime 3100802632301809 := by
  apply lucas_primality 3100802632301809 (11 : ZMod 3100802632301809)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (7, 1), (73, 1), (14046543779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (7, 1), (73, 1), (14046543779, 1)] : List FactorBlock).map factorBlockValue).prod) = 3100802632301809 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_7
      · exact prime_oneHundredSixtyEightFJ_73
      · exact prime_oneHundredSixtyEightFJ_14046543779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 3100802632301809) ^ 1550401316150904 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (11 : ZMod 3100802632301809) ^ 1033600877433936 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (11 : ZMod 3100802632301809) ^ 442971804614544 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (11 : ZMod 3100802632301809) ^ 42476748387696 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (11 : ZMod 3100802632301809) ^ 220752 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_3563453043581677 : Nat.Prime 3563453043581677 := by
  apply lucas_primality 3563453043581677 (5 : ZMod 3563453043581677)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (4241, 1), (80279, 1), (124601, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (4241, 1), (80279, 1), (124601, 1)] : List FactorBlock).map factorBlockValue).prod) = 3563453043581677 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_7
      · exact prime_oneHundredSixtyEightFJ_4241
      · exact prime_oneHundredSixtyEightFJ_80279
      · exact prime_oneHundredSixtyEightFJ_124601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 3563453043581677) ^ 1781726521790838 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 3563453043581677) ^ 1187817681193892 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 3563453043581677) ^ 509064720511668 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 3563453043581677) ^ 840238869036 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 3563453043581677) ^ 44388358644 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 3563453043581677) ^ 28598912076 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_4490118111021163 : Nat.Prime 4490118111021163 := by
  apply lucas_primality 4490118111021163 (2 : ZMod 4490118111021163)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (139, 1), (1259, 1), (4276278527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (139, 1), (1259, 1), (4276278527, 1)] : List FactorBlock).map factorBlockValue).prod) = 4490118111021163 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_139
      · exact prime_oneHundredSixtyEightFJ_1259
      · exact prime_oneHundredSixtyEightFJ_4276278527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4490118111021163) ^ 2245059055510581 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4490118111021163) ^ 1496706037007054 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4490118111021163) ^ 32303007992958 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4490118111021163) ^ 3566416291518 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4490118111021163) ^ 1050006 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_5575409842724003 : Nat.Prime 5575409842724003 := by
  apply lucas_primality 5575409842724003 (2 : ZMod 5575409842724003)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2787704921362001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2787704921362001, 1)] : List FactorBlock).map factorBlockValue).prod) = 5575409842724003 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_2787704921362001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 5575409842724003) ^ 2787704921362001 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 5575409842724003) ^ 2 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_6217604037225011 : Nat.Prime 6217604037225011 := by
  apply lucas_primality 6217604037225011 (2 : ZMod 6217604037225011)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (621760403722501, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (621760403722501, 1)] : List FactorBlock).map factorBlockValue).prod) = 6217604037225011 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_5
      · exact prime_oneHundredSixtyEightFJ_621760403722501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 6217604037225011) ^ 3108802018612505 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 6217604037225011) ^ 1243520807445002 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 6217604037225011) ^ 10 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_8648524669571609 : Nat.Prime 8648524669571609 := by
  apply lucas_primality 8648524669571609 (3 : ZMod 8648524669571609)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (242989, 1), (4449030959, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (242989, 1), (4449030959, 1)] : List FactorBlock).map factorBlockValue).prod) = 8648524669571609 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_242989
      · exact prime_oneHundredSixtyEightFJ_4449030959
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 8648524669571609) ^ 4324262334785804 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 8648524669571609) ^ 35592247672 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 8648524669571609) ^ 1943912 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_9992031134077379 : Nat.Prime 9992031134077379 := by
  apply lucas_primality 9992031134077379 (2 : ZMod 9992031134077379)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (17627, 1), (25339, 1), (360823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (17627, 1), (25339, 1), (360823, 1)] : List FactorBlock).map factorBlockValue).prod) = 9992031134077379 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_31
      · exact prime_oneHundredSixtyEightFJ_17627
      · exact prime_oneHundredSixtyEightFJ_25339
      · exact prime_oneHundredSixtyEightFJ_360823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9992031134077379) ^ 4996015567038689 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 9992031134077379) ^ 322323584970238 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 9992031134077379) ^ 566859427814 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 9992031134077379) ^ 394334075302 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 9992031134077379) ^ 27692334286 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_10274071785470159 : Nat.Prime 10274071785470159 := by
  apply lucas_primality 10274071785470159 (7 : ZMod 10274071785470159)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (512593, 1), (10021666103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (512593, 1), (10021666103, 1)] : List FactorBlock).map factorBlockValue).prod) = 10274071785470159 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_512593
      · exact prime_oneHundredSixtyEightFJ_10021666103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 10274071785470159) ^ 5137035892735079 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (7 : ZMod 10274071785470159) ^ 20043332206 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (7 : ZMod 10274071785470159) ^ 1025186 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_10402226321133749 : Nat.Prime 10402226321133749 := by
  apply lucas_primality 10402226321133749 (2 : ZMod 10402226321133749)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (31, 1), (4934642467331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (31, 1), (4934642467331, 1)] : List FactorBlock).map factorBlockValue).prod) = 10402226321133749 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_17
      · exact prime_oneHundredSixtyEightFJ_31
      · exact prime_oneHundredSixtyEightFJ_4934642467331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 10402226321133749) ^ 5201113160566874 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 10402226321133749) ^ 611895665949044 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 10402226321133749) ^ 335555687778508 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 10402226321133749) ^ 2108 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_10702957282677991 : Nat.Prime 10702957282677991 := by
  apply lucas_primality 10702957282677991 (15 : ZMod 10702957282677991)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (5, 1), (11, 1), (17, 1), (59, 1), (1427, 1), (839269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (5, 1), (11, 1), (17, 1), (59, 1), (1427, 1), (839269, 1)] : List FactorBlock).map factorBlockValue).prod) = 10702957282677991 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_5
      · exact prime_oneHundredSixtyEightFJ_11
      · exact prime_oneHundredSixtyEightFJ_17
      · exact prime_oneHundredSixtyEightFJ_59
      · exact prime_oneHundredSixtyEightFJ_1427
      · exact prime_oneHundredSixtyEightFJ_839269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 10702957282677991) ^ 5351478641338995 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (15 : ZMod 10702957282677991) ^ 3567652427559330 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (15 : ZMod 10702957282677991) ^ 2140591456535598 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (15 : ZMod 10702957282677991) ^ 972996116607090 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (15 : ZMod 10702957282677991) ^ 629585722510470 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (15 : ZMod 10702957282677991) ^ 181406055638610 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (15 : ZMod 10702957282677991) ^ 7500320450370 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (15 : ZMod 10702957282677991) ^ 12752713710 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_15745880390038507 : Nat.Prime 15745880390038507 := by
  apply lucas_primality 15745880390038507 (3 : ZMod 15745880390038507)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (109, 1), (863, 1), (9299447551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (109, 1), (863, 1), (9299447551, 1)] : List FactorBlock).map factorBlockValue).prod) = 15745880390038507 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_109
      · exact prime_oneHundredSixtyEightFJ_863
      · exact prime_oneHundredSixtyEightFJ_9299447551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 15745880390038507) ^ 7872940195019253 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 15745880390038507) ^ 5248626796679502 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 15745880390038507) ^ 144457618257234 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 15745880390038507) ^ 18245516095062 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 15745880390038507) ^ 1693206 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_16695774487261171 : Nat.Prime 16695774487261171 := by
  apply lucas_primality 16695774487261171 (3 : ZMod 16695774487261171)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (7, 1), (97, 1), (167, 1), (545326447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (7, 1), (97, 1), (167, 1), (545326447, 1)] : List FactorBlock).map factorBlockValue).prod) = 16695774487261171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_5
      · exact prime_oneHundredSixtyEightFJ_7
      · exact prime_oneHundredSixtyEightFJ_97
      · exact prime_oneHundredSixtyEightFJ_167
      · exact prime_oneHundredSixtyEightFJ_545326447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 16695774487261171) ^ 8347887243630585 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 16695774487261171) ^ 5565258162420390 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 16695774487261171) ^ 3339154897452234 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 16695774487261171) ^ 2385110641037310 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 16695774487261171) ^ 172121386466610 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 16695774487261171) ^ 99974697528510 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 16695774487261171) ^ 30616110 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_18379229417192999 : Nat.Prime 18379229417192999 := by
  apply lucas_primality 18379229417192999 (11 : ZMod 18379229417192999)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (197, 1), (27799, 1), (1678038433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (197, 1), (27799, 1), (1678038433, 1)] : List FactorBlock).map factorBlockValue).prod) = 18379229417192999 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_197
      · exact prime_oneHundredSixtyEightFJ_27799
      · exact prime_oneHundredSixtyEightFJ_1678038433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 18379229417192999) ^ 9189614708596499 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (11 : ZMod 18379229417192999) ^ 93295580797934 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (11 : ZMod 18379229417192999) ^ 661147142602 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (11 : ZMod 18379229417192999) ^ 10952806 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_24281067873010409 : Nat.Prime 24281067873010409 := by
  apply lucas_primality 24281067873010409 (3 : ZMod 24281067873010409)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (53, 1), (103, 1), (189859, 1), (2928421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (53, 1), (103, 1), (189859, 1), (2928421, 1)] : List FactorBlock).map factorBlockValue).prod) = 24281067873010409 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_53
      · exact prime_oneHundredSixtyEightFJ_103
      · exact prime_oneHundredSixtyEightFJ_189859
      · exact prime_oneHundredSixtyEightFJ_2928421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 24281067873010409) ^ 12140533936505204 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 24281067873010409) ^ 458133356094536 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 24281067873010409) ^ 235738523038936 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 24281067873010409) ^ 127890001912 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 24281067873010409) ^ 8291522248 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_26312157423034289 : Nat.Prime 26312157423034289 := by
  apply lucas_primality 26312157423034289 (3 : ZMod 26312157423034289)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (13, 2), (47, 1), (139, 1), (157, 1), (9487187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (13, 2), (47, 1), (139, 1), (157, 1), (9487187, 1)] : List FactorBlock).map factorBlockValue).prod) = 26312157423034289 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_13
      · exact prime_oneHundredSixtyEightFJ_47
      · exact prime_oneHundredSixtyEightFJ_139
      · exact prime_oneHundredSixtyEightFJ_157
      · exact prime_oneHundredSixtyEightFJ_9487187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 26312157423034289) ^ 13156078711517144 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 26312157423034289) ^ 2024012109464176 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 26312157423034289) ^ 559833136660304 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 26312157423034289) ^ 189296096568592 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 26312157423034289) ^ 167593359382384 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 26312157423034289) ^ 2773441424 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_29580241950103007 : Nat.Prime 29580241950103007 := by
  apply lucas_primality 29580241950103007 (5 : ZMod 29580241950103007)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (479, 1), (91541, 1), (337303277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (479, 1), (91541, 1), (337303277, 1)] : List FactorBlock).map factorBlockValue).prod) = 29580241950103007 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_479
      · exact prime_oneHundredSixtyEightFJ_91541
      · exact prime_oneHundredSixtyEightFJ_337303277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 29580241950103007) ^ 14790120975051503 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 29580241950103007) ^ 61754158559714 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 29580241950103007) ^ 323136539366 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 29580241950103007) ^ 87696278 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_33894984439465493 : Nat.Prime 33894984439465493 := by
  apply lucas_primality 33894984439465493 (2 : ZMod 33894984439465493)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (67, 1), (673, 1), (26846491729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (67, 1), (673, 1), (26846491729, 1)] : List FactorBlock).map factorBlockValue).prod) = 33894984439465493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_7
      · exact prime_oneHundredSixtyEightFJ_67
      · exact prime_oneHundredSixtyEightFJ_673
      · exact prime_oneHundredSixtyEightFJ_26846491729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 33894984439465493) ^ 16947492219732746 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 33894984439465493) ^ 4842140634209356 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 33894984439465493) ^ 505895290141276 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 33894984439465493) ^ 50364018483604 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 33894984439465493) ^ 1262548 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_35411224683593039 : Nat.Prime 35411224683593039 := by
  apply lucas_primality 35411224683593039 (13 : ZMod 35411224683593039)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (2131, 1), (2179, 1), (544718633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (2131, 1), (2179, 1), (544718633, 1)] : List FactorBlock).map factorBlockValue).prod) = 35411224683593039 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_7
      · exact prime_oneHundredSixtyEightFJ_2131
      · exact prime_oneHundredSixtyEightFJ_2179
      · exact prime_oneHundredSixtyEightFJ_544718633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 35411224683593039) ^ 17705612341796519 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (13 : ZMod 35411224683593039) ^ 5058746383370434 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (13 : ZMod 35411224683593039) ^ 16617186618298 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (13 : ZMod 35411224683593039) ^ 16251135696922 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (13 : ZMod 35411224683593039) ^ 65008286 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_37051420944511243 : Nat.Prime 37051420944511243 := by
  apply lucas_primality 37051420944511243 (3 : ZMod 37051420944511243)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (131, 1), (170603, 1), (92103133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (131, 1), (170603, 1), (92103133, 1)] : List FactorBlock).map factorBlockValue).prod) = 37051420944511243 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_131
      · exact prime_oneHundredSixtyEightFJ_170603
      · exact prime_oneHundredSixtyEightFJ_92103133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 37051420944511243) ^ 18525710472255621 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 37051420944511243) ^ 12350473648170414 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 37051420944511243) ^ 282835274385582 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 37051420944511243) ^ 217179187614 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 37051420944511243) ^ 402281874 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_53241274286720537 : Nat.Prime 53241274286720537 := by
  apply lucas_primality 53241274286720537 (3 : ZMod 53241274286720537)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (145829, 1), (45636734023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (145829, 1), (45636734023, 1)] : List FactorBlock).map factorBlockValue).prod) = 53241274286720537 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_145829
      · exact prime_oneHundredSixtyEightFJ_45636734023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 53241274286720537) ^ 26620637143360268 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 53241274286720537) ^ 365093872184 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 53241274286720537) ^ 1166632 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_64217743696067947 : Nat.Prime 64217743696067947 := by
  apply lucas_primality 64217743696067947 (2 : ZMod 64217743696067947)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (10702957282677991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (10702957282677991, 1)] : List FactorBlock).map factorBlockValue).prod) = 64217743696067947 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_10702957282677991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 64217743696067947) ^ 32108871848033973 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 64217743696067947) ^ 21405914565355982 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 64217743696067947) ^ 6 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_70075919093336591 : Nat.Prime 70075919093336591 := by
  apply lucas_primality 70075919093336591 (14 : ZMod 70075919093336591)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (31, 1), (24841, 1), (1299989947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (31, 1), (24841, 1), (1299989947, 1)] : List FactorBlock).map factorBlockValue).prod) = 70075919093336591 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_5
      · exact prime_oneHundredSixtyEightFJ_7
      · exact prime_oneHundredSixtyEightFJ_31
      · exact prime_oneHundredSixtyEightFJ_24841
      · exact prime_oneHundredSixtyEightFJ_1299989947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 70075919093336591) ^ 35037959546668295 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (14 : ZMod 70075919093336591) ^ 14015183818667318 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (14 : ZMod 70075919093336591) ^ 10010845584762370 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (14 : ZMod 70075919093336591) ^ 2260513519139890 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (14 : ZMod 70075919093336591) ^ 2820978184990 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (14 : ZMod 70075919093336591) ^ 53904970 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_70112722111512029 : Nat.Prime 70112722111512029 := by
  apply lucas_primality 70112722111512029 (2 : ZMod 70112722111512029)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (41, 1), (32885892172379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (41, 1), (32885892172379, 1)] : List FactorBlock).map factorBlockValue).prod) = 70112722111512029 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_13
      · exact prime_oneHundredSixtyEightFJ_41
      · exact prime_oneHundredSixtyEightFJ_32885892172379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 70112722111512029) ^ 35056361055756014 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 70112722111512029) ^ 5393286316270156 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 70112722111512029) ^ 1710066392963708 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 70112722111512029) ^ 2132 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_141258197699135131 : Nat.Prime 141258197699135131 := by
  apply lucas_primality 141258197699135131 (3 : ZMod 141258197699135131)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (198127, 1), (23765597773, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (198127, 1), (23765597773, 1)] : List FactorBlock).map factorBlockValue).prod) = 141258197699135131 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_5
      · exact prime_oneHundredSixtyEightFJ_198127
      · exact prime_oneHundredSixtyEightFJ_23765597773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 141258197699135131) ^ 70629098849567565 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 141258197699135131) ^ 47086065899711710 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 141258197699135131) ^ 28251639539827026 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 141258197699135131) ^ 712967933190 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 141258197699135131) ^ 5943810 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_182805221679518773 : Nat.Prime 182805221679518773 := by
  apply lucas_primality 182805221679518773 (2 : ZMod 182805221679518773)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (33023, 1), (48491, 1), (3171089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (33023, 1), (48491, 1), (3171089, 1)] : List FactorBlock).map factorBlockValue).prod) = 182805221679518773 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_33023
      · exact prime_oneHundredSixtyEightFJ_48491
      · exact prime_oneHundredSixtyEightFJ_3171089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 182805221679518773) ^ 91402610839759386 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 182805221679518773) ^ 60935073893172924 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 182805221679518773) ^ 5535693961164 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 182805221679518773) ^ 3769879393692 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 182805221679518773) ^ 57647458548 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_335902595973800657 : Nat.Prime 335902595973800657 := by
  apply lucas_primality 335902595973800657 (3 : ZMod 335902595973800657)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (23, 1), (53, 1), (1559, 1), (97453, 1), (113357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (23, 1), (53, 1), (1559, 1), (97453, 1), (113357, 1)] : List FactorBlock).map factorBlockValue).prod) = 335902595973800657 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_23
      · exact prime_oneHundredSixtyEightFJ_53
      · exact prime_oneHundredSixtyEightFJ_1559
      · exact prime_oneHundredSixtyEightFJ_97453
      · exact prime_oneHundredSixtyEightFJ_113357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 335902595973800657) ^ 167951297986900328 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 335902595973800657) ^ 14604460694513072 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 335902595973800657) ^ 6337784829694352 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 335902595973800657) ^ 215460292478384 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 335902595973800657) ^ 3446816372752 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 335902595973800657) ^ 2963227643408 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_403913079464067949 : Nat.Prime 403913079464067949 := by
  apply lucas_primality 403913079464067949 (2 : ZMod 403913079464067949)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (223, 1), (313, 1), (1933, 1), (249474187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (223, 1), (313, 1), (1933, 1), (249474187, 1)] : List FactorBlock).map factorBlockValue).prod) = 403913079464067949 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_223
      · exact prime_oneHundredSixtyEightFJ_313
      · exact prime_oneHundredSixtyEightFJ_1933
      · exact prime_oneHundredSixtyEightFJ_249474187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 403913079464067949) ^ 201956539732033974 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 403913079464067949) ^ 134637693154689316 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 403913079464067949) ^ 1811269414637076 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 403913079464067949) ^ 1290457122888396 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 403913079464067949) ^ 208956585340956 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 403913079464067949) ^ 1619057604 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_878478886576156007 : Nat.Prime 878478886576156007 := by
  apply lucas_primality 878478886576156007 (5 : ZMod 878478886576156007)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (131, 1), (967, 1), (3467396948839, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (131, 1), (967, 1), (3467396948839, 1)] : List FactorBlock).map factorBlockValue).prod) = 878478886576156007 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_131
      · exact prime_oneHundredSixtyEightFJ_967
      · exact prime_oneHundredSixtyEightFJ_3467396948839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 878478886576156007) ^ 439239443288078003 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 878478886576156007) ^ 6705945699054626 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 878478886576156007) ^ 908458000595818 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 878478886576156007) ^ 253354 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_1492065108799822793 : Nat.Prime 1492065108799822793 := by
  apply lucas_primality 1492065108799822793 (3 : ZMod 1492065108799822793)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (23, 1), (47981, 1), (88873, 1), (1901651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (23, 1), (47981, 1), (88873, 1), (1901651, 1)] : List FactorBlock).map factorBlockValue).prod) = 1492065108799822793 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_23
      · exact prime_oneHundredSixtyEightFJ_47981
      · exact prime_oneHundredSixtyEightFJ_88873
      · exact prime_oneHundredSixtyEightFJ_1901651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1492065108799822793) ^ 746032554399911396 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1492065108799822793) ^ 64872396034774904 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1492065108799822793) ^ 31096998995432 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1492065108799822793) ^ 16788733460104 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1492065108799822793) ^ 784615635992 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_2068648210956352507 : Nat.Prime 2068648210956352507 := by
  apply lucas_primality 2068648210956352507 (2 : ZMod 2068648210956352507)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (787, 1), (33699022756921, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (787, 1), (33699022756921, 1)] : List FactorBlock).map factorBlockValue).prod) = 2068648210956352507 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_13
      · exact prime_oneHundredSixtyEightFJ_787
      · exact prime_oneHundredSixtyEightFJ_33699022756921
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2068648210956352507) ^ 1034324105478176253 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2068648210956352507) ^ 689549403652117502 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2068648210956352507) ^ 159126785458180962 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2068648210956352507) ^ 2628523775039838 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2068648210956352507) ^ 61386 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_2220502305087140441 : Nat.Prime 2220502305087140441 := by
  apply lucas_primality 2220502305087140441 (3 : ZMod 2220502305087140441)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (101, 1), (191, 1), (48017, 1), (59929613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (101, 1), (191, 1), (48017, 1), (59929613, 1)] : List FactorBlock).map factorBlockValue).prod) = 2220502305087140441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_5
      · exact prime_oneHundredSixtyEightFJ_101
      · exact prime_oneHundredSixtyEightFJ_191
      · exact prime_oneHundredSixtyEightFJ_48017
      · exact prime_oneHundredSixtyEightFJ_59929613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2220502305087140441) ^ 1110251152543570220 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 444100461017428088 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 21985171337496440 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 11625666518780840 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 46244086575320 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 37051837880 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_3503795954666829551 : Nat.Prime 3503795954666829551 := by
  apply lucas_primality 3503795954666829551 (13 : ZMod 3503795954666829551)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (70075919093336591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (70075919093336591, 1)] : List FactorBlock).map factorBlockValue).prod) = 3503795954666829551 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_5
      · exact prime_oneHundredSixtyEightFJ_70075919093336591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 3503795954666829551) ^ 1751897977333414775 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (13 : ZMod 3503795954666829551) ^ 700759190933365910 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (13 : ZMod 3503795954666829551) ^ 50 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_3873419681044591673 : Nat.Prime 3873419681044591673 := by
  apply lucas_primality 3873419681044591673 (3 : ZMod 3873419681044591673)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (29, 1), (16695774487261171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (29, 1), (16695774487261171, 1)] : List FactorBlock).map factorBlockValue).prod) = 3873419681044591673 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_29
      · exact prime_oneHundredSixtyEightFJ_16695774487261171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 3873419681044591673) ^ 1936709840522295836 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 3873419681044591673) ^ 133566195898089368 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 3873419681044591673) ^ 232 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_4546615613828032933 : Nat.Prime 4546615613828032933 := by
  apply lucas_primality 4546615613828032933 (5 : ZMod 4546615613828032933)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (1036307, 1), (33237310643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (1036307, 1), (33237310643, 1)] : List FactorBlock).map factorBlockValue).prod) = 4546615613828032933 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_11
      · exact prime_oneHundredSixtyEightFJ_1036307
      · exact prime_oneHundredSixtyEightFJ_33237310643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 4546615613828032933) ^ 2273307806914016466 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 4546615613828032933) ^ 1515538537942677644 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 4546615613828032933) ^ 413328692166184812 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 4546615613828032933) ^ 4387325004876 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 4546615613828032933) ^ 136792524 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_4873991417970856459 : Nat.Prime 4873991417970856459 := by
  apply lucas_primality 4873991417970856459 (2 : ZMod 4873991417970856459)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (557, 1), (1458405570906899, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (557, 1), (1458405570906899, 1)] : List FactorBlock).map factorBlockValue).prod) = 4873991417970856459 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_557
      · exact prime_oneHundredSixtyEightFJ_1458405570906899
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4873991417970856459) ^ 2436995708985428229 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4873991417970856459) ^ 1624663805990285486 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4873991417970856459) ^ 8750433425441394 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4873991417970856459) ^ 3342 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_9562794600184569431 : Nat.Prime 9562794600184569431 := by
  apply lucas_primality 9562794600184569431 (7 : ZMod 9562794600184569431)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (113, 1), (379, 1), (6691, 1), (3337153199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (113, 1), (379, 1), (6691, 1), (3337153199, 1)] : List FactorBlock).map factorBlockValue).prod) = 9562794600184569431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_5
      · exact prime_oneHundredSixtyEightFJ_113
      · exact prime_oneHundredSixtyEightFJ_379
      · exact prime_oneHundredSixtyEightFJ_6691
      · exact prime_oneHundredSixtyEightFJ_3337153199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 9562794600184569431) ^ 4781397300092284715 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (7 : ZMod 9562794600184569431) ^ 1912558920036913886 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (7 : ZMod 9562794600184569431) ^ 84626500886589110 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (7 : ZMod 9562794600184569431) ^ 25231648021595170 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (7 : ZMod 9562794600184569431) ^ 1429202600535730 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (7 : ZMod 9562794600184569431) ^ 2865554570 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_10006176146377349017 : Nat.Prime 10006176146377349017 := by
  apply lucas_primality 10006176146377349017 (10 : ZMod 10006176146377349017)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (13, 1), (3563453043581677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (13, 1), (3563453043581677, 1)] : List FactorBlock).map factorBlockValue).prod) = 10006176146377349017 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_13
      · exact prime_oneHundredSixtyEightFJ_3563453043581677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 10006176146377349017) ^ 5003088073188674508 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (10 : ZMod 10006176146377349017) ^ 3335392048792449672 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (10 : ZMod 10006176146377349017) ^ 769705857413642232 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (10 : ZMod 10006176146377349017) ^ 2808 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_13311937837557174217 : Nat.Prime 13311937837557174217 := by
  apply lucas_primality 13311937837557174217 (5 : ZMod 13311937837557174217)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (4253, 1), (130417135331503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (4253, 1), (130417135331503, 1)] : List FactorBlock).map factorBlockValue).prod) = 13311937837557174217 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_4253
      · exact prime_oneHundredSixtyEightFJ_130417135331503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 13311937837557174217) ^ 6655968918778587108 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 13311937837557174217) ^ 4437312612519058072 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 13311937837557174217) ^ 3130011247956072 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 13311937837557174217) ^ 102072 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_13380221384344769281 : Nat.Prime 13380221384344769281 := by
  apply lucas_primality 13380221384344769281 (19 : ZMod 13380221384344769281)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 1), (5, 1), (31, 1), (397, 1), (283126078831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 1), (5, 1), (31, 1), (397, 1), (283126078831, 1)] : List FactorBlock).map factorBlockValue).prod) = 13380221384344769281 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_5
      · exact prime_oneHundredSixtyEightFJ_31
      · exact prime_oneHundredSixtyEightFJ_397
      · exact prime_oneHundredSixtyEightFJ_283126078831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 13380221384344769281) ^ 6690110692172384640 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (19 : ZMod 13380221384344769281) ^ 4460073794781589760 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (19 : ZMod 13380221384344769281) ^ 2676044276868953856 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (19 : ZMod 13380221384344769281) ^ 431620044656282880 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (19 : ZMod 13380221384344769281) ^ 33703328424042240 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (19 : ZMod 13380221384344769281) ^ 47258880 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_17266229799685710913 : Nat.Prime 17266229799685710913 := by
  apply lucas_primality 17266229799685710913 (15 : ZMod 17266229799685710913)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (9992031134077379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (9992031134077379, 1)] : List FactorBlock).map factorBlockValue).prod) = 17266229799685710913 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_9992031134077379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (15 : ZMod 17266229799685710913) ^ 8633114899842855456 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (15 : ZMod 17266229799685710913) ^ 5755409933228570304 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (15 : ZMod 17266229799685710913) ^ 1728 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_35235616776614517997 : Nat.Prime 35235616776614517997 := by
  apply lucas_primality 35235616776614517997 (5 : ZMod 35235616776614517997)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (15173, 1), (64507159604807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (15173, 1), (64507159604807, 1)] : List FactorBlock).map factorBlockValue).prod) = 35235616776614517997 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_15173
      · exact prime_oneHundredSixtyEightFJ_64507159604807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 35235616776614517997) ^ 17617808388307258998 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 35235616776614517997) ^ 11745205592204839332 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 35235616776614517997) ^ 2322257745773052 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 35235616776614517997) ^ 546228 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_40397650260468665189 : Nat.Prime 40397650260468665189 := by
  apply lucas_primality 40397650260468665189 (2 : ZMod 40397650260468665189)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (983, 1), (10274071785470159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (983, 1), (10274071785470159, 1)] : List FactorBlock).map factorBlockValue).prod) = 40397650260468665189 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_983
      · exact prime_oneHundredSixtyEightFJ_10274071785470159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 40397650260468665189) ^ 20198825130234332594 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 40397650260468665189) ^ 41096287141880636 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 40397650260468665189) ^ 3932 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_58870400848523288429 : Nat.Prime 58870400848523288429 := by
  apply lucas_primality 58870400848523288429 (2 : ZMod 58870400848523288429)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1217, 1), (106861, 1), (113168924711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1217, 1), (106861, 1), (113168924711, 1)] : List FactorBlock).map factorBlockValue).prod) = 58870400848523288429 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_1217
      · exact prime_oneHundredSixtyEightFJ_106861
      · exact prime_oneHundredSixtyEightFJ_113168924711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 58870400848523288429) ^ 29435200424261644214 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 58870400848523288429) ^ 48373377854168684 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 58870400848523288429) ^ 550906325493148 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 58870400848523288429) ^ 520199348 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_66344737026778446149 : Nat.Prime 66344737026778446149 := by
  apply lucas_primality 66344737026778446149 (3 : ZMod 66344737026778446149)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (319053557, 1), (4725961831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (319053557, 1), (4725961831, 1)] : List FactorBlock).map factorBlockValue).prod) = 66344737026778446149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_11
      · exact prime_oneHundredSixtyEightFJ_319053557
      · exact prime_oneHundredSixtyEightFJ_4725961831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 66344737026778446149) ^ 33172368513389223074 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 66344737026778446149) ^ 6031339729707131468 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 66344737026778446149) ^ 207942320564 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 66344737026778446149) ^ 14038356508 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_76364612785197585103 : Nat.Prime 76364612785197585103 := by
  apply lucas_primality 76364612785197585103 (5 : ZMod 76364612785197585103)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (89, 1), (6217604037225011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (89, 1), (6217604037225011, 1)] : List FactorBlock).map factorBlockValue).prod) = 76364612785197585103 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_23
      · exact prime_oneHundredSixtyEightFJ_89
      · exact prime_oneHundredSixtyEightFJ_6217604037225011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 76364612785197585103) ^ 38182306392598792551 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 76364612785197585103) ^ 25454870928399195034 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 76364612785197585103) ^ 3320200555878155874 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 76364612785197585103) ^ 858029357137051518 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 76364612785197585103) ^ 12282 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_87394902519107620253 : Nat.Prime 87394902519107620253 := by
  apply lucas_primality 87394902519107620253 (2 : ZMod 87394902519107620253)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (617, 1), (35411224683593039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (617, 1), (35411224683593039, 1)] : List FactorBlock).map factorBlockValue).prod) = 87394902519107620253 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_617
      · exact prime_oneHundredSixtyEightFJ_35411224683593039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 87394902519107620253) ^ 43697451259553810126 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 87394902519107620253) ^ 141644898734372156 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 87394902519107620253) ^ 2468 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_94268036096709849533 : Nat.Prime 94268036096709849533 := by
  apply lucas_primality 94268036096709849533 (2 : ZMod 94268036096709849533)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (23, 1), (263, 1), (16339, 1), (14026408709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (23, 1), (263, 1), (16339, 1), (14026408709, 1)] : List FactorBlock).map factorBlockValue).prod) = 94268036096709849533 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_17
      · exact prime_oneHundredSixtyEightFJ_23
      · exact prime_oneHundredSixtyEightFJ_263
      · exact prime_oneHundredSixtyEightFJ_16339
      · exact prime_oneHundredSixtyEightFJ_14026408709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 94268036096709849533) ^ 47134018048354924766 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 94268036096709849533) ^ 5545178593924108796 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 94268036096709849533) ^ 4098610265074341284 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 94268036096709849533) ^ 358433597325892964 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 94268036096709849533) ^ 5769510747090388 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 94268036096709849533) ^ 6720753548 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_237411658455564283589 : Nat.Prime 237411658455564283589 := by
  apply lucas_primality 237411658455564283589 (2 : ZMod 237411658455564283589)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (73, 1), (79, 1), (605401060944023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (73, 1), (79, 1), (605401060944023, 1)] : List FactorBlock).map factorBlockValue).prod) = 237411658455564283589 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_17
      · exact prime_oneHundredSixtyEightFJ_73
      · exact prime_oneHundredSixtyEightFJ_79
      · exact prime_oneHundredSixtyEightFJ_605401060944023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 237411658455564283589) ^ 118705829227782141794 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 237411658455564283589) ^ 13965391673856722564 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 237411658455564283589) ^ 3252214499391291556 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 237411658455564283589) ^ 3005210866526130172 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 237411658455564283589) ^ 392156 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_256223811061086791179 : Nat.Prime 256223811061086791179 := by
  apply lucas_primality 256223811061086791179 (2 : ZMod 256223811061086791179)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (6863, 1), (366020420757353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (6863, 1), (366020420757353, 1)] : List FactorBlock).map factorBlockValue).prod) = 256223811061086791179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_17
      · exact prime_oneHundredSixtyEightFJ_6863
      · exact prime_oneHundredSixtyEightFJ_366020420757353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 256223811061086791179) ^ 128111905530543395589 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 85407937020362263726 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 15071988885946281834 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 37334082917250006 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 700026 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_377942286057032472047 : Nat.Prime 377942286057032472047 := by
  apply lucas_primality 377942286057032472047 (5 : ZMod 377942286057032472047)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (113, 1), (199, 1), (1592737, 1), (5276183617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (113, 1), (199, 1), (1592737, 1), (5276183617, 1)] : List FactorBlock).map factorBlockValue).prod) = 377942286057032472047 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_113
      · exact prime_oneHundredSixtyEightFJ_199
      · exact prime_oneHundredSixtyEightFJ_1592737
      · exact prime_oneHundredSixtyEightFJ_5276183617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 377942286057032472047) ^ 188971143028516236023 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 377942286057032472047) ^ 3344622000504712142 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 377942286057032472047) ^ 1899207467623278754 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 377942286057032472047) ^ 237291081990958 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 377942286057032472047) ^ 71631753838 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_436475098927491161569 : Nat.Prime 436475098927491161569 := by
  apply lucas_primality 436475098927491161569 (7 : ZMod 436475098927491161569)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (4546615613828032933, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (4546615613828032933, 1)] : List FactorBlock).map factorBlockValue).prod) = 436475098927491161569 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_4546615613828032933
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 436475098927491161569) ^ 218237549463745580784 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (7 : ZMod 436475098927491161569) ^ 145491699642497053856 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (7 : ZMod 436475098927491161569) ^ 96 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_575284891189512700303 : Nat.Prime 575284891189512700303 := by
  apply lucas_primality 575284891189512700303 (5 : ZMod 575284891189512700303)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1709, 1), (12823, 1), (4375221181031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1709, 1), (12823, 1), (4375221181031, 1)] : List FactorBlock).map factorBlockValue).prod) = 575284891189512700303 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_1709
      · exact prime_oneHundredSixtyEightFJ_12823
      · exact prime_oneHundredSixtyEightFJ_4375221181031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 575284891189512700303) ^ 287642445594756350151 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 575284891189512700303) ^ 191761630396504233434 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 575284891189512700303) ^ 336620767226163078 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 575284891189512700303) ^ 44863517990291874 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 575284891189512700303) ^ 131487042 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_719951796451679731129 : Nat.Prime 719951796451679731129 := by
  apply lucas_primality 719951796451679731129 (17 : ZMod 719951796451679731129)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (7, 1), (367, 1), (1297434865222957, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (7, 1), (367, 1), (1297434865222957, 1)] : List FactorBlock).map factorBlockValue).prod) = 719951796451679731129 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_7
      · exact prime_oneHundredSixtyEightFJ_367
      · exact prime_oneHundredSixtyEightFJ_1297434865222957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 719951796451679731129) ^ 359975898225839865564 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (17 : ZMod 719951796451679731129) ^ 239983932150559910376 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (17 : ZMod 719951796451679731129) ^ 102850256635954247304 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (17 : ZMod 719951796451679731129) ^ 1961721516217110984 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (17 : ZMod 719951796451679731129) ^ 554904 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_2248002179148066535807 : Nat.Prime 2248002179148066535807 := by
  apply lucas_primality 2248002179148066535807 (3 : ZMod 2248002179148066535807)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (41, 1), (53, 1), (7717, 1), (720734907931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (41, 1), (53, 1), (7717, 1), (720734907931, 1)] : List FactorBlock).map factorBlockValue).prod) = 2248002179148066535807 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_31
      · exact prime_oneHundredSixtyEightFJ_41
      · exact prime_oneHundredSixtyEightFJ_53
      · exact prime_oneHundredSixtyEightFJ_7717
      · exact prime_oneHundredSixtyEightFJ_720734907931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2248002179148066535807) ^ 1124001089574033267903 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2248002179148066535807) ^ 749334059716022178602 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2248002179148066535807) ^ 72516199327356985026 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2248002179148066535807) ^ 54829321442635769166 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2248002179148066535807) ^ 42415135455623896902 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2248002179148066535807) ^ 291305193617735718 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 2248002179148066535807) ^ 3119041626 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_3074685732733041494149 : Nat.Prime 3074685732733041494149 := by
  apply lucas_primality 3074685732733041494149 (2 : ZMod 3074685732733041494149)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (256223811061086791179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (256223811061086791179, 1)] : List FactorBlock).map factorBlockValue).prod) = 3074685732733041494149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_256223811061086791179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3074685732733041494149) ^ 1537342866366520747074 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 3074685732733041494149) ^ 1024895244244347164716 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 3074685732733041494149) ^ 12 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_3970959864830274425357 : Nat.Prime 3970959864830274425357 := by
  apply lucas_primality 3970959864830274425357 (2 : ZMod 3970959864830274425357)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (76364612785197585103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (76364612785197585103, 1)] : List FactorBlock).map factorBlockValue).prod) = 3970959864830274425357 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_13
      · exact prime_oneHundredSixtyEightFJ_76364612785197585103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3970959864830274425357) ^ 1985479932415137212678 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 3970959864830274425357) ^ 305458451140790340412 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 3970959864830274425357) ^ 52 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_9680897125634440093519 : Nat.Prime 9680897125634440093519 := by
  apply lucas_primality 9680897125634440093519 (3 : ZMod 9680897125634440093519)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (17, 1), (277, 1), (2131, 1), (5711, 1), (2165692049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (17, 1), (277, 1), (2131, 1), (5711, 1), (2165692049, 1)] : List FactorBlock).map factorBlockValue).prod) = 9680897125634440093519 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_13
      · exact prime_oneHundredSixtyEightFJ_17
      · exact prime_oneHundredSixtyEightFJ_277
      · exact prime_oneHundredSixtyEightFJ_2131
      · exact prime_oneHundredSixtyEightFJ_5711
      · exact prime_oneHundredSixtyEightFJ_2165692049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 9680897125634440093519) ^ 4840448562817220046759 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 9680897125634440093519) ^ 3226965708544813364506 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 9680897125634440093519) ^ 744684394279572314886 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 9680897125634440093519) ^ 569464536802025887854 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 9680897125634440093519) ^ 34949087096153213334 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 9680897125634440093519) ^ 4542889312827048378 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 9680897125634440093519) ^ 1695131697712211538 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 9680897125634440093519) ^ 4470117129582 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_9803875754057824351433 : Nat.Prime 9803875754057824351433 := by
  apply lucas_primality 9803875754057824351433 (3 : ZMod 9803875754057824351433)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (94268036096709849533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (94268036096709849533, 1)] : List FactorBlock).map factorBlockValue).prod) = 9803875754057824351433 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_13
      · exact prime_oneHundredSixtyEightFJ_94268036096709849533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 9803875754057824351433) ^ 4901937877028912175716 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 9803875754057824351433) ^ 754144288773678796264 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 9803875754057824351433) ^ 104 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_14172787871626434216079 : Nat.Prime 14172787871626434216079 := by
  apply lucas_primality 14172787871626434216079 (6 : ZMod 14172787871626434216079)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (19, 1), (2971, 1), (17257, 1), (317189, 1), (694979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (19, 1), (2971, 1), (17257, 1), (317189, 1), (694979, 1)] : List FactorBlock).map factorBlockValue).prod) = 14172787871626434216079 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_11
      · exact prime_oneHundredSixtyEightFJ_19
      · exact prime_oneHundredSixtyEightFJ_2971
      · exact prime_oneHundredSixtyEightFJ_17257
      · exact prime_oneHundredSixtyEightFJ_317189
      · exact prime_oneHundredSixtyEightFJ_694979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 14172787871626434216079) ^ 7086393935813217108039 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (6 : ZMod 14172787871626434216079) ^ 4724262623875478072026 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (6 : ZMod 14172787871626434216079) ^ 1288435261056948565098 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (6 : ZMod 14172787871626434216079) ^ 745936203769812327162 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (6 : ZMod 14172787871626434216079) ^ 4770376261065780618 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (6 : ZMod 14172787871626434216079) ^ 821277619031490654 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (6 : ZMod 14172787871626434216079) ^ 44682469668325302 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (6 : ZMod 14172787871626434216079) ^ 20393116729608282 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_34826819892562670796919 : Nat.Prime 34826819892562670796919 := by
  apply lucas_primality 34826819892562670796919 (3 : ZMod 34826819892562670796919)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (503, 1), (21247, 1), (181040488126411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (503, 1), (21247, 1), (181040488126411, 1)] : List FactorBlock).map factorBlockValue).prod) = 34826819892562670796919 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_503
      · exact prime_oneHundredSixtyEightFJ_21247
      · exact prime_oneHundredSixtyEightFJ_181040488126411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 34826819892562670796919) ^ 17413409946281335398459 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 34826819892562670796919) ^ 11608939964187556932306 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 34826819892562670796919) ^ 69238210521993381306 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 34826819892562670796919) ^ 1639140579496525194 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 34826819892562670796919) ^ 192370338 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_39195807816488567672161 : Nat.Prime 39195807816488567672161 := by
  apply lucas_primality 39195807816488567672161 (11 : ZMod 39195807816488567672161)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (5, 1), (59, 1), (367457, 1), (1255505416853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (5, 1), (59, 1), (367457, 1), (1255505416853, 1)] : List FactorBlock).map factorBlockValue).prod) = 39195807816488567672161 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_5
      · exact prime_oneHundredSixtyEightFJ_59
      · exact prime_oneHundredSixtyEightFJ_367457
      · exact prime_oneHundredSixtyEightFJ_1255505416853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 39195807816488567672161) ^ 19597903908244283836080 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (11 : ZMod 39195807816488567672161) ^ 13065269272162855890720 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (11 : ZMod 39195807816488567672161) ^ 7839161563297713534432 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (11 : ZMod 39195807816488567672161) ^ 664335725703196062240 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (11 : ZMod 39195807816488567672161) ^ 106667740215830880 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (11 : ZMod 39195807816488567672161) ^ 31219146720 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_47886543588161587791203 : Nat.Prime 47886543588161587791203 := by
  apply lucas_primality 47886543588161587791203 (2 : ZMod 47886543588161587791203)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (14201963, 1), (240844691621461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (14201963, 1), (240844691621461, 1)] : List FactorBlock).map factorBlockValue).prod) = 47886543588161587791203 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_7
      · exact prime_oneHundredSixtyEightFJ_14201963
      · exact prime_oneHundredSixtyEightFJ_240844691621461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 47886543588161587791203) ^ 23943271794080793895601 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 47886543588161587791203) ^ 6840934798308798255886 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 47886543588161587791203) ^ 3371825682700454 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 47886543588161587791203) ^ 198827482 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_94954930555009359595661 : Nat.Prime 94954930555009359595661 := by
  apply lucas_primality 94954930555009359595661 (2 : ZMod 94954930555009359595661)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (1621, 1), (3623, 1), (808418374374301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (1621, 1), (3623, 1), (808418374374301, 1)] : List FactorBlock).map factorBlockValue).prod) = 94954930555009359595661 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_5
      · exact prime_oneHundredSixtyEightFJ_1621
      · exact prime_oneHundredSixtyEightFJ_3623
      · exact prime_oneHundredSixtyEightFJ_808418374374301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 94954930555009359595661) ^ 47477465277504679797830 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 94954930555009359595661) ^ 18990986111001871919132 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 94954930555009359595661) ^ 58577995407161850460 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 94954930555009359595661) ^ 26208923697214838420 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 94954930555009359595661) ^ 117457660 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_121523297187681894329819 : Nat.Prime 121523297187681894329819 := by
  apply lucas_primality 121523297187681894329819 (2 : ZMod 121523297187681894329819)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (47, 1), (761, 1), (1627, 1), (4759, 1), (31343373377, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (47, 1), (761, 1), (1627, 1), (4759, 1), (31343373377, 1)] : List FactorBlock).map factorBlockValue).prod) = 121523297187681894329819 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_7
      · exact prime_oneHundredSixtyEightFJ_47
      · exact prime_oneHundredSixtyEightFJ_761
      · exact prime_oneHundredSixtyEightFJ_1627
      · exact prime_oneHundredSixtyEightFJ_4759
      · exact prime_oneHundredSixtyEightFJ_31343373377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 121523297187681894329819) ^ 60761648593840947164909 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 121523297187681894329819) ^ 17360471026811699189974 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 121523297187681894329819) ^ 2585602067823019028294 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 121523297187681894329819) ^ 159688958196691056938 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 121523297187681894329819) ^ 74691639328630543534 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 121523297187681894329819) ^ 25535469045530971702 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 121523297187681894329819) ^ 3877160755034 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_555151061633957839279969 : Nat.Prime 555151061633957839279969 := by
  apply lucas_primality 555151061633957839279969 (7 : ZMod 555151061633957839279969)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (103, 1), (139, 1), (403913079464067949, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (103, 1), (139, 1), (403913079464067949, 1)] : List FactorBlock).map factorBlockValue).prod) = 555151061633957839279969 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_103
      · exact prime_oneHundredSixtyEightFJ_139
      · exact prime_oneHundredSixtyEightFJ_403913079464067949
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 555151061633957839279969) ^ 277575530816978919639984 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (7 : ZMod 555151061633957839279969) ^ 185050353877985946426656 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (7 : ZMod 555151061633957839279969) ^ 5389816132368522711456 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (7 : ZMod 555151061633957839279969) ^ 3993892529740703879712 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (7 : ZMod 555151061633957839279969) ^ 1374432 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_661273722384977303384623 : Nat.Prime 661273722384977303384623 := by
  apply lucas_primality 661273722384977303384623 (3 : ZMod 661273722384977303384623)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (17, 1), (332647531, 1), (2784189228833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (17, 1), (332647531, 1), (2784189228833, 1)] : List FactorBlock).map factorBlockValue).prod) = 661273722384977303384623 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_7
      · exact prime_oneHundredSixtyEightFJ_17
      · exact prime_oneHundredSixtyEightFJ_332647531
      · exact prime_oneHundredSixtyEightFJ_2784189228833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 661273722384977303384623) ^ 330636861192488651692311 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 661273722384977303384623) ^ 220424574128325767794874 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 661273722384977303384623) ^ 94467674626425329054946 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 661273722384977303384623) ^ 38898454257939841375566 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 661273722384977303384623) ^ 1987911109386762 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 661273722384977303384623) ^ 237510337134 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_830886129210047261927189 : Nat.Prime 830886129210047261927189 := by
  apply lucas_primality 830886129210047261927189 (2 : ZMod 830886129210047261927189)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (37, 1), (53, 1), (257, 1), (76730309, 1), (5371602329, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (37, 1), (53, 1), (257, 1), (76730309, 1), (5371602329, 1)] : List FactorBlock).map factorBlockValue).prod) = 830886129210047261927189 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_37
      · exact prime_oneHundredSixtyEightFJ_53
      · exact prime_oneHundredSixtyEightFJ_257
      · exact prime_oneHundredSixtyEightFJ_76730309
      · exact prime_oneHundredSixtyEightFJ_5371602329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 830886129210047261927189) ^ 415443064605023630963594 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 830886129210047261927189) ^ 22456381870541817889924 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 830886129210047261927189) ^ 15677096777548061545796 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 830886129210047261927189) ^ 3233019958015748100884 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 830886129210047261927189) ^ 10828656107849732 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 830886129210047261927189) ^ 154681243755572 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_878899926231809511221431 : Nat.Prime 878899926231809511221431 := by
  apply lucas_primality 878899926231809511221431 (6 : ZMod 878899926231809511221431)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 1), (797, 1), (125287, 1), (13971226936099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 1), (797, 1), (125287, 1), (13971226936099, 1)] : List FactorBlock).map factorBlockValue).prod) = 878899926231809511221431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_5
      · exact prime_oneHundredSixtyEightFJ_7
      · exact prime_oneHundredSixtyEightFJ_797
      · exact prime_oneHundredSixtyEightFJ_125287
      · exact prime_oneHundredSixtyEightFJ_13971226936099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 878899926231809511221431) ^ 439449963115904755610715 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (6 : ZMod 878899926231809511221431) ^ 292966642077269837073810 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (6 : ZMod 878899926231809511221431) ^ 175779985246361902244286 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (6 : ZMod 878899926231809511221431) ^ 125557132318829930174490 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (6 : ZMod 878899926231809511221431) ^ 1102760258760112310190 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (6 : ZMod 878899926231809511221431) ^ 7015092756884668890 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (6 : ZMod 878899926231809511221431) ^ 62907855570 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_1410068483584820052832327 : Nat.Prime 1410068483584820052832327 := by
  apply lucas_primality 1410068483584820052832327 (3 : ZMod 1410068483584820052832327)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (541, 1), (11717, 1), (4562083, 1), (8126659771, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (541, 1), (11717, 1), (4562083, 1), (8126659771, 1)] : List FactorBlock).map factorBlockValue).prod) = 1410068483584820052832327 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_541
      · exact prime_oneHundredSixtyEightFJ_11717
      · exact prime_oneHundredSixtyEightFJ_4562083
      · exact prime_oneHundredSixtyEightFJ_8126659771
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1410068483584820052832327) ^ 705034241792410026416163 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1410068483584820052832327) ^ 470022827861606684277442 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1410068483584820052832327) ^ 2606411245073604533886 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1410068483584820052832327) ^ 120343815275652475278 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1410068483584820052832327) ^ 309084355454475522 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 1410068483584820052832327) ^ 173511445454706 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_2038182006457405518952373 : Nat.Prime 2038182006457405518952373 := by
  apply lucas_primality 2038182006457405518952373 (2 : ZMod 2038182006457405518952373)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (39195807816488567672161, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (39195807816488567672161, 1)] : List FactorBlock).map factorBlockValue).prod) = 2038182006457405518952373 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_13
      · exact prime_oneHundredSixtyEightFJ_39195807816488567672161
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2038182006457405518952373) ^ 1019091003228702759476186 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2038182006457405518952373) ^ 156783231265954270688644 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2038182006457405518952373) ^ 52 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_2689225764700833597198797 : Nat.Prime 2689225764700833597198797 := by
  apply lucas_primality 2689225764700833597198797 (2 : ZMod 2689225764700833597198797)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (383, 1), (4506446297, 1), (389524068949, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (383, 1), (4506446297, 1), (389524068949, 1)] : List FactorBlock).map factorBlockValue).prod) = 2689225764700833597198797 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_383
      · exact prime_oneHundredSixtyEightFJ_4506446297
      · exact prime_oneHundredSixtyEightFJ_389524068949
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2689225764700833597198797) ^ 1344612882350416798599398 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2689225764700833597198797) ^ 7021477192430374927412 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2689225764700833597198797) ^ 596750873629868 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2689225764700833597198797) ^ 6903875727004 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_4240229634287053665981571 : Nat.Prime 4240229634287053665981571 := by
  apply lucas_primality 4240229634287053665981571 (2 : ZMod 4240229634287053665981571)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (37, 1), (43, 1), (47, 1), (431, 1), (2102497, 1), (695290307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (37, 1), (43, 1), (47, 1), (431, 1), (2102497, 1), (695290307, 1)] : List FactorBlock).map factorBlockValue).prod) = 4240229634287053665981571 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_5
      · exact prime_oneHundredSixtyEightFJ_37
      · exact prime_oneHundredSixtyEightFJ_43
      · exact prime_oneHundredSixtyEightFJ_47
      · exact prime_oneHundredSixtyEightFJ_431
      · exact prime_oneHundredSixtyEightFJ_2102497
      · exact prime_oneHundredSixtyEightFJ_695290307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4240229634287053665981571) ^ 2120114817143526832990785 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4240229634287053665981571) ^ 1413409878095684555327190 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4240229634287053665981571) ^ 848045926857410733196314 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4240229634287053665981571) ^ 114600800926677126107610 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4240229634287053665981571) ^ 98609991495047759673990 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4240229634287053665981571) ^ 90217651793341567361310 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4240229634287053665981571) ^ 9838119801130054909470 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4240229634287053665981571) ^ 2016758946284847810 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4240229634287053665981571) ^ 6098502440775510 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_4613081487580689516488033 : Nat.Prime 4613081487580689516488033 := by
  apply lucas_primality 4613081487580689516488033 (5 : ZMod 4613081487580689516488033)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (7, 1), (97, 1), (719, 1), (17207, 1), (17160791887493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (7, 1), (97, 1), (719, 1), (17207, 1), (17160791887493, 1)] : List FactorBlock).map factorBlockValue).prod) = 4613081487580689516488033 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_7
      · exact prime_oneHundredSixtyEightFJ_97
      · exact prime_oneHundredSixtyEightFJ_719
      · exact prime_oneHundredSixtyEightFJ_17207
      · exact prime_oneHundredSixtyEightFJ_17160791887493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 4613081487580689516488033) ^ 2306540743790344758244016 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 4613081487580689516488033) ^ 659011641082955645212576 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 4613081487580689516488033) ^ 47557541109079273365856 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 4613081487580689516488033) ^ 6415968689263824084128 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 4613081487580689516488033) ^ 268093304328511042976 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (5 : ZMod 4613081487580689516488033) ^ 268815187424 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_4719067607433632726410909 : Nat.Prime 4719067607433632726410909 := by
  apply lucas_primality 4719067607433632726410909 (2 : ZMod 4719067607433632726410909)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7517, 1), (63849983, 1), (819350299919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7517, 1), (63849983, 1), (819350299919, 1)] : List FactorBlock).map factorBlockValue).prod) = 4719067607433632726410909 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_7517
      · exact prime_oneHundredSixtyEightFJ_63849983
      · exact prime_oneHundredSixtyEightFJ_819350299919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4719067607433632726410909) ^ 2359533803716816363205454 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4719067607433632726410909) ^ 1573022535811210908803636 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4719067607433632726410909) ^ 627786032650476616524 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4719067607433632726410909) ^ 73908674453893476 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 4719067607433632726410909) ^ 5759523866532 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_5604425409968232726351827 : Nat.Prime 5604425409968232726351827 := by
  apply lucas_primality 5604425409968232726351827 (2 : ZMod 5604425409968232726351827)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (4871, 1), (575284891189512700303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (4871, 1), (575284891189512700303, 1)] : List FactorBlock).map factorBlockValue).prod) = 5604425409968232726351827 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_4871
      · exact prime_oneHundredSixtyEightFJ_575284891189512700303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 5604425409968232726351827) ^ 2802212704984116363175913 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 5604425409968232726351827) ^ 1150569782379025400606 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 5604425409968232726351827) ^ 9742 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_12581290715732828771895151 : Nat.Prime 12581290715732828771895151 := by
  apply lucas_primality 12581290715732828771895151 (6 : ZMod 12581290715732828771895151)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (7, 2), (179, 1), (9562794600184569431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (7, 2), (179, 1), (9562794600184569431, 1)] : List FactorBlock).map factorBlockValue).prod) = 12581290715732828771895151 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_5
      · exact prime_oneHundredSixtyEightFJ_7
      · exact prime_oneHundredSixtyEightFJ_179
      · exact prime_oneHundredSixtyEightFJ_9562794600184569431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 12581290715732828771895151) ^ 6290645357866414385947575 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (6 : ZMod 12581290715732828771895151) ^ 4193763571910942923965050 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (6 : ZMod 12581290715732828771895151) ^ 2516258143146565754379030 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (6 : ZMod 12581290715732828771895151) ^ 1797327245104689824556450 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (6 : ZMod 12581290715732828771895151) ^ 70286540311356585317850 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (6 : ZMod 12581290715732828771895151) ^ 1315650 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_68231135874020669124668069 : Nat.Prime 68231135874020669124668069 := by
  apply lucas_primality 68231135874020669124668069 (2 : ZMod 68231135874020669124668069)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (79, 1), (225781, 1), (8914481, 1), (107278344443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (79, 1), (225781, 1), (8914481, 1), (107278344443, 1)] : List FactorBlock).map factorBlockValue).prod) = 68231135874020669124668069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_79
      · exact prime_oneHundredSixtyEightFJ_225781
      · exact prime_oneHundredSixtyEightFJ_8914481
      · exact prime_oneHundredSixtyEightFJ_107278344443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 68231135874020669124668069) ^ 34115567937010334562334034 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 68231135874020669124668069) ^ 863685264228109735755292 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 68231135874020669124668069) ^ 302200521186550990228 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 68231135874020669124668069) ^ 7653966156192454628 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 68231135874020669124668069) ^ 636019657352876 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_295127543134136950701201707 : Nat.Prime 295127543134136950701201707 := by
  apply lucas_primality 295127543134136950701201707 (2 : ZMod 295127543134136950701201707)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (727, 1), (143107, 1), (734087, 1), (1932132586471, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (727, 1), (143107, 1), (734087, 1), (1932132586471, 1)] : List FactorBlock).map factorBlockValue).prod) = 295127543134136950701201707 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_727
      · exact prime_oneHundredSixtyEightFJ_143107
      · exact prime_oneHundredSixtyEightFJ_734087
      · exact prime_oneHundredSixtyEightFJ_1932132586471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 295127543134136950701201707) ^ 147563771567068475350600853 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 295127543134136950701201707) ^ 405952604035951789135078 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 295127543134136950701201707) ^ 2062285863962887564558 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 295127543134136950701201707) ^ 402033468967761247238 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 295127543134136950701201707) ^ 152747045001286 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_589379336882119192349877593 : Nat.Prime 589379336882119192349877593 := by
  apply lucas_primality 589379336882119192349877593 (3 : ZMod 589379336882119192349877593)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (31, 1), (71, 1), (383, 1), (87394902519107620253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (31, 1), (71, 1), (383, 1), (87394902519107620253, 1)] : List FactorBlock).map factorBlockValue).prod) = 589379336882119192349877593 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_31
      · exact prime_oneHundredSixtyEightFJ_71
      · exact prime_oneHundredSixtyEightFJ_383
      · exact prime_oneHundredSixtyEightFJ_87394902519107620253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 589379336882119192349877593) ^ 294689668441059596174938796 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 589379336882119192349877593) ^ 19012236673616748140318632 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 589379336882119192349877593) ^ 8301117420874918202110952 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 589379336882119192349877593) ^ 1538849443556446977414824 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 589379336882119192349877593) ^ 6743864 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_651215857473030058432487701 : Nat.Prime 651215857473030058432487701 := by
  apply lucas_primality 651215857473030058432487701 (2 : ZMod 651215857473030058432487701)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (5981, 1), (151009, 1), (600833, 1), (4000122587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (5981, 1), (151009, 1), (600833, 1), (4000122587, 1)] : List FactorBlock).map factorBlockValue).prod) = 651215857473030058432487701 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_5
      · exact prime_oneHundredSixtyEightFJ_5981
      · exact prime_oneHundredSixtyEightFJ_151009
      · exact prime_oneHundredSixtyEightFJ_600833
      · exact prime_oneHundredSixtyEightFJ_4000122587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 651215857473030058432487701) ^ 325607928736515029216243850 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 651215857473030058432487701) ^ 217071952491010019477495900 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 651215857473030058432487701) ^ 130243171494606011686497540 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 651215857473030058432487701) ^ 108880765335734836721700 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 651215857473030058432487701) ^ 4312430765537352465300 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 651215857473030058432487701) ^ 1083855010415589786900 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 651215857473030058432487701) ^ 162798975108767100 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_2579491383497067114570243491 : Nat.Prime 2579491383497067114570243491 := by
  apply lucas_primality 2579491383497067114570243491 (2 : ZMod 2579491383497067114570243491)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (103573, 1), (10089149659, 1), (35264271901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (103573, 1), (10089149659, 1), (35264271901, 1)] : List FactorBlock).map factorBlockValue).prod) = 2579491383497067114570243491 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_5
      · exact prime_oneHundredSixtyEightFJ_7
      · exact prime_oneHundredSixtyEightFJ_103573
      · exact prime_oneHundredSixtyEightFJ_10089149659
      · exact prime_oneHundredSixtyEightFJ_35264271901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2579491383497067114570243491) ^ 1289745691748533557285121745 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2579491383497067114570243491) ^ 515898276699413422914048698 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2579491383497067114570243491) ^ 368498769071009587795749070 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2579491383497067114570243491) ^ 24905056177740020223130 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2579491383497067114570243491) ^ 255669850352159110 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 2579491383497067114570243491) ^ 73147444834212490 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_5368130717007409941132668887 : Nat.Prime 5368130717007409941132668887 := by
  apply lucas_primality 5368130717007409941132668887 (3 : ZMod 5368130717007409941132668887)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (211, 1), (4240229634287053665981571, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (211, 1), (4240229634287053665981571, 1)] : List FactorBlock).map factorBlockValue).prod) = 5368130717007409941132668887 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_211
      · exact prime_oneHundredSixtyEightFJ_4240229634287053665981571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 5368130717007409941132668887) ^ 2684065358503704970566334443 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 5368130717007409941132668887) ^ 1789376905669136647044222962 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 5368130717007409941132668887) ^ 25441377805722321995889426 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 5368130717007409941132668887) ^ 1266 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_9028219842239734900995852221 : Nat.Prime 9028219842239734900995852221 := by
  apply lucas_primality 9028219842239734900995852221 (2 : ZMod 9028219842239734900995852221)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (2269, 1), (24570248051, 1), (8097073720069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (2269, 1), (24570248051, 1), (8097073720069, 1)] : List FactorBlock).map factorBlockValue).prod) = 9028219842239734900995852221 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_5
      · exact prime_oneHundredSixtyEightFJ_2269
      · exact prime_oneHundredSixtyEightFJ_24570248051
      · exact prime_oneHundredSixtyEightFJ_8097073720069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9028219842239734900995852221) ^ 4514109921119867450497926110 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 9028219842239734900995852221) ^ 1805643968447946980199170444 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 9028219842239734900995852221) ^ 3978942195786573336710380 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 9028219842239734900995852221) ^ 367445205416731220 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 9028219842239734900995852221) ^ 1114997856554380 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_13241389101951611188127249921 : Nat.Prime 13241389101951611188127249921 := by
  apply lucas_primality 13241389101951611188127249921 (11 : ZMod 13241389101951611188127249921)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 9), (5, 1), (7, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 9), (5, 1), (7, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 13241389101951611188127249921 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_5
      · exact prime_oneHundredSixtyEightFJ_7
      · exact prime_oneHundredSixtyEightFJ_171401
      · exact prime_oneHundredSixtyEightFJ_714027719
      · exact prime_oneHundredSixtyEightFJ_6037638679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 13241389101951611188127249921) ^ 6620694550975805594063624960 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (11 : ZMod 13241389101951611188127249921) ^ 2648277820390322237625449984 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (11 : ZMod 13241389101951611188127249921) ^ 1891627014564515884018178560 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (11 : ZMod 13241389101951611188127249921) ^ 77253861424096774161920 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (11 : ZMod 13241389101951611188127249921) ^ 18544642945369479680 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (11 : ZMod 13241389101951611188127249921) ^ 2193140365952596480 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_24827604566159270977738593611 : Nat.Prime 24827604566159270977738593611 := by
  apply lucas_primality 24827604566159270977738593611 (2 : ZMod 24827604566159270977738593611)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (443, 1), (5604425409968232726351827, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (443, 1), (5604425409968232726351827, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159270977738593611 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_5
      · exact prime_oneHundredSixtyEightFJ_443
      · exact prime_oneHundredSixtyEightFJ_5604425409968232726351827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 24827604566159270977738593611) ^ 12413802283079635488869296805 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 24827604566159270977738593611) ^ 4965520913231854195547718722 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 24827604566159270977738593611) ^ 56044254099682327263518270 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 24827604566159270977738593611) ^ 4430 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_39724167305854833564381749771 : Nat.Prime 39724167305854833564381749771 := by
  apply lucas_primality 39724167305854833564381749771 (2 : ZMod 39724167305854833564381749771)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1949, 1), (2038182006457405518952373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1949, 1), (2038182006457405518952373, 1)] : List FactorBlock).map factorBlockValue).prod) = 39724167305854833564381749771 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_5
      · exact prime_oneHundredSixtyEightFJ_1949
      · exact prime_oneHundredSixtyEightFJ_2038182006457405518952373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 39724167305854833564381749771) ^ 19862083652927416782190874885 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 39724167305854833564381749771) ^ 7944833461170966712876349954 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 39724167305854833564381749771) ^ 20381820064574055189523730 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 39724167305854833564381749771) ^ 19490 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_39724167305854833564381749777 : Nat.Prime 39724167305854833564381749777 := by
  apply lucas_primality 39724167305854833564381749777 (3 : ZMod 39724167305854833564381749777)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (443, 1), (5604425409968232726351827, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (443, 1), (5604425409968232726351827, 1)] : List FactorBlock).map factorBlockValue).prod) = 39724167305854833564381749777 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_443
      · exact prime_oneHundredSixtyEightFJ_5604425409968232726351827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 39724167305854833564381749777) ^ 19862083652927416782190874888 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 39724167305854833564381749777) ^ 89670806559491723621629232 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 39724167305854833564381749777) ^ 7088 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_99310418264637083910954374417 : Nat.Prime 99310418264637083910954374417 := by
  apply lucas_primality 99310418264637083910954374417 (3 : ZMod 99310418264637083910954374417)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (103981, 1), (292202129, 1), (204285462728549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (103981, 1), (292202129, 1), (204285462728549, 1)] : List FactorBlock).map factorBlockValue).prod) = 99310418264637083910954374417 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_103981
      · exact prime_oneHundredSixtyEightFJ_292202129
      · exact prime_oneHundredSixtyEightFJ_204285462728549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 99310418264637083910954374417) ^ 49655209132318541955477187208 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 99310418264637083910954374417) ^ 955082354128514670093136 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 99310418264637083910954374417) ^ 339868907199636057104 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (3 : ZMod 99310418264637083910954374417) ^ 486135513208784 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_198620836529274167821908748831 : Nat.Prime 198620836529274167821908748831 := by
  apply lucas_primality 198620836529274167821908748831 (6 : ZMod 198620836529274167821908748831)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (17, 1), (331, 1), (3169, 1), (12409, 1), (29327, 1), (340078141943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (17, 1), (331, 1), (3169, 1), (12409, 1), (29327, 1), (340078141943, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748831 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_5
      · exact prime_oneHundredSixtyEightFJ_17
      · exact prime_oneHundredSixtyEightFJ_331
      · exact prime_oneHundredSixtyEightFJ_3169
      · exact prime_oneHundredSixtyEightFJ_12409
      · exact prime_oneHundredSixtyEightFJ_29327
      · exact prime_oneHundredSixtyEightFJ_340078141943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 198620836529274167821908748831) ^ 99310418264637083910954374415 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (6 : ZMod 198620836529274167821908748831) ^ 66206945509758055940636249610 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (6 : ZMod 198620836529274167821908748831) ^ 39724167305854833564381749766 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (6 : ZMod 198620836529274167821908748831) ^ 11683578619369068695406396990 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (6 : ZMod 198620836529274167821908748831) ^ 600062950239498996440811930 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (6 : ZMod 198620836529274167821908748831) ^ 62676186976735300669583070 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (6 : ZMod 198620836529274167821908748831) ^ 16006192000102680943017870 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (6 : ZMod 198620836529274167821908748831) ^ 6772627153451569128172290 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (6 : ZMod 198620836529274167821908748831) ^ 584044700416425810 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyEightFJ_198620836529274167821908748867 : Nat.Prime 198620836529274167821908748867 := by
  apply lucas_primality 198620836529274167821908748867 (2 : ZMod 198620836529274167821908748867)
  · rw [← oneHundredSixtyEightFJFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (53, 1), (61, 1), (137, 1), (151, 1), (233, 1), (70379, 1), (3353735554207, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (53, 1), (61, 1), (137, 1), (151, 1), (233, 1), (70379, 1), (3353735554207, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748867 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyEightFJ_2
      · exact prime_oneHundredSixtyEightFJ_3
      · exact prime_oneHundredSixtyEightFJ_53
      · exact prime_oneHundredSixtyEightFJ_61
      · exact prime_oneHundredSixtyEightFJ_137
      · exact prime_oneHundredSixtyEightFJ_151
      · exact prime_oneHundredSixtyEightFJ_233
      · exact prime_oneHundredSixtyEightFJ_70379
      · exact prime_oneHundredSixtyEightFJ_3353735554207
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 198620836529274167821908748867) ^ 99310418264637083910954374433 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 198620836529274167821908748867) ^ 66206945509758055940636249622 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 198620836529274167821908748867) ^ 3747562953382531468337900922 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 198620836529274167821908748867) ^ 3256079287365150292162438506 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 198620836529274167821908748867) ^ 1449787127950906334466487218 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 198620836529274167821908748867) ^ 1315369778339564025310653966 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 198620836529274167821908748867) ^ 852449942185726042154114802 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 198620836529274167821908748867) ^ 2822160538360507648899654 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide
    · change (2 : ZMod 198620836529274167821908748867) ^ 59223762076327038 ≠ 1
      rw [← oneHundredSixtyEightFJFastPow_eq_pow]
      decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748800 : Nat.totient 198620836529274167821908748800 = 45398783408065799221592064000 := by
  rw [← show ((([(2, 9), (3, 1), (5, 2), (7, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748800 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_2, prime_oneHundredSixtyEightFJ_3, prime_oneHundredSixtyEightFJ_5, prime_oneHundredSixtyEightFJ_7, prime_oneHundredSixtyEightFJ_171401, prime_oneHundredSixtyEightFJ_714027719, prime_oneHundredSixtyEightFJ_6037638679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748801 : Nat.totient 198620836529274167821908748801 = 195254174083629073159685030400 := by
  rw [← show ((([(59, 1), (940619, 1), (28089823441, 1), (127411913641, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748801 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_59, prime_oneHundredSixtyEightFJ_940619, prime_oneHundredSixtyEightFJ_28089823441, prime_oneHundredSixtyEightFJ_127411913641]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748802 : Nat.totient 198620836529274167821908748802 = 94461889216570726398356413440 := by
  rw [← show ((([(2, 1), (23, 1), (179, 1), (19744281793, 1), (1221722587537021, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748802 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_2, prime_oneHundredSixtyEightFJ_23, prime_oneHundredSixtyEightFJ_179, prime_oneHundredSixtyEightFJ_19744281793, prime_oneHundredSixtyEightFJ_1221722587537021]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748803 : Nat.totient 198620836529274167821908748803 = 132413891019510506319455325120 := by
  rw [← show ((([(3, 2), (24251390888827, 1), (910008911973521, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748803 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_3, prime_oneHundredSixtyEightFJ_24251390888827, prime_oneHundredSixtyEightFJ_910008911973521]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748804 : Nat.totient 198620836529274167821908748804 = 99267173363322577369100578080 := by
  rw [← show ((([(2, 2), (2311, 1), (364979, 1), (58870400848523288429, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748804 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_2, prime_oneHundredSixtyEightFJ_2311, prime_oneHundredSixtyEightFJ_364979, prime_oneHundredSixtyEightFJ_58870400848523288429]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748805 : Nat.totient 198620836529274167821908748805 = 156291805793527214023797048000 := by
  rw [← show ((([(5, 1), (61, 1), (651215857473030058432487701, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748805 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_5, prime_oneHundredSixtyEightFJ_61, prime_oneHundredSixtyEightFJ_651215857473030058432487701]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748806 : Nat.totient 198620836529274167821908748806 = 65863878864934695397960402944 := by
  rw [← show ((([(2, 1), (3, 1), (193, 1), (2585293, 1), (66344737026778446149, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748806 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_2, prime_oneHundredSixtyEightFJ_3, prime_oneHundredSixtyEightFJ_193, prime_oneHundredSixtyEightFJ_2585293, prime_oneHundredSixtyEightFJ_66344737026778446149]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748807 : Nat.totient 198620836529274167821908748807 = 154769483009824026874214609400 := by
  rw [← show ((([(7, 1), (11, 1), (2579491383497067114570243491, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748807 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_7, prime_oneHundredSixtyEightFJ_11, prime_oneHundredSixtyEightFJ_2579491383497067114570243491]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748808 : Nat.totient 198620836529274167821908748808 = 99214273384389813306542645760 := by
  rw [← show ((([(2, 3), (1321, 1), (4733, 1), (3970959864830274425357, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748808 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_2, prime_oneHundredSixtyEightFJ_1321, prime_oneHundredSixtyEightFJ_4733, prime_oneHundredSixtyEightFJ_3970959864830274425357]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748809 : Nat.totient 198620836529274167821908748809 = 121960695970398326383681961472 := by
  rw [← show ((([(3, 1), (13, 1), (457, 1), (2286437, 1), (4873991417970856459, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748809 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_3, prime_oneHundredSixtyEightFJ_13, prime_oneHundredSixtyEightFJ_457, prime_oneHundredSixtyEightFJ_2286437, prime_oneHundredSixtyEightFJ_4873991417970856459]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748810 : Nat.totient 198620836529274167821908748810 = 77018130250067945288589120000 := by
  rw [← show ((([(2, 1), (5, 1), (43, 1), (251, 1), (283, 1), (267811, 1), (24281067873010409, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748810 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_2, prime_oneHundredSixtyEightFJ_5, prime_oneHundredSixtyEightFJ_43, prime_oneHundredSixtyEightFJ_251, prime_oneHundredSixtyEightFJ_283, prime_oneHundredSixtyEightFJ_267811, prime_oneHundredSixtyEightFJ_24281067873010409]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748811 : Nat.totient 198620836529274167821908748811 = 198325708986140030871207546432 := by
  rw [← show ((([(673, 1), (295127543134136950701201707, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748811 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_673, prime_oneHundredSixtyEightFJ_295127543134136950701201707]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748812 : Nat.totient 198620836529274167821908748812 = 66206945091428730370727714880 := by
  rw [← show ((([(2, 2), (3, 4), (158265131, 1), (3873419681044591673, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748812 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_2, prime_oneHundredSixtyEightFJ_3, prime_oneHundredSixtyEightFJ_158265131, prime_oneHundredSixtyEightFJ_3873419681044591673]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748813 : Nat.totient 198620836529274167821908748813 = 183410125470630111454226841600 := by
  rw [← show ((([(17, 1), (53, 1), (12767401, 1), (17266229799685710913, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748813 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_17, prime_oneHundredSixtyEightFJ_53, prime_oneHundredSixtyEightFJ_12767401, prime_oneHundredSixtyEightFJ_17266229799685710913]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748814 : Nat.totient 198620836529274167821908748814 = 77886505415273059310634228960 := by
  rw [← show ((([(2, 1), (7, 1), (19, 1), (31, 1), (503, 1), (47886543588161587791203, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748814 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_2, prime_oneHundredSixtyEightFJ_7, prime_oneHundredSixtyEightFJ_19, prime_oneHundredSixtyEightFJ_31, prime_oneHundredSixtyEightFJ_503, prime_oneHundredSixtyEightFJ_47886543588161587791203]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748815 : Nat.totient 198620836529274167821908748815 = 105931112815612889505017999360 := by
  rw [← show ((([(3, 1), (5, 1), (13241389101951611188127249921, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748815 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_3, prime_oneHundredSixtyEightFJ_5, prime_oneHundredSixtyEightFJ_13241389101951611188127249921]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748816 : Nat.totient 198620836529274167821908748816 = 98448796491671804711663370240 := by
  rw [← show ((([(2, 4), (163, 1), (617, 1), (1231, 1), (14737, 1), (22699, 1), (76163, 1), (3935629, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748816 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_2, prime_oneHundredSixtyEightFJ_163, prime_oneHundredSixtyEightFJ_617, prime_oneHundredSixtyEightFJ_1231, prime_oneHundredSixtyEightFJ_14737, prime_oneHundredSixtyEightFJ_22699, prime_oneHundredSixtyEightFJ_76163, prime_oneHundredSixtyEightFJ_3935629]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748817 : Nat.totient 198620836529274167821908748817 = 198466747432465949136026605600 := by
  rw [← show ((([(1289, 1), (27637266851, 1), (5575409842724003, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748817 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_1289, prime_oneHundredSixtyEightFJ_27637266851, prime_oneHundredSixtyEightFJ_5575409842724003]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748818 : Nat.totient 198620836529274167821908748818 = 58644165110773780486279616000 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (41, 1), (773, 1), (94954930555009359595661, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748818 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_2, prime_oneHundredSixtyEightFJ_3, prime_oneHundredSixtyEightFJ_11, prime_oneHundredSixtyEightFJ_41, prime_oneHundredSixtyEightFJ_773, prime_oneHundredSixtyEightFJ_94954930555009359595661]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748819 : Nat.totient 198620836529274167821908748819 = 193252705812266757880776079896 := by
  rw [← show ((([(37, 1), (5368130717007409941132668887, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748819 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_37, prime_oneHundredSixtyEightFJ_5368130717007409941132668887]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748820 : Nat.totient 198620836529274167821908748820 = 79448257164532662053234544672 := by
  rw [← show ((([(2, 2), (5, 1), (1025839, 1), (9680897125634440093519, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748820 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_2, prime_oneHundredSixtyEightFJ_5, prime_oneHundredSixtyEightFJ_1025839, prime_oneHundredSixtyEightFJ_9680897125634440093519]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748821 : Nat.totient 198620836529274167821908748821 = 111898918696799447221457256192 := by
  rw [← show ((([(3, 2), (7, 1), (89, 1), (347, 1), (2755243, 1), (37051420944511243, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748821 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_3, prime_oneHundredSixtyEightFJ_7, prime_oneHundredSixtyEightFJ_89, prime_oneHundredSixtyEightFJ_347, prime_oneHundredSixtyEightFJ_2755243, prime_oneHundredSixtyEightFJ_37051420944511243]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748822 : Nat.totient 198620836529274167821908748822 = 91668885318352387254249100800 := by
  rw [← show ((([(2, 1), (13, 1), (41681, 1), (1297477, 1), (141258197699135131, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748822 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_2, prime_oneHundredSixtyEightFJ_13, prime_oneHundredSixtyEightFJ_41681, prime_oneHundredSixtyEightFJ_1297477, prime_oneHundredSixtyEightFJ_141258197699135131]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748823 : Nat.totient 198620836529274167821908748823 = 196692478893049112180535428568 := by
  rw [← show ((([(103, 1), (11333960240279, 1), (170139791857879, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748823 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_103, prime_oneHundredSixtyEightFJ_11333960240279, prime_oneHundredSixtyEightFJ_170139791857879]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748824 : Nat.totient 198620836529274167821908748824 = 66206945509332124502815796736 := by
  rw [← show ((([(2, 3), (3, 1), (155440836073, 1), (53241274286720537, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748824 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_2, prime_oneHundredSixtyEightFJ_3, prime_oneHundredSixtyEightFJ_155440836073, prime_oneHundredSixtyEightFJ_53241274286720537]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748825 : Nat.totient 198620836529274167821908748825 = 145250796440968282328406912000 := by
  rw [← show ((([(5, 2), (23, 1), (29, 1), (101, 1), (3347, 1), (35235616776614517997, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748825 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_5, prime_oneHundredSixtyEightFJ_23, prime_oneHundredSixtyEightFJ_29, prime_oneHundredSixtyEightFJ_101, prime_oneHundredSixtyEightFJ_3347, prime_oneHundredSixtyEightFJ_35235616776614517997]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748826 : Nat.totient 198620836529274167821908748826 = 99307729038872383077357138688 := by
  rw [← show ((([(2, 1), (36929, 1), (2689225764700833597198797, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748826 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_2, prime_oneHundredSixtyEightFJ_36929, prime_oneHundredSixtyEightFJ_2689225764700833597198797]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748827 : Nat.totient 198620836529274167821908748827 = 132366650933340432997080143040 := by
  rw [← show ((([(3, 1), (2803, 1), (5260447481, 1), (4490118111021163, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748827 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_3, prime_oneHundredSixtyEightFJ_2803, prime_oneHundredSixtyEightFJ_5260447481, prime_oneHundredSixtyEightFJ_4490118111021163]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748828 : Nat.totient 198620836529274167821908748828 = 85049388061599742781875338240 := by
  rw [← show ((([(2, 2), (7, 2), (1153, 1), (878899926231809511221431, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748828 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_2, prime_oneHundredSixtyEightFJ_7, prime_oneHundredSixtyEightFJ_1153, prime_oneHundredSixtyEightFJ_878899926231809511221431]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748829 : Nat.totient 198620836529274167821908748829 = 180564396841900353840989059200 := by
  rw [← show ((([(11, 2), (62385401941, 1), (26312157423034289, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748829 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_11, prime_oneHundredSixtyEightFJ_62385401941, prime_oneHundredSixtyEightFJ_26312157423034289]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748830 : Nat.totient 198620836529274167821908748830 = 49677950608265539408786882560 := by
  rw [← show ((([(2, 1), (3, 2), (5, 1), (17, 1), (331, 1), (3169, 1), (12409, 1), (29327, 1), (340078141943, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748830 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_2, prime_oneHundredSixtyEightFJ_3, prime_oneHundredSixtyEightFJ_5, prime_oneHundredSixtyEightFJ_17, prime_oneHundredSixtyEightFJ_331, prime_oneHundredSixtyEightFJ_3169, prime_oneHundredSixtyEightFJ_12409, prime_oneHundredSixtyEightFJ_29327, prime_oneHundredSixtyEightFJ_340078141943]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748831 : Nat.totient 198620836529274167821908748831 = 198620836529274167821908748830 := by
  rw [← show ((([(198620836529274167821908748831, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748831 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_198620836529274167821908748831]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748832 : Nat.totient 198620836529274167821908748832 = 99309462842416830633215569920 := by
  rw [← show ((([(2, 5), (103981, 1), (292202129, 1), (204285462728549, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748832 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_2, prime_oneHundredSixtyEightFJ_103981, prime_oneHundredSixtyEightFJ_292202129, prime_oneHundredSixtyEightFJ_204285462728549]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748833 : Nat.totient 198620836529274167821908748833 = 125440459617755836888312893696 := by
  rw [← show ((([(3, 1), (19, 1), (42943, 1), (92369, 1), (878478886576156007, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748833 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_3, prime_oneHundredSixtyEightFJ_19, prime_oneHundredSixtyEightFJ_42943, prime_oneHundredSixtyEightFJ_92369, prime_oneHundredSixtyEightFJ_878478886576156007]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748834 : Nat.totient 198620836529274167821908748834 = 99310418264637083910954374416 := by
  rw [← show ((([(2, 1), (99310418264637083910954374417, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748834 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_2, prime_oneHundredSixtyEightFJ_99310418264637083910954374417]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748835 : Nat.totient 198620836529274167821908748835 = 125720441574845634052198542720 := by
  rw [← show ((([(5, 1), (7, 1), (13, 1), (14757462491, 1), (29580241950103007, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748835 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_5, prime_oneHundredSixtyEightFJ_7, prime_oneHundredSixtyEightFJ_13, prime_oneHundredSixtyEightFJ_14757462491, prime_oneHundredSixtyEightFJ_29580241950103007]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748836 : Nat.totient 198620836529274167821908748836 = 65218682367177252466866645024 := by
  rw [← show ((([(2, 2), (3, 1), (67, 1), (653647, 1), (377942286057032472047, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748836 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_2, prime_oneHundredSixtyEightFJ_3, prime_oneHundredSixtyEightFJ_67, prime_oneHundredSixtyEightFJ_653647, prime_oneHundredSixtyEightFJ_377942286057032472047]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748837 : Nat.totient 198620836529274167821908748837 = 198608255238558434993136837900 := by
  rw [← show ((([(15787, 1), (12581290715732828771895151, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748837 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_15787, prime_oneHundredSixtyEightFJ_12581290715732828771895151]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748838 : Nat.totient 198620836529274167821908748838 = 99310206225071510506099739400 := by
  rw [← show ((([(2, 1), (468359, 1), (300752680831, 1), (705028111211, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748838 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_2, prime_oneHundredSixtyEightFJ_468359, prime_oneHundredSixtyEightFJ_300752680831, prime_oneHundredSixtyEightFJ_705028111211]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748839 : Nat.totient 198620836529274167821908748839 = 132410941464112594636590407520 := by
  rw [← show ((([(3, 3), (44893, 1), (11905824439, 1), (13763311522591, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748839 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_3, prime_oneHundredSixtyEightFJ_44893, prime_oneHundredSixtyEightFJ_11905824439, prime_oneHundredSixtyEightFJ_13763311522591]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748840 : Nat.totient 198620836529274167821908748840 = 72193927197404404458122112000 := by
  rw [← show ((([(2, 3), (5, 1), (11, 1), (2269, 1), (24570248051, 1), (8097073720069, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748840 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_2, prime_oneHundredSixtyEightFJ_5, prime_oneHundredSixtyEightFJ_11, prime_oneHundredSixtyEightFJ_2269, prime_oneHundredSixtyEightFJ_24570248051, prime_oneHundredSixtyEightFJ_8097073720069]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748841 : Nat.totient 198620836529274167821908748841 = 198031457192392048629558870912 := by
  rw [← show ((([(337, 1), (589379336882119192349877593, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748841 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_337, prime_oneHundredSixtyEightFJ_589379336882119192349877593]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748842 : Nat.totient 198620836529274167821908748842 = 56741304949830443959591236480 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (7561, 1), (2416168199, 1), (258862483991359, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748842 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_2, prime_oneHundredSixtyEightFJ_3, prime_oneHundredSixtyEightFJ_7, prime_oneHundredSixtyEightFJ_7561, prime_oneHundredSixtyEightFJ_2416168199, prime_oneHundredSixtyEightFJ_258862483991359]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748843 : Nat.totient 198620836529274167821908748843 = 195678292776780459140856299520 := by
  rw [← show ((([(73, 1), (887, 1), (229253, 1), (13380221384344769281, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748843 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_73, prime_oneHundredSixtyEightFJ_887, prime_oneHundredSixtyEightFJ_229253, prime_oneHundredSixtyEightFJ_13380221384344769281]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748844 : Nat.totient 198620836529274167821908748844 = 99235991886563045966411022336 := by
  rw [← show ((([(2, 2), (2029, 1), (5153, 1), (16139, 1), (1442173, 1), (204046262249, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748844 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_2, prime_oneHundredSixtyEightFJ_2029, prime_oneHundredSixtyEightFJ_5153, prime_oneHundredSixtyEightFJ_16139, prime_oneHundredSixtyEightFJ_1442173, prime_oneHundredSixtyEightFJ_204046262249]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748845 : Nat.totient 198620836529274167821908748845 = 102506155338863669215915814400 := by
  rw [← show ((([(3, 1), (5, 1), (31, 1), (13147, 1), (3756671, 1), (8648524669571609, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748845 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_3, prime_oneHundredSixtyEightFJ_5, prime_oneHundredSixtyEightFJ_31, prime_oneHundredSixtyEightFJ_13147, prime_oneHundredSixtyEightFJ_3756671, prime_oneHundredSixtyEightFJ_8648524669571609]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748846 : Nat.totient 198620836529274167821908748846 = 96819230510626989662855362560 := by
  rw [← show ((([(2, 1), (47, 1), (257, 1), (7982699411, 1), (1029945047292067, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748846 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_2, prime_oneHundredSixtyEightFJ_47, prime_oneHundredSixtyEightFJ_257, prime_oneHundredSixtyEightFJ_7982699411, prime_oneHundredSixtyEightFJ_1029945047292067]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748847 : Nat.totient 198620836529274167821908748847 = 185902381918842339840405765120 := by
  rw [← show ((([(17, 1), (181, 1), (89659, 1), (719951796451679731129, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748847 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_17, prime_oneHundredSixtyEightFJ_181, prime_oneHundredSixtyEightFJ_89659, prime_oneHundredSixtyEightFJ_719951796451679731129]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748848 : Nat.totient 198620836529274167821908748848 = 58456968610622497552936341504 := by
  rw [← show ((([(2, 4), (3, 2), (13, 1), (23, 1), (4613081487580689516488033, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748848 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_2, prime_oneHundredSixtyEightFJ_3, prime_oneHundredSixtyEightFJ_13, prime_oneHundredSixtyEightFJ_23, prime_oneHundredSixtyEightFJ_4613081487580689516488033]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748849 : Nat.totient 198620836529274167821908748849 = 170189128573630122906686056320 := by
  rw [← show ((([(7, 1), (2971, 1), (626696252953, 1), (15239370115789, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748849 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_7, prime_oneHundredSixtyEightFJ_2971, prime_oneHundredSixtyEightFJ_626696252953, prime_oneHundredSixtyEightFJ_15239370115789]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748850 : Nat.totient 198620836529274167821908748850 = 79407570971580519018384413120 := by
  rw [← show ((([(2, 1), (5, 2), (1949, 1), (2038182006457405518952373, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748850 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_2, prime_oneHundredSixtyEightFJ_5, prime_oneHundredSixtyEightFJ_1949, prime_oneHundredSixtyEightFJ_2038182006457405518952373]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748851 : Nat.totient 198620836529274167821908748851 = 120017870504142123086609333760 := by
  rw [← show ((([(3, 1), (11, 1), (419, 1), (2143, 1), (8693, 1), (151787, 1), (262519, 1), (19351279, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748851 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_3, prime_oneHundredSixtyEightFJ_11, prime_oneHundredSixtyEightFJ_419, prime_oneHundredSixtyEightFJ_2143, prime_oneHundredSixtyEightFJ_8693, prime_oneHundredSixtyEightFJ_151787, prime_oneHundredSixtyEightFJ_262519, prime_oneHundredSixtyEightFJ_19351279]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748852 : Nat.totient 198620836529274167821908748852 = 93484295750357898690220480512 := by
  rw [← show ((([(2, 2), (19, 1), (157, 1), (1057169473, 1), (15745880390038507, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748852 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_2, prime_oneHundredSixtyEightFJ_19, prime_oneHundredSixtyEightFJ_157, prime_oneHundredSixtyEightFJ_1057169473, prime_oneHundredSixtyEightFJ_15745880390038507]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748853 : Nat.totient 198620836529274167821908748853 = 194001652891571616444378904704 := by
  rw [← show ((([(43, 1), (2054753, 1), (2248002179148066535807, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748853 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_43, prime_oneHundredSixtyEightFJ_2054753, prime_oneHundredSixtyEightFJ_2248002179148066535807]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748854 : Nat.totient 198620836529274167821908748854 = 63923947388149385261412920064 := by
  rw [← show ((([(2, 1), (3, 1), (29, 1), (109736033929, 1), (10402226321133749, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748854 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_2, prime_oneHundredSixtyEightFJ_3, prime_oneHundredSixtyEightFJ_29, prime_oneHundredSixtyEightFJ_109736033929, prime_oneHundredSixtyEightFJ_10402226321133749]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748855 : Nat.totient 198620836529274167821908748855 = 158896669223419334257526999080 := by
  rw [← show ((([(5, 1), (39724167305854833564381749771, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748855 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_5, prime_oneHundredSixtyEightFJ_39724167305854833564381749771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748856 : Nat.totient 198620836529274167821908748856 = 82819931676784100601026153472 := by
  rw [← show ((([(2, 3), (7, 1), (37, 1), (31177, 1), (3074685732733041494149, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748856 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_2, prime_oneHundredSixtyEightFJ_7, prime_oneHundredSixtyEightFJ_37, prime_oneHundredSixtyEightFJ_31177, prime_oneHundredSixtyEightFJ_3074685732733041494149]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748857 : Nat.totient 198620836529274167821908748857 = 132413807816411069199828443904 := by
  rw [← show ((([(3, 2), (1591813, 1), (7076497397, 1), (1959168993193, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748857 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_3, prime_oneHundredSixtyEightFJ_1591813, prime_oneHundredSixtyEightFJ_7076497397, prime_oneHundredSixtyEightFJ_1959168993193]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748858 : Nat.totient 198620836529274167821908748858 = 99310418264633951080995589440 := by
  rw [← show ((([(2, 1), (32027326483181, 1), (3100802632301809, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748858 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_2, prime_oneHundredSixtyEightFJ_32027326483181, prime_oneHundredSixtyEightFJ_3100802632301809]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748859 : Nat.totient 198620836529274167821908748859 = 191047180447257873549070590400 := by
  rw [← show ((([(41, 1), (71, 1), (68231135874020669124668069, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748859 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_41, prime_oneHundredSixtyEightFJ_71, prime_oneHundredSixtyEightFJ_68231135874020669124668069]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748860 : Nat.totient 198620836529274167821908748860 = 51531053307472703893402066944 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (59, 2), (97, 1), (9803875754057824351433, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748860 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_2, prime_oneHundredSixtyEightFJ_3, prime_oneHundredSixtyEightFJ_5, prime_oneHundredSixtyEightFJ_59, prime_oneHundredSixtyEightFJ_97, prime_oneHundredSixtyEightFJ_9803875754057824351433]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748861 : Nat.totient 198620836529274167821908748861 = 183194095354375536335135822400 := by
  rw [← show ((([(13, 1), (1237, 1), (350800075411, 1), (35208869166271, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748861 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_13, prime_oneHundredSixtyEightFJ_1237, prime_oneHundredSixtyEightFJ_350800075411, prime_oneHundredSixtyEightFJ_35208869166271]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748862 : Nat.totient 198620836529274167821908748862 = 90282198422397349009958522200 := by
  rw [← show ((([(2, 1), (11, 1), (9028219842239734900995852221, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748862 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_2, prime_oneHundredSixtyEightFJ_11, prime_oneHundredSixtyEightFJ_9028219842239734900995852221]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748863 : Nat.totient 198620836529274167821908748863 = 113346460683417253213611900000 := by
  rw [← show ((([(3, 1), (7, 1), (751, 1), (3594403, 1), (3503795954666829551, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748863 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_3, prime_oneHundredSixtyEightFJ_7, prime_oneHundredSixtyEightFJ_751, prime_oneHundredSixtyEightFJ_3594403, prime_oneHundredSixtyEightFJ_3503795954666829551]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748864 : Nat.totient 198620836529274167821908748864 = 93468626031256353929029156864 := by
  rw [← show ((([(2, 6), (17, 2), (31969337, 1), (335902595973800657, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748864 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_2, prime_oneHundredSixtyEightFJ_17, prime_oneHundredSixtyEightFJ_31969337, prime_oneHundredSixtyEightFJ_335902595973800657]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748865 : Nat.totient 198620836529274167821908748865 = 158676536938909362662149882560 := by
  rw [← show ((([(5, 1), (727, 1), (105323, 1), (2609083, 1), (198842527769411, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748865 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_5, prime_oneHundredSixtyEightFJ_727, prime_oneHundredSixtyEightFJ_105323, prime_oneHundredSixtyEightFJ_2609083, prime_oneHundredSixtyEightFJ_198842527769411]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748866 : Nat.totient 198620836529274167821908748866 = 62735156735849879482865664000 := by
  rw [← show ((([(2, 1), (3, 3), (53, 1), (61, 1), (137, 1), (151, 1), (233, 1), (70379, 1), (3353735554207, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748866 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_2, prime_oneHundredSixtyEightFJ_3, prime_oneHundredSixtyEightFJ_53, prime_oneHundredSixtyEightFJ_61, prime_oneHundredSixtyEightFJ_137, prime_oneHundredSixtyEightFJ_151, prime_oneHundredSixtyEightFJ_233, prime_oneHundredSixtyEightFJ_70379, prime_oneHundredSixtyEightFJ_3353735554207]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748867 : Nat.totient 198620836529274167821908748867 = 198620836529274167821908748866 := by
  rw [← show ((([(198620836529274167821908748867, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748867 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_198620836529274167821908748867]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748868 : Nat.totient 198620836529274167821908748868 = 99048385498747412719371901248 := by
  rw [← show ((([(2, 2), (379, 1), (6653737764137, 1), (19690644203179, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748868 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_2, prime_oneHundredSixtyEightFJ_379, prime_oneHundredSixtyEightFJ_6653737764137, prime_oneHundredSixtyEightFJ_19690644203179]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748869 : Nat.totient 198620836529274167821908748869 = 132362240245933576177024524288 := by
  rw [← show ((([(3, 1), (2689, 1), (55343, 1), (8141093, 1), (54647127243493, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748869 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_3, prime_oneHundredSixtyEightFJ_2689, prime_oneHundredSixtyEightFJ_55343, prime_oneHundredSixtyEightFJ_8141093, prime_oneHundredSixtyEightFJ_54647127243493]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748870 : Nat.totient 198620836529274167821908748870 = 68098572204836063718166645248 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (213150073, 1), (13311937837557174217, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748870 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_2, prime_oneHundredSixtyEightFJ_5, prime_oneHundredSixtyEightFJ_7, prime_oneHundredSixtyEightFJ_213150073, prime_oneHundredSixtyEightFJ_13311937837557174217]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748871 : Nat.totient 198620836529274167821908748871 = 175787645207271827276734387200 := by
  rw [← show ((([(19, 1), (23, 1), (79, 1), (131, 1), (313, 1), (13727981, 1), (10221013826539, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748871 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_19, prime_oneHundredSixtyEightFJ_23, prime_oneHundredSixtyEightFJ_79, prime_oneHundredSixtyEightFJ_131, prime_oneHundredSixtyEightFJ_313, prime_oneHundredSixtyEightFJ_13727981, prime_oneHundredSixtyEightFJ_10221013826539]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748872 : Nat.totient 198620836529274167821908748872 = 66206943610464788295843111104 := by
  rw [← show ((([(2, 3), (3, 1), (34858727, 1), (237411658455564283589, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748872 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_2, prime_oneHundredSixtyEightFJ_3, prime_oneHundredSixtyEightFJ_34858727, prime_oneHundredSixtyEightFJ_237411658455564283589]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748873 : Nat.totient 198620836529274167821908748873 = 180564396844455742848350838000 := by
  rw [← show ((([(11, 1), (532717155151, 1), (33894984439465493, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748873 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_11, prime_oneHundredSixtyEightFJ_532717155151, prime_oneHundredSixtyEightFJ_33894984439465493]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748874 : Nat.totient 198620836529274167821908748874 = 90520966945136065065867659520 := by
  rw [← show ((([(2, 1), (13, 1), (83, 1), (1987, 1), (660661, 1), (70112722111512029, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748874 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_2, prime_oneHundredSixtyEightFJ_13, prime_oneHundredSixtyEightFJ_83, prime_oneHundredSixtyEightFJ_1987, prime_oneHundredSixtyEightFJ_660661, prime_oneHundredSixtyEightFJ_70112722111512029]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748875 : Nat.totient 198620836529274167821908748875 = 104980104544259703616865280000 := by
  rw [← show ((([(3, 2), (5, 3), (127, 1), (1667, 1), (1951, 1), (4474849, 1), (95520658789, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748875 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_3, prime_oneHundredSixtyEightFJ_5, prime_oneHundredSixtyEightFJ_127, prime_oneHundredSixtyEightFJ_1667, prime_oneHundredSixtyEightFJ_1951, prime_oneHundredSixtyEightFJ_4474849, prime_oneHundredSixtyEightFJ_95520658789]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748876 : Nat.totient 198620836529274167821908748876 = 94927838755452748906291200000 := by
  rw [← show ((([(2, 2), (31, 1), (277, 1), (293, 1), (463, 1), (577, 1), (709, 1), (104196394828751, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748876 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_2, prime_oneHundredSixtyEightFJ_31, prime_oneHundredSixtyEightFJ_277, prime_oneHundredSixtyEightFJ_293, prime_oneHundredSixtyEightFJ_463, prime_oneHundredSixtyEightFJ_577, prime_oneHundredSixtyEightFJ_709, prime_oneHundredSixtyEightFJ_104196394828751]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748877 : Nat.totient 198620836529274167821908748877 = 170246393584386176102879082480 := by
  rw [← show ((([(7, 3), (4517543, 1), (4980897683, 1), (25734798431, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748877 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_7, prime_oneHundredSixtyEightFJ_4517543, prime_oneHundredSixtyEightFJ_4980897683, prime_oneHundredSixtyEightFJ_25734798431]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748878 : Nat.totient 198620836529274167821908748878 = 66206945509721293879531931256 := by
  rw [← show ((([(2, 1), (3, 1), (1801134966187, 1), (18379229417192999, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748878 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_2, prime_oneHundredSixtyEightFJ_3, prime_oneHundredSixtyEightFJ_1801134966187, prime_oneHundredSixtyEightFJ_18379229417192999]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748879 : Nat.totient 198620836529274167821908748879 = 198620830886917382029522434840 := by
  rw [← show ((([(45133343, 1), (159972523, 1), (27509450135411, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748879 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_45133343, prime_oneHundredSixtyEightFJ_159972523, prime_oneHundredSixtyEightFJ_27509450135411]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748880 : Nat.totient 198620836529274167821908748880 = 79268992998590683681520226944 := by
  rw [← show ((([(2, 4), (5, 1), (443, 1), (5604425409968232726351827, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748880 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_2, prime_oneHundredSixtyEightFJ_5, prime_oneHundredSixtyEightFJ_443, prime_oneHundredSixtyEightFJ_5604425409968232726351827]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748881 : Nat.totient 198620836529274167821908748881 = 123432510308539210759929231360 := by
  rw [← show ((([(3, 1), (17, 1), (109, 1), (2521, 1), (14172787871626434216079, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748881 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_3, prime_oneHundredSixtyEightFJ_17, prime_oneHundredSixtyEightFJ_109, prime_oneHundredSixtyEightFJ_2521, prime_oneHundredSixtyEightFJ_14172787871626434216079]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748882 : Nat.totient 198620836529274167821908748882 = 99309863113575449953114915584 := by
  rw [← show ((([(2, 1), (178889, 1), (555151061633957839279969, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748882 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_2, prime_oneHundredSixtyEightFJ_178889, prime_oneHundredSixtyEightFJ_555151061633957839279969]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748883 : Nat.totient 198620836529274167821908748883 = 191748577354577866918508737888 := by
  rw [← show ((([(29, 1), (8243, 1), (830886129210047261927189, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748883 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_29, prime_oneHundredSixtyEightFJ_8243, prime_oneHundredSixtyEightFJ_830886129210047261927189]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748884 : Nat.totient 198620836529274167821908748884 = 51477183719686484517305088000 := by
  rw [← show ((([(2, 2), (3, 2), (7, 1), (11, 1), (461, 1), (69997, 1), (2220502305087140441, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748884 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_2, prime_oneHundredSixtyEightFJ_3, prime_oneHundredSixtyEightFJ_7, prime_oneHundredSixtyEightFJ_11, prime_oneHundredSixtyEightFJ_461, prime_oneHundredSixtyEightFJ_69997, prime_oneHundredSixtyEightFJ_2220502305087140441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748885 : Nat.totient 198620836529274167821908748885 = 158896669223419334257526999104 := by
  rw [← show ((([(5, 1), (39724167305854833564381749777, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748885 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_5, prime_oneHundredSixtyEightFJ_39724167305854833564381749777]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748886 : Nat.totient 198620836529274167821908748886 = 99304059887097580079949542400 := by
  rw [← show ((([(2, 1), (17881, 1), (124297, 1), (18114361, 1), (2466717089059, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748886 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_2, prime_oneHundredSixtyEightFJ_17881, prime_oneHundredSixtyEightFJ_124297, prime_oneHundredSixtyEightFJ_18114361, prime_oneHundredSixtyEightFJ_2466717089059]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748887 : Nat.totient 198620836529274167821908748887 = 121488644452154693382432092160 := by
  rw [← show ((([(3, 1), (13, 1), (311, 1), (383, 1), (4273, 1), (10006176146377349017, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748887 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_3, prime_oneHundredSixtyEightFJ_13, prime_oneHundredSixtyEightFJ_311, prime_oneHundredSixtyEightFJ_383, prime_oneHundredSixtyEightFJ_4273, prime_oneHundredSixtyEightFJ_10006176146377349017]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748888 : Nat.totient 198620836529274167821908748888 = 99310418264637083910954374440 := by
  rw [← show ((([(2, 3), (24827604566159270977738593611, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748888 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_2, prime_oneHundredSixtyEightFJ_24827604566159270977738593611]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748889 : Nat.totient 198620836529274167821908748889 = 198620836488876517556523440400 := by
  rw [← show ((([(4916643301, 1), (40397650260468665189, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748889 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_4916643301, prime_oneHundredSixtyEightFJ_40397650260468665189]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748890 : Nat.totient 198620836529274167821908748890 = 49661309039078441471840206848 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (19, 1), (139, 1), (353, 1), (3433, 1), (2068648210956352507, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748890 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_2, prime_oneHundredSixtyEightFJ_3, prime_oneHundredSixtyEightFJ_5, prime_oneHundredSixtyEightFJ_19, prime_oneHundredSixtyEightFJ_139, prime_oneHundredSixtyEightFJ_353, prime_oneHundredSixtyEightFJ_3433, prime_oneHundredSixtyEightFJ_2068648210956352507]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748891 : Nat.totient 198620836529274167821908748891 = 170246431310799086876688556968 := by
  rw [← show ((([(7, 1), (23642614645087, 1), (1200138209940499, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748891 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_7, prime_oneHundredSixtyEightFJ_23642614645087, prime_oneHundredSixtyEightFJ_1200138209940499]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748892 : Nat.totient 198620836529274167821908748892 = 99178420695171318852542357760 := by
  rw [← show ((([(2, 2), (881, 1), (5147, 1), (44985986047, 1), (243420692987, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748892 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_2, prime_oneHundredSixtyEightFJ_881, prime_oneHundredSixtyEightFJ_5147, prime_oneHundredSixtyEightFJ_44985986047, prime_oneHundredSixtyEightFJ_243420692987]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748893 : Nat.totient 198620836529274167821908748893 = 126093964076088948404477920224 := by
  rw [← show ((([(3, 4), (37, 1), (47, 1), (1410068483584820052832327, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748893 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_3, prime_oneHundredSixtyEightFJ_37, prime_oneHundredSixtyEightFJ_47, prime_oneHundredSixtyEightFJ_1410068483584820052832327]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748894 : Nat.totient 198620836529274167821908748894 = 94989900479723429521845537880 := by
  rw [← show ((([(2, 1), (23, 1), (35531, 1), (121523297187681894329819, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748894 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_2, prime_oneHundredSixtyEightFJ_23, prime_oneHundredSixtyEightFJ_35531, prime_oneHundredSixtyEightFJ_121523297187681894329819]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748895 : Nat.totient 198620836529274167821908748895 = 144451517473267046418688974240 := by
  rw [← show ((([(5, 1), (11, 1), (56235048587, 1), (64217743696067947, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748895 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_5, prime_oneHundredSixtyEightFJ_11, prime_oneHundredSixtyEightFJ_56235048587, prime_oneHundredSixtyEightFJ_64217743696067947]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748896 : Nat.totient 198620836529274167821908748896 = 64667232023733921551485501440 := by
  rw [← show ((([(2, 5), (3, 1), (43, 1), (4282273, 1), (32701811, 1), (343588771969, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748896 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_2, prime_oneHundredSixtyEightFJ_3, prime_oneHundredSixtyEightFJ_43, prime_oneHundredSixtyEightFJ_4282273, prime_oneHundredSixtyEightFJ_32701811, prime_oneHundredSixtyEightFJ_343588771969]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748897 : Nat.totient 198620836529274167821908748897 = 198620836092799068893962530816 := by
  rw [← show ((([(455056513, 1), (436475098927491161569, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748897 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_455056513, prime_oneHundredSixtyEightFJ_436475098927491161569]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748898 : Nat.totient 198620836529274167821908748898 = 80115967532435363412880476672 := by
  rw [← show ((([(2, 1), (7, 1), (17, 1), (559319647, 1), (1492065108799822793, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748898 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_2, prime_oneHundredSixtyEightFJ_7, prime_oneHundredSixtyEightFJ_17, prime_oneHundredSixtyEightFJ_559319647, prime_oneHundredSixtyEightFJ_1492065108799822793]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748899 : Nat.totient 198620836529274167821908748899 = 132413891019150500713569322080 := by
  rw [← show ((([(3, 1), (362172069821, 1), (182805221679518773, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748899 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_3, prime_oneHundredSixtyEightFJ_362172069821, prime_oneHundredSixtyEightFJ_182805221679518773]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748900 : Nat.totient 198620836529274167821908748900 = 70879543845343547605887513600 := by
  rw [← show ((([(2, 2), (5, 2), (13, 1), (41, 1), (107, 1), (34826819892562670796919, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748900 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_2, prime_oneHundredSixtyEightFJ_5, prime_oneHundredSixtyEightFJ_13, prime_oneHundredSixtyEightFJ_41, prime_oneHundredSixtyEightFJ_107, prime_oneHundredSixtyEightFJ_34826819892562670796919]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748901 : Nat.totient 198620836529274167821908748901 = 198616117461666734189182295904 := by
  rw [← show ((([(42089, 1), (4719067607433632726410909, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748901 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_42089, prime_oneHundredSixtyEightFJ_4719067607433632726410909]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748902 : Nat.totient 198620836529274167821908748902 = 66206825880021213643187712000 := by
  rw [← show ((([(2, 1), (3, 2), (553601, 1), (1815083779, 1), (10981426522441, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748902 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_2, prime_oneHundredSixtyEightFJ_3, prime_oneHundredSixtyEightFJ_553601, prime_oneHundredSixtyEightFJ_1815083779, prime_oneHundredSixtyEightFJ_10981426522441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyEightFJ_198620836529274167821908748903 : Nat.totient 198620836529274167821908748903 = 195612702366144906068811803064 := by
  rw [← show ((([(67, 1), (4483, 1), (661273722384977303384623, 1)] : List FactorBlock).map factorBlockValue).prod) = 198620836529274167821908748903 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyEightFJ_67, prime_oneHundredSixtyEightFJ_4483, prime_oneHundredSixtyEightFJ_661273722384977303384623]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64OneHundredSixtyEightFJ : certifiedKill 3 198620836529274167821908748799 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_oneHundredSixtyEightFJ_198620836529274167821908748800, phi_oneHundredSixtyEightFJ_198620836529274167821908748801, phi_oneHundredSixtyEightFJ_198620836529274167821908748802,
    phi_oneHundredSixtyEightFJ_198620836529274167821908748803, phi_oneHundredSixtyEightFJ_198620836529274167821908748804, phi_oneHundredSixtyEightFJ_198620836529274167821908748805,
    phi_oneHundredSixtyEightFJ_198620836529274167821908748806, phi_oneHundredSixtyEightFJ_198620836529274167821908748807, phi_oneHundredSixtyEightFJ_198620836529274167821908748808,
    phi_oneHundredSixtyEightFJ_198620836529274167821908748809, phi_oneHundredSixtyEightFJ_198620836529274167821908748810, phi_oneHundredSixtyEightFJ_198620836529274167821908748811,
    phi_oneHundredSixtyEightFJ_198620836529274167821908748812, phi_oneHundredSixtyEightFJ_198620836529274167821908748813, phi_oneHundredSixtyEightFJ_198620836529274167821908748814,
    phi_oneHundredSixtyEightFJ_198620836529274167821908748815, phi_oneHundredSixtyEightFJ_198620836529274167821908748816, phi_oneHundredSixtyEightFJ_198620836529274167821908748817,
    phi_oneHundredSixtyEightFJ_198620836529274167821908748818, phi_oneHundredSixtyEightFJ_198620836529274167821908748819, phi_oneHundredSixtyEightFJ_198620836529274167821908748820,
    phi_oneHundredSixtyEightFJ_198620836529274167821908748821, phi_oneHundredSixtyEightFJ_198620836529274167821908748822, phi_oneHundredSixtyEightFJ_198620836529274167821908748823,
    phi_oneHundredSixtyEightFJ_198620836529274167821908748824, phi_oneHundredSixtyEightFJ_198620836529274167821908748825, phi_oneHundredSixtyEightFJ_198620836529274167821908748826,
    phi_oneHundredSixtyEightFJ_198620836529274167821908748827, phi_oneHundredSixtyEightFJ_198620836529274167821908748828, phi_oneHundredSixtyEightFJ_198620836529274167821908748829,
    phi_oneHundredSixtyEightFJ_198620836529274167821908748830, phi_oneHundredSixtyEightFJ_198620836529274167821908748831, phi_oneHundredSixtyEightFJ_198620836529274167821908748832,
    phi_oneHundredSixtyEightFJ_198620836529274167821908748833, phi_oneHundredSixtyEightFJ_198620836529274167821908748834, phi_oneHundredSixtyEightFJ_198620836529274167821908748835,
    phi_oneHundredSixtyEightFJ_198620836529274167821908748836, phi_oneHundredSixtyEightFJ_198620836529274167821908748837, phi_oneHundredSixtyEightFJ_198620836529274167821908748838,
    phi_oneHundredSixtyEightFJ_198620836529274167821908748839, phi_oneHundredSixtyEightFJ_198620836529274167821908748840, phi_oneHundredSixtyEightFJ_198620836529274167821908748841,
    phi_oneHundredSixtyEightFJ_198620836529274167821908748842, phi_oneHundredSixtyEightFJ_198620836529274167821908748843, phi_oneHundredSixtyEightFJ_198620836529274167821908748844,
    phi_oneHundredSixtyEightFJ_198620836529274167821908748845, phi_oneHundredSixtyEightFJ_198620836529274167821908748846, phi_oneHundredSixtyEightFJ_198620836529274167821908748847,
    phi_oneHundredSixtyEightFJ_198620836529274167821908748848, phi_oneHundredSixtyEightFJ_198620836529274167821908748849, phi_oneHundredSixtyEightFJ_198620836529274167821908748850,
    phi_oneHundredSixtyEightFJ_198620836529274167821908748851, phi_oneHundredSixtyEightFJ_198620836529274167821908748852, phi_oneHundredSixtyEightFJ_198620836529274167821908748853,
    phi_oneHundredSixtyEightFJ_198620836529274167821908748854, phi_oneHundredSixtyEightFJ_198620836529274167821908748855, phi_oneHundredSixtyEightFJ_198620836529274167821908748856,
    phi_oneHundredSixtyEightFJ_198620836529274167821908748857, phi_oneHundredSixtyEightFJ_198620836529274167821908748858, phi_oneHundredSixtyEightFJ_198620836529274167821908748859,
    phi_oneHundredSixtyEightFJ_198620836529274167821908748860, phi_oneHundredSixtyEightFJ_198620836529274167821908748861, phi_oneHundredSixtyEightFJ_198620836529274167821908748862,
    phi_oneHundredSixtyEightFJ_198620836529274167821908748863, phi_oneHundredSixtyEightFJ_198620836529274167821908748864, phi_oneHundredSixtyEightFJ_198620836529274167821908748865,
    phi_oneHundredSixtyEightFJ_198620836529274167821908748866, phi_oneHundredSixtyEightFJ_198620836529274167821908748867, phi_oneHundredSixtyEightFJ_198620836529274167821908748868,
    phi_oneHundredSixtyEightFJ_198620836529274167821908748869, phi_oneHundredSixtyEightFJ_198620836529274167821908748870, phi_oneHundredSixtyEightFJ_198620836529274167821908748871,
    phi_oneHundredSixtyEightFJ_198620836529274167821908748872, phi_oneHundredSixtyEightFJ_198620836529274167821908748873, phi_oneHundredSixtyEightFJ_198620836529274167821908748874,
    phi_oneHundredSixtyEightFJ_198620836529274167821908748875, phi_oneHundredSixtyEightFJ_198620836529274167821908748876, phi_oneHundredSixtyEightFJ_198620836529274167821908748877,
    phi_oneHundredSixtyEightFJ_198620836529274167821908748878, phi_oneHundredSixtyEightFJ_198620836529274167821908748879, phi_oneHundredSixtyEightFJ_198620836529274167821908748880,
    phi_oneHundredSixtyEightFJ_198620836529274167821908748881, phi_oneHundredSixtyEightFJ_198620836529274167821908748882, phi_oneHundredSixtyEightFJ_198620836529274167821908748883,
    phi_oneHundredSixtyEightFJ_198620836529274167821908748884, phi_oneHundredSixtyEightFJ_198620836529274167821908748885, phi_oneHundredSixtyEightFJ_198620836529274167821908748886,
    phi_oneHundredSixtyEightFJ_198620836529274167821908748887, phi_oneHundredSixtyEightFJ_198620836529274167821908748888, phi_oneHundredSixtyEightFJ_198620836529274167821908748889,
    phi_oneHundredSixtyEightFJ_198620836529274167821908748890, phi_oneHundredSixtyEightFJ_198620836529274167821908748891, phi_oneHundredSixtyEightFJ_198620836529274167821908748892,
    phi_oneHundredSixtyEightFJ_198620836529274167821908748893, phi_oneHundredSixtyEightFJ_198620836529274167821908748894, phi_oneHundredSixtyEightFJ_198620836529274167821908748895,
    phi_oneHundredSixtyEightFJ_198620836529274167821908748896, phi_oneHundredSixtyEightFJ_198620836529274167821908748897, phi_oneHundredSixtyEightFJ_198620836529274167821908748898,
    phi_oneHundredSixtyEightFJ_198620836529274167821908748899, phi_oneHundredSixtyEightFJ_198620836529274167821908748900, phi_oneHundredSixtyEightFJ_198620836529274167821908748901,
    phi_oneHundredSixtyEightFJ_198620836529274167821908748902, phi_oneHundredSixtyEightFJ_198620836529274167821908748903]

end TotientTailPeriodKiller
end Erdos249257
