import Erdos249257.DiagonalPincerCertificatesT64

/- Kernel-checked off-diagonal certificate at a freely chosen position. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def oneHundredFiftySixEXFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem oneHundredFiftySixEXFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : oneHundredFiftySixEXFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [oneHundredFiftySixEXFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [oneHundredFiftySixEXFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then oneHundredFiftySixEXFastPow a n * oneHundredFiftySixEXFastPow a n * a else oneHundredFiftySixEXFastPow a n * oneHundredFiftySixEXFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_oneHundredFiftySixEX_2 : Nat.Prime 2 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_3 : Nat.Prime 3 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_5 : Nat.Prime 5 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_7 : Nat.Prime 7 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_11 : Nat.Prime 11 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_13 : Nat.Prime 13 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_17 : Nat.Prime 17 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_19 : Nat.Prime 19 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_23 : Nat.Prime 23 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_29 : Nat.Prime 29 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_31 : Nat.Prime 31 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_37 : Nat.Prime 37 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_41 : Nat.Prime 41 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_43 : Nat.Prime 43 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_47 : Nat.Prime 47 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_53 : Nat.Prime 53 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_59 : Nat.Prime 59 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_61 : Nat.Prime 61 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_67 : Nat.Prime 67 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_71 : Nat.Prime 71 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_73 : Nat.Prime 73 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_79 : Nat.Prime 79 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_83 : Nat.Prime 83 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_89 : Nat.Prime 89 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_97 : Nat.Prime 97 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_101 : Nat.Prime 101 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_103 : Nat.Prime 103 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_107 : Nat.Prime 107 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_109 : Nat.Prime 109 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_113 : Nat.Prime 113 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_127 : Nat.Prime 127 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_131 : Nat.Prime 131 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_137 : Nat.Prime 137 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_139 : Nat.Prime 139 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_149 : Nat.Prime 149 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_151 : Nat.Prime 151 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_167 : Nat.Prime 167 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_173 : Nat.Prime 173 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_179 : Nat.Prime 179 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_191 : Nat.Prime 191 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_193 : Nat.Prime 193 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_197 : Nat.Prime 197 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_211 : Nat.Prime 211 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_223 : Nat.Prime 223 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_227 : Nat.Prime 227 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_229 : Nat.Prime 229 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_233 : Nat.Prime 233 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_239 : Nat.Prime 239 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_241 : Nat.Prime 241 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_251 : Nat.Prime 251 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_257 : Nat.Prime 257 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_263 : Nat.Prime 263 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_269 : Nat.Prime 269 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_271 : Nat.Prime 271 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_277 : Nat.Prime 277 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_281 : Nat.Prime 281 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_283 : Nat.Prime 283 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_293 : Nat.Prime 293 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_307 : Nat.Prime 307 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_311 : Nat.Prime 311 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_313 : Nat.Prime 313 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_317 : Nat.Prime 317 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_337 : Nat.Prime 337 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_347 : Nat.Prime 347 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_349 : Nat.Prime 349 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_353 : Nat.Prime 353 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_359 : Nat.Prime 359 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_373 : Nat.Prime 373 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_379 : Nat.Prime 379 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_389 : Nat.Prime 389 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_401 : Nat.Prime 401 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_419 : Nat.Prime 419 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_421 : Nat.Prime 421 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_431 : Nat.Prime 431 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_433 : Nat.Prime 433 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_439 : Nat.Prime 439 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_443 : Nat.Prime 443 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_457 : Nat.Prime 457 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_461 : Nat.Prime 461 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_487 : Nat.Prime 487 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_491 : Nat.Prime 491 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_499 : Nat.Prime 499 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_503 : Nat.Prime 503 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_509 : Nat.Prime 509 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_523 : Nat.Prime 523 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_557 : Nat.Prime 557 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_569 : Nat.Prime 569 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_587 : Nat.Prime 587 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_619 : Nat.Prime 619 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_631 : Nat.Prime 631 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_643 : Nat.Prime 643 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_653 : Nat.Prime 653 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_691 : Nat.Prime 691 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_701 : Nat.Prime 701 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_769 : Nat.Prime 769 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_773 : Nat.Prime 773 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_797 : Nat.Prime 797 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_821 : Nat.Prime 821 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_827 : Nat.Prime 827 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_829 : Nat.Prime 829 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_883 : Nat.Prime 883 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_911 : Nat.Prime 911 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_919 : Nat.Prime 919 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_947 : Nat.Prime 947 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_967 : Nat.Prime 967 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_971 : Nat.Prime 971 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_1049 : Nat.Prime 1049 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_1051 : Nat.Prime 1051 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_1093 : Nat.Prime 1093 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_1097 : Nat.Prime 1097 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_1103 : Nat.Prime 1103 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_1109 : Nat.Prime 1109 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_1151 : Nat.Prime 1151 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_1153 : Nat.Prime 1153 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_1223 : Nat.Prime 1223 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_1259 : Nat.Prime 1259 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_1279 : Nat.Prime 1279 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_1283 : Nat.Prime 1283 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_1289 : Nat.Prime 1289 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_1301 : Nat.Prime 1301 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_1367 : Nat.Prime 1367 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_1381 : Nat.Prime 1381 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_1423 : Nat.Prime 1423 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_1427 : Nat.Prime 1427 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_1439 : Nat.Prime 1439 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_1447 : Nat.Prime 1447 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_1499 : Nat.Prime 1499 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_1583 : Nat.Prime 1583 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_1601 : Nat.Prime 1601 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_1613 : Nat.Prime 1613 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_1721 : Nat.Prime 1721 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_1741 : Nat.Prime 1741 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_1789 : Nat.Prime 1789 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_1811 : Nat.Prime 1811 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_1831 : Nat.Prime 1831 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_1877 : Nat.Prime 1877 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_1997 : Nat.Prime 1997 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_2011 : Nat.Prime 2011 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_2081 : Nat.Prime 2081 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_2129 : Nat.Prime 2129 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_2153 : Nat.Prime 2153 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_2179 : Nat.Prime 2179 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_2293 : Nat.Prime 2293 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_2297 : Nat.Prime 2297 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_2309 : Nat.Prime 2309 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_2357 : Nat.Prime 2357 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_2399 : Nat.Prime 2399 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_2617 : Nat.Prime 2617 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_2663 : Nat.Prime 2663 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_2671 : Nat.Prime 2671 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_2693 : Nat.Prime 2693 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_2767 : Nat.Prime 2767 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_2777 : Nat.Prime 2777 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_2909 : Nat.Prime 2909 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_2969 : Nat.Prime 2969 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_3001 : Nat.Prime 3001 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_3373 : Nat.Prime 3373 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_3727 : Nat.Prime 3727 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_3739 : Nat.Prime 3739 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_3803 : Nat.Prime 3803 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_3823 : Nat.Prime 3823 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_3851 : Nat.Prime 3851 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_4019 : Nat.Prime 4019 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_4027 : Nat.Prime 4027 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_4211 : Nat.Prime 4211 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_4241 : Nat.Prime 4241 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_4253 : Nat.Prime 4253 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_4271 : Nat.Prime 4271 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_4273 : Nat.Prime 4273 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_4363 : Nat.Prime 4363 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_4423 : Nat.Prime 4423 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_4463 : Nat.Prime 4463 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_4567 : Nat.Prime 4567 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_4603 : Nat.Prime 4603 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_4691 : Nat.Prime 4691 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_4733 : Nat.Prime 4733 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_4969 : Nat.Prime 4969 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_5009 : Nat.Prime 5009 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_5087 : Nat.Prime 5087 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_5333 : Nat.Prime 5333 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_5503 : Nat.Prime 5503 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_5527 : Nat.Prime 5527 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_5591 : Nat.Prime 5591 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_6323 : Nat.Prime 6323 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_6491 : Nat.Prime 6491 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_6709 : Nat.Prime 6709 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_6863 : Nat.Prime 6863 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_7057 : Nat.Prime 7057 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_7247 : Nat.Prime 7247 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_7309 : Nat.Prime 7309 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_7351 : Nat.Prime 7351 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_7561 : Nat.Prime 7561 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_7583 : Nat.Prime 7583 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_7919 : Nat.Prime 7919 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_8273 : Nat.Prime 8273 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_8521 : Nat.Prime 8521 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_8819 : Nat.Prime 8819 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_9187 : Nat.Prime 9187 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_9719 : Nat.Prime 9719 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_9829 : Nat.Prime 9829 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_9967 : Nat.Prime 9967 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_9973 : Nat.Prime 9973 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_10093 : Nat.Prime 10093 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_10163 : Nat.Prime 10163 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_10531 : Nat.Prime 10531 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_10789 : Nat.Prime 10789 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_11467 : Nat.Prime 11467 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_12073 : Nat.Prime 12073 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_12281 : Nat.Prime 12281 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_12343 : Nat.Prime 12343 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_13411 : Nat.Prime 13411 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_13729 : Nat.Prime 13729 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_13921 : Nat.Prime 13921 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_14051 : Nat.Prime 14051 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_14107 : Nat.Prime 14107 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_15091 : Nat.Prime 15091 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_15199 : Nat.Prime 15199 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_15373 : Nat.Prime 15373 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_15809 : Nat.Prime 15809 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_15817 : Nat.Prime 15817 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_15901 : Nat.Prime 15901 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_16417 : Nat.Prime 16417 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_16943 : Nat.Prime 16943 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_17203 : Nat.Prime 17203 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_17483 : Nat.Prime 17483 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_17683 : Nat.Prime 17683 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_17707 : Nat.Prime 17707 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_17903 : Nat.Prime 17903 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_17977 : Nat.Prime 17977 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_18341 : Nat.Prime 18341 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_18371 : Nat.Prime 18371 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_19469 : Nat.Prime 19469 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_20261 : Nat.Prime 20261 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_20753 : Nat.Prime 20753 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_21617 : Nat.Prime 21617 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_22469 : Nat.Prime 22469 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_23447 : Nat.Prime 23447 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_23581 : Nat.Prime 23581 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_23627 : Nat.Prime 23627 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_23719 : Nat.Prime 23719 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_23833 : Nat.Prime 23833 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_25117 : Nat.Prime 25117 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_28607 : Nat.Prime 28607 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_28729 : Nat.Prime 28729 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_31177 : Nat.Prime 31177 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_31547 : Nat.Prime 31547 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_32531 : Nat.Prime 32531 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_33617 : Nat.Prime 33617 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_34217 : Nat.Prime 34217 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_34981 : Nat.Prime 34981 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_37123 : Nat.Prime 37123 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_37573 : Nat.Prime 37573 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_38333 : Nat.Prime 38333 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_40763 : Nat.Prime 40763 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_41513 : Nat.Prime 41513 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_43291 : Nat.Prime 43291 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_47981 : Nat.Prime 47981 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_48017 : Nat.Prime 48017 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_50287 : Nat.Prime 50287 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_51361 : Nat.Prime 51361 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_51503 : Nat.Prime 51503 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_52757 : Nat.Prime 52757 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_53597 : Nat.Prime 53597 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_53897 : Nat.Prime 53897 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_54419 : Nat.Prime 54419 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_55351 : Nat.Prime 55351 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_55799 : Nat.Prime 55799 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_57397 : Nat.Prime 57397 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_59887 : Nat.Prime 59887 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_62039 : Nat.Prime 62039 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_62969 : Nat.Prime 62969 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_63901 : Nat.Prime 63901 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_65609 : Nat.Prime 65609 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_65837 : Nat.Prime 65837 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_66239 : Nat.Prime 66239 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_66377 : Nat.Prime 66377 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_69997 : Nat.Prime 69997 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_71119 : Nat.Prime 71119 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_71171 : Nat.Prime 71171 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_71473 : Nat.Prime 71473 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_75269 : Nat.Prime 75269 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_75329 : Nat.Prime 75329 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_77933 : Nat.Prime 77933 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_88423 : Nat.Prime 88423 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_88873 : Nat.Prime 88873 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_95279 : Nat.Prime 95279 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_96601 : Nat.Prime 96601 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_110119 : Nat.Prime 110119 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_113017 : Nat.Prime 113017 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_114001 : Nat.Prime 114001 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_119237 : Nat.Prime 119237 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_119929 : Nat.Prime 119929 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_120619 : Nat.Prime 120619 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_121661 : Nat.Prime 121661 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_121721 : Nat.Prime 121721 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_124847 : Nat.Prime 124847 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_125287 : Nat.Prime 125287 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_125753 : Nat.Prime 125753 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_125791 : Nat.Prime 125791 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_129001 : Nat.Prime 129001 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_134171 : Nat.Prime 134171 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_136849 : Nat.Prime 136849 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_139409 : Nat.Prime 139409 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_160183 : Nat.Prime 160183 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_160969 : Nat.Prime 160969 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_169003 : Nat.Prime 169003 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_171251 : Nat.Prime 171251 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_171401 : Nat.Prime 171401 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_172313 : Nat.Prime 172313 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_187843 : Nat.Prime 187843 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_188459 : Nat.Prime 188459 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_201211 : Nat.Prime 201211 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_201743 : Nat.Prime 201743 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_208387 : Nat.Prime 208387 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_220589 : Nat.Prime 220589 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_221587 : Nat.Prime 221587 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_226777 : Nat.Prime 226777 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_235013 : Nat.Prime 235013 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_237467 : Nat.Prime 237467 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_238531 : Nat.Prime 238531 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_241817 : Nat.Prime 241817 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_245299 : Nat.Prime 245299 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_251897 : Nat.Prime 251897 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_256211 : Nat.Prime 256211 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_265261 : Nat.Prime 265261 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_266009 : Nat.Prime 266009 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_271769 : Nat.Prime 271769 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_296773 : Nat.Prime 296773 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_310901 : Nat.Prime 310901 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_320401 : Nat.Prime 320401 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_321187 : Nat.Prime 321187 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_321911 : Nat.Prime 321911 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_325411 : Nat.Prime 325411 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_327289 : Nat.Prime 327289 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_346417 : Nat.Prime 346417 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_351991 : Nat.Prime 351991 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_355027 : Nat.Prime 355027 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_357817 : Nat.Prime 357817 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_362027 : Nat.Prime 362027 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_374317 : Nat.Prime 374317 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_392423 : Nat.Prime 392423 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_398341 : Nat.Prime 398341 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_404017 : Nat.Prime 404017 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_428173 : Nat.Prime 428173 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_430739 : Nat.Prime 430739 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_446921 : Nat.Prime 446921 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_460711 : Nat.Prime 460711 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_471139 : Nat.Prime 471139 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_477013 : Nat.Prime 477013 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_508271 : Nat.Prime 508271 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_517721 : Nat.Prime 517721 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_542537 : Nat.Prime 542537 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_555671 : Nat.Prime 555671 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_555697 : Nat.Prime 555697 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_569507 : Nat.Prime 569507 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_572549 : Nat.Prime 572549 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_591391 : Nat.Prime 591391 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_596159 : Nat.Prime 596159 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_598777 : Nat.Prime 598777 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_624089 : Nat.Prime 624089 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_632221 : Nat.Prime 632221 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_678593 : Nat.Prime 678593 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_694717 : Nat.Prime 694717 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_747139 : Nat.Prime 747139 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_767537 : Nat.Prime 767537 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_781631 : Nat.Prime 781631 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_921517 : Nat.Prime 921517 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_925291 : Nat.Prime 925291 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_965749 : Nat.Prime 965749 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_973373 : Nat.Prime 973373 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_1006301 : Nat.Prime 1006301 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_1050509 : Nat.Prime 1050509 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_1129187 : Nat.Prime 1129187 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_1171967 : Nat.Prime 1171967 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_1214749 : Nat.Prime 1214749 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_1342567 : Nat.Prime 1342567 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_1446257 : Nat.Prime 1446257 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_1473061 : Nat.Prime 1473061 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_1617523 : Nat.Prime 1617523 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_1650673 : Nat.Prime 1650673 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_1727563 : Nat.Prime 1727563 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_1745927 : Nat.Prime 1745927 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_1781359 : Nat.Prime 1781359 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_1871339 : Nat.Prime 1871339 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_1899659 : Nat.Prime 1899659 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_1901651 : Nat.Prime 1901651 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_2017409 : Nat.Prime 2017409 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_2353297 : Nat.Prime 2353297 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_2450593 : Nat.Prime 2450593 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_2484311 : Nat.Prime 2484311 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_2532919 : Nat.Prime 2532919 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_2535473 : Nat.Prime 2535473 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_2551429 : Nat.Prime 2551429 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_2677099 : Nat.Prime 2677099 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_2976643 : Nat.Prime 2976643 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_3059143 : Nat.Prime 3059143 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_3227281 : Nat.Prime 3227281 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_3231313 : Nat.Prime 3231313 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_3378589 : Nat.Prime 3378589 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_3463319 : Nat.Prime 3463319 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_3473849 : Nat.Prime 3473849 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_3638827 : Nat.Prime 3638827 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_3703267 : Nat.Prime 3703267 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_3813401 : Nat.Prime 3813401 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_4273343 : Nat.Prime 4273343 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_4906547 : Nat.Prime 4906547 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_5202511 : Nat.Prime 5202511 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_5285263 : Nat.Prime 5285263 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_5345317 : Nat.Prime 5345317 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_5843287 : Nat.Prime 5843287 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_6224681 : Nat.Prime 6224681 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_6313019 : Nat.Prime 6313019 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_6336347 : Nat.Prime 6336347 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_6931649 : Nat.Prime 6931649 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_7389959 : Nat.Prime 7389959 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_7631857 : Nat.Prime 7631857 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_7760507 : Nat.Prime 7760507 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_8302403 : Nat.Prime 8302403 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_8485681 : Nat.Prime 8485681 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_8532299 : Nat.Prime 8532299 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_9813527 : Nat.Prime 9813527 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_9890501 : Nat.Prime 9890501 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_10071353 : Nat.Prime 10071353 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_10117339 : Nat.Prime 10117339 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_10320283 : Nat.Prime 10320283 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_10399843 : Nat.Prime 10399843 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_10820141 : Nat.Prime 10820141 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_11622449 : Nat.Prime 11622449 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_12040139 : Nat.Prime 12040139 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_14201963 : Nat.Prime 14201963 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_14341337 : Nat.Prime 14341337 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_14692609 : Nat.Prime 14692609 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_15054001 : Nat.Prime 15054001 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_15425269 : Nat.Prime 15425269 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_15628141 : Nat.Prime 15628141 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_16411201 : Nat.Prime 16411201 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_18100919 : Nat.Prime 18100919 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_18101393 : Nat.Prime 18101393 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_19297753 : Nat.Prime 19297753 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_19796807 : Nat.Prime 19796807 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_19916623 : Nat.Prime 19916623 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_19952099 : Nat.Prime 19952099 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_21724111 : Nat.Prime 21724111 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_21937549 : Nat.Prime 21937549 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_22284553 : Nat.Prime 22284553 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_23081273 : Nat.Prime 23081273 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_24108629 : Nat.Prime 24108629 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_24338467 : Nat.Prime 24338467 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_24366007 : Nat.Prime 24366007 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_25356953 : Nat.Prime 25356953 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_29567803 : Nat.Prime 29567803 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_29772199 : Nat.Prime 29772199 := by
  norm_num

private theorem prime_oneHundredFiftySixEX_32084053 : Nat.Prime 32084053 := by
  apply lucas_primality 32084053 (2 : ZMod 32084053)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (11, 1), (13, 1), (2671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (11, 1), (13, 1), (2671, 1)] : List FactorBlock).map factorBlockValue).prod) = 32084053 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_7
      · exact prime_oneHundredFiftySixEX_11
      · exact prime_oneHundredFiftySixEX_13
      · exact prime_oneHundredFiftySixEX_2671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 32084053) ^ 16042026 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 32084053) ^ 10694684 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 32084053) ^ 4583436 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 32084053) ^ 2916732 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 32084053) ^ 2468004 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 32084053) ^ 12012 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_32210527 : Nat.Prime 32210527 := by
  apply lucas_primality 32210527 (3 : ZMod 32210527)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (43, 1), (124847, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (43, 1), (124847, 1)] : List FactorBlock).map factorBlockValue).prod) = 32210527 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_43
      · exact prime_oneHundredFiftySixEX_124847
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 32210527) ^ 16105263 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 32210527) ^ 10736842 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 32210527) ^ 749082 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 32210527) ^ 258 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_35410211 : Nat.Prime 35410211 := by
  apply lucas_primality 35410211 (2 : ZMod 35410211)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (321911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (321911, 1)] : List FactorBlock).map factorBlockValue).prod) = 35410211 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_5
      · exact prime_oneHundredFiftySixEX_11
      · exact prime_oneHundredFiftySixEX_321911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 35410211) ^ 17705105 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 35410211) ^ 7082042 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 35410211) ^ 3219110 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 35410211) ^ 110 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_37910053 : Nat.Prime 37910053 := by
  apply lucas_primality 37910053 (5 : ZMod 37910053)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (37, 1), (53, 1), (179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (37, 1), (53, 1), (179, 1)] : List FactorBlock).map factorBlockValue).prod) = 37910053 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_37
      · exact prime_oneHundredFiftySixEX_53
      · exact prime_oneHundredFiftySixEX_179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 37910053) ^ 18955026 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 37910053) ^ 12636684 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 37910053) ^ 1024596 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 37910053) ^ 715284 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 37910053) ^ 211788 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_38398499 : Nat.Prime 38398499 := by
  apply lucas_primality 38398499 (2 : ZMod 38398499)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (59, 1), (325411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (59, 1), (325411, 1)] : List FactorBlock).map factorBlockValue).prod) = 38398499 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_59
      · exact prime_oneHundredFiftySixEX_325411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 38398499) ^ 19199249 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 38398499) ^ 650822 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 38398499) ^ 118 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_39880429 : Nat.Prime 39880429 := by
  apply lucas_primality 39880429 (2 : ZMod 39880429)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (223, 1), (2129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (223, 1), (2129, 1)] : List FactorBlock).map factorBlockValue).prod) = 39880429 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_7
      · exact prime_oneHundredFiftySixEX_223
      · exact prime_oneHundredFiftySixEX_2129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 39880429) ^ 19940214 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 39880429) ^ 13293476 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 39880429) ^ 5697204 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 39880429) ^ 178836 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 39880429) ^ 18732 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_47508173 : Nat.Prime 47508173 := by
  apply lucas_primality 47508173 (2 : ZMod 47508173)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (701, 1), (16943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (701, 1), (16943, 1)] : List FactorBlock).map factorBlockValue).prod) = 47508173 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_701
      · exact prime_oneHundredFiftySixEX_16943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 47508173) ^ 23754086 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 47508173) ^ 67772 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 47508173) ^ 2804 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_52025111 : Nat.Prime 52025111 := by
  apply lucas_primality 52025111 (13 : ZMod 52025111)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (5202511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (5202511, 1)] : List FactorBlock).map factorBlockValue).prod) = 52025111 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_5
      · exact prime_oneHundredFiftySixEX_5202511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 52025111) ^ 26012555 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (13 : ZMod 52025111) ^ 10405022 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (13 : ZMod 52025111) ^ 10 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_59223277 : Nat.Prime 59223277 := by
  apply lucas_primality 59223277 (2 : ZMod 59223277)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (235013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (235013, 1)] : List FactorBlock).map factorBlockValue).prod) = 59223277 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_7
      · exact prime_oneHundredFiftySixEX_235013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 59223277) ^ 29611638 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 59223277) ^ 19741092 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 59223277) ^ 8460468 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 59223277) ^ 252 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_59899309 : Nat.Prime 59899309 := by
  apply lucas_primality 59899309 (11 : ZMod 59899309)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (643, 1), (1109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (643, 1), (1109, 1)] : List FactorBlock).map factorBlockValue).prod) = 59899309 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_7
      · exact prime_oneHundredFiftySixEX_643
      · exact prime_oneHundredFiftySixEX_1109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 59899309) ^ 29949654 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (11 : ZMod 59899309) ^ 19966436 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (11 : ZMod 59899309) ^ 8557044 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (11 : ZMod 59899309) ^ 93156 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (11 : ZMod 59899309) ^ 54012 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_59929613 : Nat.Prime 59929613 := by
  apply lucas_primality 59929613 (2 : ZMod 59929613)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1811, 1), (8273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1811, 1), (8273, 1)] : List FactorBlock).map factorBlockValue).prod) = 59929613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_1811
      · exact prime_oneHundredFiftySixEX_8273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 59929613) ^ 29964806 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 59929613) ^ 33092 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 59929613) ^ 7244 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_60081907 : Nat.Prime 60081907 := by
  apply lucas_primality 60081907 (5 : ZMod 60081907)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (227, 1), (1423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (227, 1), (1423, 1)] : List FactorBlock).map factorBlockValue).prod) = 60081907 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_31
      · exact prime_oneHundredFiftySixEX_227
      · exact prime_oneHundredFiftySixEX_1423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 60081907) ^ 30040953 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 60081907) ^ 20027302 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 60081907) ^ 1938126 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 60081907) ^ 264678 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 60081907) ^ 42222 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_60378061 : Nat.Prime 60378061 := by
  apply lucas_primality 60378061 (2 : ZMod 60378061)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (1006301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (1006301, 1)] : List FactorBlock).map factorBlockValue).prod) = 60378061 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_5
      · exact prime_oneHundredFiftySixEX_1006301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 60378061) ^ 30189030 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 60378061) ^ 20126020 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 60378061) ^ 12075612 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 60378061) ^ 60 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_61908677 : Nat.Prime 61908677 := by
  apply lucas_primality 61908677 (2 : ZMod 61908677)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3851, 1), (4019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3851, 1), (4019, 1)] : List FactorBlock).map factorBlockValue).prod) = 61908677 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3851
      · exact prime_oneHundredFiftySixEX_4019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 61908677) ^ 30954338 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 61908677) ^ 16076 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 61908677) ^ 15404 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_62402203 : Nat.Prime 62402203 := by
  apply lucas_primality 62402203 (3 : ZMod 62402203)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (37, 1), (43, 1), (2179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (37, 1), (43, 1), (2179, 1)] : List FactorBlock).map factorBlockValue).prod) = 62402203 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_37
      · exact prime_oneHundredFiftySixEX_43
      · exact prime_oneHundredFiftySixEX_2179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 62402203) ^ 31201101 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 62402203) ^ 20800734 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 62402203) ^ 1686546 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 62402203) ^ 1451214 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 62402203) ^ 28638 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_68744369 : Nat.Prime 68744369 := by
  apply lucas_primality 68744369 (6 : ZMod 68744369)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (11, 1), (55799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (11, 1), (55799, 1)] : List FactorBlock).map factorBlockValue).prod) = 68744369 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_7
      · exact prime_oneHundredFiftySixEX_11
      · exact prime_oneHundredFiftySixEX_55799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 68744369) ^ 34372184 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 68744369) ^ 9820624 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 68744369) ^ 6249488 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 68744369) ^ 1232 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_69337351 : Nat.Prime 69337351 := by
  apply lucas_primality 69337351 (6 : ZMod 69337351)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 2), (51361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 2), (51361, 1)] : List FactorBlock).map factorBlockValue).prod) = 69337351 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_5
      · exact prime_oneHundredFiftySixEX_51361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 69337351) ^ 34668675 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 69337351) ^ 23112450 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 69337351) ^ 13867470 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 69337351) ^ 1350 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_74696173 : Nat.Prime 74696173 := by
  apply lucas_primality 74696173 (5 : ZMod 74696173)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (6224681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (6224681, 1)] : List FactorBlock).map factorBlockValue).prod) = 74696173 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_6224681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 74696173) ^ 37348086 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 74696173) ^ 24898724 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 74696173) ^ 12 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_74913961 : Nat.Prime 74913961 := by
  apply lucas_primality 74913961 (13 : ZMod 74913961)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (11, 1), (19, 1), (29, 1), (103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (11, 1), (19, 1), (29, 1), (103, 1)] : List FactorBlock).map factorBlockValue).prod) = 74913961 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_5
      · exact prime_oneHundredFiftySixEX_11
      · exact prime_oneHundredFiftySixEX_19
      · exact prime_oneHundredFiftySixEX_29
      · exact prime_oneHundredFiftySixEX_103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 74913961) ^ 37456980 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (13 : ZMod 74913961) ^ 24971320 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (13 : ZMod 74913961) ^ 14982792 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (13 : ZMod 74913961) ^ 6810360 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (13 : ZMod 74913961) ^ 3942840 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (13 : ZMod 74913961) ^ 2583240 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (13 : ZMod 74913961) ^ 727320 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_82284739 : Nat.Prime 82284739 := by
  apply lucas_primality 82284739 (2 : ZMod 82284739)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (229, 1), (59887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (229, 1), (59887, 1)] : List FactorBlock).map factorBlockValue).prod) = 82284739 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_229
      · exact prime_oneHundredFiftySixEX_59887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 82284739) ^ 41142369 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 82284739) ^ 27428246 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 82284739) ^ 359322 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 82284739) ^ 1374 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_85398031 : Nat.Prime 85398031 := by
  apply lucas_primality 85398031 (6 : ZMod 85398031)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (211, 1), (1499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (211, 1), (1499, 1)] : List FactorBlock).map factorBlockValue).prod) = 85398031 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_5
      · exact prime_oneHundredFiftySixEX_211
      · exact prime_oneHundredFiftySixEX_1499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 85398031) ^ 42699015 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 85398031) ^ 28466010 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 85398031) ^ 17079606 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 85398031) ^ 404730 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 85398031) ^ 56970 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_88875769 : Nat.Prime 88875769 := by
  apply lucas_primality 88875769 (7 : ZMod 88875769)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (19, 1), (67, 1), (2909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (19, 1), (67, 1), (2909, 1)] : List FactorBlock).map factorBlockValue).prod) = 88875769 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_19
      · exact prime_oneHundredFiftySixEX_67
      · exact prime_oneHundredFiftySixEX_2909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 88875769) ^ 44437884 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (7 : ZMod 88875769) ^ 29625256 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (7 : ZMod 88875769) ^ 4677672 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (7 : ZMod 88875769) ^ 1326504 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (7 : ZMod 88875769) ^ 30552 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_95016347 : Nat.Prime 95016347 := by
  apply lucas_primality 95016347 (2 : ZMod 95016347)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47508173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47508173, 1)] : List FactorBlock).map factorBlockValue).prod) = 95016347 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_47508173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 95016347) ^ 47508173 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 95016347) ^ 2 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_102534983 : Nat.Prime 102534983 := by
  apply lucas_primality 102534983 (5 : ZMod 102534983)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (19, 1), (245299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (19, 1), (245299, 1)] : List FactorBlock).map factorBlockValue).prod) = 102534983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_11
      · exact prime_oneHundredFiftySixEX_19
      · exact prime_oneHundredFiftySixEX_245299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 102534983) ^ 51267491 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 102534983) ^ 9321362 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 102534983) ^ 5396578 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 102534983) ^ 418 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_104050223 : Nat.Prime 104050223 := by
  apply lucas_primality 104050223 (5 : ZMod 104050223)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (52025111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (52025111, 1)] : List FactorBlock).map factorBlockValue).prod) = 104050223 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_52025111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 104050223) ^ 52025111 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 104050223) ^ 2 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_115555991 : Nat.Prime 115555991 := by
  apply lucas_primality 115555991 (11 : ZMod 115555991)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (1050509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (1050509, 1)] : List FactorBlock).map factorBlockValue).prod) = 115555991 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_5
      · exact prime_oneHundredFiftySixEX_11
      · exact prime_oneHundredFiftySixEX_1050509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 115555991) ^ 57777995 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (11 : ZMod 115555991) ^ 23111198 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (11 : ZMod 115555991) ^ 10505090 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (11 : ZMod 115555991) ^ 110 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_142641539 : Nat.Prime 142641539 := by
  apply lucas_primality 142641539 (2 : ZMod 142641539)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (23, 1), (238531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (23, 1), (238531, 1)] : List FactorBlock).map factorBlockValue).prod) = 142641539 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_13
      · exact prime_oneHundredFiftySixEX_23
      · exact prime_oneHundredFiftySixEX_238531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 142641539) ^ 71320769 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 142641539) ^ 10972426 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 142641539) ^ 6201806 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 142641539) ^ 598 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_146030803 : Nat.Prime 146030803 := by
  apply lucas_primality 146030803 (3 : ZMod 146030803)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (24338467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (24338467, 1)] : List FactorBlock).map factorBlockValue).prod) = 146030803 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_24338467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 146030803) ^ 73015401 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 146030803) ^ 48676934 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 146030803) ^ 6 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_146675273 : Nat.Prime 146675273 := by
  apply lucas_primality 146675273 (3 : ZMod 146675273)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (29, 1), (632221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (29, 1), (632221, 1)] : List FactorBlock).map factorBlockValue).prod) = 146675273 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_29
      · exact prime_oneHundredFiftySixEX_632221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 146675273) ^ 73337636 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 146675273) ^ 5057768 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 146675273) ^ 232 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_151640213 : Nat.Prime 151640213 := by
  apply lucas_primality 151640213 (2 : ZMod 151640213)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (37910053, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (37910053, 1)] : List FactorBlock).map factorBlockValue).prod) = 151640213 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_37910053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 151640213) ^ 75820106 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 151640213) ^ 4 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_153773531 : Nat.Prime 153773531 := by
  apply lucas_primality 153773531 (2 : ZMod 153773531)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (179, 1), (271, 1), (317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (179, 1), (271, 1), (317, 1)] : List FactorBlock).map factorBlockValue).prod) = 153773531 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_5
      · exact prime_oneHundredFiftySixEX_179
      · exact prime_oneHundredFiftySixEX_271
      · exact prime_oneHundredFiftySixEX_317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 153773531) ^ 76886765 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 153773531) ^ 30754706 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 153773531) ^ 859070 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 153773531) ^ 567430 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 153773531) ^ 485090 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_182112103 : Nat.Prime 182112103 := by
  apply lucas_primality 182112103 (5 : ZMod 182112103)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (10117339, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (10117339, 1)] : List FactorBlock).map factorBlockValue).prod) = 182112103 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_10117339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 182112103) ^ 91056051 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 182112103) ^ 60704034 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 182112103) ^ 18 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_185423809 : Nat.Prime 185423809 := by
  apply lucas_primality 185423809 (11 : ZMod 185423809)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (965749, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (965749, 1)] : List FactorBlock).map factorBlockValue).prod) = 185423809 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_965749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 185423809) ^ 92711904 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (11 : ZMod 185423809) ^ 61807936 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (11 : ZMod 185423809) ^ 192 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_196906361 : Nat.Prime 196906361 := by
  apply lucas_primality 196906361 (3 : ZMod 196906361)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (7, 1), (167, 1), (4211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (7, 1), (167, 1), (4211, 1)] : List FactorBlock).map factorBlockValue).prod) = 196906361 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_5
      · exact prime_oneHundredFiftySixEX_7
      · exact prime_oneHundredFiftySixEX_167
      · exact prime_oneHundredFiftySixEX_4211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 196906361) ^ 98453180 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 196906361) ^ 39381272 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 196906361) ^ 28129480 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 196906361) ^ 1179080 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 196906361) ^ 46760 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_213150073 : Nat.Prime 213150073 := by
  apply lucas_primality 213150073 (5 : ZMod 213150073)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (73, 1), (121661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (73, 1), (121661, 1)] : List FactorBlock).map factorBlockValue).prod) = 213150073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_73
      · exact prime_oneHundredFiftySixEX_121661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 213150073) ^ 106575036 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 213150073) ^ 71050024 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 213150073) ^ 2919864 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 213150073) ^ 1752 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_220888517 : Nat.Prime 220888517 := by
  apply lucas_primality 220888517 (2 : ZMod 220888517)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (31, 1), (1781359, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (31, 1), (1781359, 1)] : List FactorBlock).map factorBlockValue).prod) = 220888517 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_31
      · exact prime_oneHundredFiftySixEX_1781359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 220888517) ^ 110444258 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 220888517) ^ 7125436 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 220888517) ^ 124 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_230703019 : Nat.Prime 230703019 := by
  apply lucas_primality 230703019 (3 : ZMod 230703019)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (13, 1), (23, 1), (18371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (13, 1), (23, 1), (18371, 1)] : List FactorBlock).map factorBlockValue).prod) = 230703019 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_7
      · exact prime_oneHundredFiftySixEX_13
      · exact prime_oneHundredFiftySixEX_23
      · exact prime_oneHundredFiftySixEX_18371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 230703019) ^ 115351509 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 230703019) ^ 76901006 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 230703019) ^ 32957574 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 230703019) ^ 17746386 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 230703019) ^ 10030566 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 230703019) ^ 12558 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_284376793 : Nat.Prime 284376793 := by
  apply lucas_primality 284376793 (5 : ZMod 284376793)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 2), (241817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 2), (241817, 1)] : List FactorBlock).map factorBlockValue).prod) = 284376793 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_7
      · exact prime_oneHundredFiftySixEX_241817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 284376793) ^ 142188396 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 284376793) ^ 94792264 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 284376793) ^ 40625256 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 284376793) ^ 1176 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_285501439 : Nat.Prime 285501439 := by
  apply lucas_primality 285501439 (13 : ZMod 285501439)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (23, 1), (151, 1), (4567, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (23, 1), (151, 1), (4567, 1)] : List FactorBlock).map factorBlockValue).prod) = 285501439 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_23
      · exact prime_oneHundredFiftySixEX_151
      · exact prime_oneHundredFiftySixEX_4567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 285501439) ^ 142750719 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (13 : ZMod 285501439) ^ 95167146 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (13 : ZMod 285501439) ^ 12413106 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (13 : ZMod 285501439) ^ 1890738 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (13 : ZMod 285501439) ^ 62514 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_295456519 : Nat.Prime 295456519 := by
  apply lucas_primality 295456519 (6 : ZMod 295456519)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 1), (781631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 1), (781631, 1)] : List FactorBlock).map factorBlockValue).prod) = 295456519 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_7
      · exact prime_oneHundredFiftySixEX_781631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 295456519) ^ 147728259 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 295456519) ^ 98485506 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 295456519) ^ 42208074 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 295456519) ^ 378 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_300595963 : Nat.Prime 300595963 := by
  apply lucas_primality 300595963 (2 : ZMod 300595963)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 1), (1727563, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 1), (1727563, 1)] : List FactorBlock).map factorBlockValue).prod) = 300595963 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_29
      · exact prime_oneHundredFiftySixEX_1727563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 300595963) ^ 150297981 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 300595963) ^ 100198654 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 300595963) ^ 10365378 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 300595963) ^ 174 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_338070989 : Nat.Prime 338070989 := by
  apply lucas_primality 338070989 (3 : ZMod 338070989)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (43, 1), (419, 1), (4691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (43, 1), (419, 1), (4691, 1)] : List FactorBlock).map factorBlockValue).prod) = 338070989 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_43
      · exact prime_oneHundredFiftySixEX_419
      · exact prime_oneHundredFiftySixEX_4691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 338070989) ^ 169035494 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 338070989) ^ 7862116 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 338070989) ^ 806852 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 338070989) ^ 72068 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_349996873 : Nat.Prime 349996873 := by
  apply lucas_primality 349996873 (11 : ZMod 349996873)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (19, 1), (767537, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (19, 1), (767537, 1)] : List FactorBlock).map factorBlockValue).prod) = 349996873 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_19
      · exact prime_oneHundredFiftySixEX_767537
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 349996873) ^ 174998436 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (11 : ZMod 349996873) ^ 116665624 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (11 : ZMod 349996873) ^ 18420888 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (11 : ZMod 349996873) ^ 456 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_371422451 : Nat.Prime 371422451 := by
  apply lucas_primality 371422451 (6 : ZMod 371422451)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (7, 2), (19, 1), (79, 1), (101, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (7, 2), (19, 1), (79, 1), (101, 1)] : List FactorBlock).map factorBlockValue).prod) = 371422451 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_5
      · exact prime_oneHundredFiftySixEX_7
      · exact prime_oneHundredFiftySixEX_19
      · exact prime_oneHundredFiftySixEX_79
      · exact prime_oneHundredFiftySixEX_101
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 371422451) ^ 185711225 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 371422451) ^ 74284490 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 371422451) ^ 53060350 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 371422451) ^ 19548550 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 371422451) ^ 4701550 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 371422451) ^ 3677450 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_429543953 : Nat.Prime 429543953 := by
  apply lucas_primality 429543953 (3 : ZMod 429543953)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (23, 1), (37, 1), (31547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (23, 1), (37, 1), (31547, 1)] : List FactorBlock).map factorBlockValue).prod) = 429543953 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_23
      · exact prime_oneHundredFiftySixEX_37
      · exact prime_oneHundredFiftySixEX_31547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 429543953) ^ 214771976 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 429543953) ^ 18675824 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 429543953) ^ 11609296 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 429543953) ^ 13616 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_433955323 : Nat.Prime 433955323 := by
  apply lucas_primality 433955323 (3 : ZMod 433955323)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (24108629, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (24108629, 1)] : List FactorBlock).map factorBlockValue).prod) = 433955323 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_24108629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 433955323) ^ 216977661 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 433955323) ^ 144651774 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 433955323) ^ 18 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_484266823 : Nat.Prime 484266823 := by
  apply lucas_primality 484266823 (5 : ZMod 484266823)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (1423, 1), (4363, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (1423, 1), (4363, 1)] : List FactorBlock).map factorBlockValue).prod) = 484266823 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_13
      · exact prime_oneHundredFiftySixEX_1423
      · exact prime_oneHundredFiftySixEX_4363
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 484266823) ^ 242133411 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 484266823) ^ 161422274 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 484266823) ^ 37251294 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 484266823) ^ 340314 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 484266823) ^ 110994 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_559319647 : Nat.Prime 559319647 := by
  apply lucas_primality 559319647 (3 : ZMod 559319647)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (47, 1), (59, 1), (33617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (47, 1), (59, 1), (33617, 1)] : List FactorBlock).map factorBlockValue).prod) = 559319647 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_47
      · exact prime_oneHundredFiftySixEX_59
      · exact prime_oneHundredFiftySixEX_33617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 559319647) ^ 279659823 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 559319647) ^ 186439882 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 559319647) ^ 11900418 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 559319647) ^ 9479994 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 559319647) ^ 16638 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_606209761 : Nat.Prime 606209761 := by
  apply lucas_primality 606209761 (14 : ZMod 606209761)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (5, 1), (13, 2), (47, 1), (53, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (5, 1), (13, 2), (47, 1), (53, 1)] : List FactorBlock).map factorBlockValue).prod) = 606209761 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_5
      · exact prime_oneHundredFiftySixEX_13
      · exact prime_oneHundredFiftySixEX_47
      · exact prime_oneHundredFiftySixEX_53
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 606209761) ^ 303104880 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (14 : ZMod 606209761) ^ 202069920 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (14 : ZMod 606209761) ^ 121241952 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (14 : ZMod 606209761) ^ 46631520 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (14 : ZMod 606209761) ^ 12898080 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (14 : ZMod 606209761) ^ 11437920 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_640433267 : Nat.Prime 640433267 := by
  apply lucas_primality 640433267 (2 : ZMod 640433267)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (19, 1), (61, 1), (25117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (19, 1), (61, 1), (25117, 1)] : List FactorBlock).map factorBlockValue).prod) = 640433267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_11
      · exact prime_oneHundredFiftySixEX_19
      · exact prime_oneHundredFiftySixEX_61
      · exact prime_oneHundredFiftySixEX_25117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 640433267) ^ 320216633 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 58221206 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 33707014 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 10498906 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 25498 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_671798731 : Nat.Prime 671798731 := by
  apply lucas_primality 671798731 (7 : ZMod 671798731)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (47, 1), (523, 1), (911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (47, 1), (523, 1), (911, 1)] : List FactorBlock).map factorBlockValue).prod) = 671798731 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_5
      · exact prime_oneHundredFiftySixEX_47
      · exact prime_oneHundredFiftySixEX_523
      · exact prime_oneHundredFiftySixEX_911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 671798731) ^ 335899365 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (7 : ZMod 671798731) ^ 223932910 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (7 : ZMod 671798731) ^ 134359746 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (7 : ZMod 671798731) ^ 14293590 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (7 : ZMod 671798731) ^ 1284510 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (7 : ZMod 671798731) ^ 737430 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_697948967 : Nat.Prime 697948967 := by
  apply lucas_primality 697948967 (7 : ZMod 697948967)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (13, 1), (47, 1), (137, 1), (379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (13, 1), (47, 1), (137, 1), (379, 1)] : List FactorBlock).map factorBlockValue).prod) = 697948967 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_11
      · exact prime_oneHundredFiftySixEX_13
      · exact prime_oneHundredFiftySixEX_47
      · exact prime_oneHundredFiftySixEX_137
      · exact prime_oneHundredFiftySixEX_379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 697948967) ^ 348974483 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (7 : ZMod 697948967) ^ 63449906 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (7 : ZMod 697948967) ^ 53688382 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (7 : ZMod 697948967) ^ 14849978 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (7 : ZMod 697948967) ^ 5094518 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (7 : ZMod 697948967) ^ 1841554 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_714027719 : Nat.Prime 714027719 := by
  apply lucas_primality 714027719 (11 : ZMod 714027719)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) = 714027719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_17203
      · exact prime_oneHundredFiftySixEX_20753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 714027719) ^ 357013859 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 41506 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 34406 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_773052649 : Nat.Prime 773052649 := by
  apply lucas_primality 773052649 (7 : ZMod 773052649)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (32210527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (32210527, 1)] : List FactorBlock).map factorBlockValue).prod) = 773052649 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_32210527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 773052649) ^ 386526324 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (7 : ZMod 773052649) ^ 257684216 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (7 : ZMod 773052649) ^ 24 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_824071373 : Nat.Prime 824071373 := by
  apply lucas_primality 824071373 (2 : ZMod 824071373)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (643, 1), (320401, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (643, 1), (320401, 1)] : List FactorBlock).map factorBlockValue).prod) = 824071373 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_643
      · exact prime_oneHundredFiftySixEX_320401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 824071373) ^ 412035686 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 824071373) ^ 1281604 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 824071373) ^ 2572 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_835787389 : Nat.Prime 835787389 := by
  apply lucas_primality 835787389 (10 : ZMod 835787389)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (43, 1), (95279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (43, 1), (95279, 1)] : List FactorBlock).map factorBlockValue).prod) = 835787389 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_17
      · exact prime_oneHundredFiftySixEX_43
      · exact prime_oneHundredFiftySixEX_95279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 835787389) ^ 417893694 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (10 : ZMod 835787389) ^ 278595796 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (10 : ZMod 835787389) ^ 49163964 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (10 : ZMod 835787389) ^ 19436916 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (10 : ZMod 835787389) ^ 8772 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_880051639 : Nat.Prime 880051639 := by
  apply lucas_primality 880051639 (6 : ZMod 880051639)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (146675273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (146675273, 1)] : List FactorBlock).map factorBlockValue).prod) = 880051639 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_146675273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 880051639) ^ 440025819 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 880051639) ^ 293350546 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 880051639) ^ 6 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_903576841 : Nat.Prime 903576841 := by
  apply lucas_primality 903576841 (7 : ZMod 903576841)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (31, 1), (293, 1), (829, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (31, 1), (293, 1), (829, 1)] : List FactorBlock).map factorBlockValue).prod) = 903576841 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_5
      · exact prime_oneHundredFiftySixEX_31
      · exact prime_oneHundredFiftySixEX_293
      · exact prime_oneHundredFiftySixEX_829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 903576841) ^ 451788420 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (7 : ZMod 903576841) ^ 301192280 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (7 : ZMod 903576841) ^ 180715368 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (7 : ZMod 903576841) ^ 29147640 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (7 : ZMod 903576841) ^ 3083880 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (7 : ZMod 903576841) ^ 1089960 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_924447929 : Nat.Prime 924447929 := by
  apply lucas_primality 924447929 (3 : ZMod 924447929)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (115555991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (115555991, 1)] : List FactorBlock).map factorBlockValue).prod) = 924447929 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_115555991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 924447929) ^ 462223964 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 924447929) ^ 8 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_942261469 : Nat.Prime 942261469 := by
  apply lucas_primality 942261469 (2 : ZMod 942261469)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (67, 1), (1171967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (67, 1), (1171967, 1)] : List FactorBlock).map factorBlockValue).prod) = 942261469 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_67
      · exact prime_oneHundredFiftySixEX_1171967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 942261469) ^ 471130734 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 942261469) ^ 314087156 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 942261469) ^ 14063604 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 942261469) ^ 804 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_1031457307 : Nat.Prime 1031457307 := by
  apply lucas_primality 1031457307 (2 : ZMod 1031457307)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (15628141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (15628141, 1)] : List FactorBlock).map factorBlockValue).prod) = 1031457307 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_11
      · exact prime_oneHundredFiftySixEX_15628141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1031457307) ^ 515728653 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1031457307) ^ 343819102 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1031457307) ^ 93768846 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1031457307) ^ 66 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_1036932751 : Nat.Prime 1036932751 := by
  apply lucas_primality 1036932751 (6 : ZMod 1036932751)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 3), (7, 1), (65837, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 3), (7, 1), (65837, 1)] : List FactorBlock).map factorBlockValue).prod) = 1036932751 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_5
      · exact prime_oneHundredFiftySixEX_7
      · exact prime_oneHundredFiftySixEX_65837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1036932751) ^ 518466375 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 1036932751) ^ 345644250 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 1036932751) ^ 207386550 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 1036932751) ^ 148133250 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 1036932751) ^ 15750 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_1102217329 : Nat.Prime 1102217329 := by
  apply lucas_primality 1102217329 (7 : ZMod 1102217329)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (2551429, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (2551429, 1)] : List FactorBlock).map factorBlockValue).prod) = 1102217329 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_2551429
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 1102217329) ^ 551108664 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (7 : ZMod 1102217329) ^ 367405776 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (7 : ZMod 1102217329) ^ 432 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_1215977617 : Nat.Prime 1215977617 := by
  apply lucas_primality 1215977617 (5 : ZMod 1215977617)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (7, 1), (23, 1), (17483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (7, 1), (23, 1), (17483, 1)] : List FactorBlock).map factorBlockValue).prod) = 1215977617 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_7
      · exact prime_oneHundredFiftySixEX_23
      · exact prime_oneHundredFiftySixEX_17483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1215977617) ^ 607988808 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 1215977617) ^ 405325872 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 1215977617) ^ 173711088 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 1215977617) ^ 52868592 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 1215977617) ^ 69552 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_1251687427 : Nat.Prime 1251687427 := by
  apply lucas_primality 1251687427 (2 : ZMod 1251687427)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (61, 1), (310901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (61, 1), (310901, 1)] : List FactorBlock).map factorBlockValue).prod) = 1251687427 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_11
      · exact prime_oneHundredFiftySixEX_61
      · exact prime_oneHundredFiftySixEX_310901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1251687427) ^ 625843713 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1251687427) ^ 417229142 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1251687427) ^ 113789766 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1251687427) ^ 20519466 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1251687427) ^ 4026 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_1378717061 : Nat.Prime 1378717061 := by
  apply lucas_primality 1378717061 (3 : ZMod 1378717061)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (23, 1), (428173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (23, 1), (428173, 1)] : List FactorBlock).map factorBlockValue).prod) = 1378717061 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_5
      · exact prime_oneHundredFiftySixEX_7
      · exact prime_oneHundredFiftySixEX_23
      · exact prime_oneHundredFiftySixEX_428173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1378717061) ^ 689358530 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1378717061) ^ 275743412 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1378717061) ^ 196959580 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1378717061) ^ 59944220 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1378717061) ^ 3220 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_1399940627 : Nat.Prime 1399940627 := by
  apply lucas_primality 1399940627 (2 : ZMod 1399940627)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (167, 1), (598777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (167, 1), (598777, 1)] : List FactorBlock).map factorBlockValue).prod) = 1399940627 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_7
      · exact prime_oneHundredFiftySixEX_167
      · exact prime_oneHundredFiftySixEX_598777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1399940627) ^ 699970313 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1399940627) ^ 199991518 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1399940627) ^ 8382878 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1399940627) ^ 2338 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_1475878223 : Nat.Prime 1475878223 := by
  apply lucas_primality 1475878223 (5 : ZMod 1475878223)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13, 1), (17, 1), (477013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13, 1), (17, 1), (477013, 1)] : List FactorBlock).map factorBlockValue).prod) = 1475878223 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_7
      · exact prime_oneHundredFiftySixEX_13
      · exact prime_oneHundredFiftySixEX_17
      · exact prime_oneHundredFiftySixEX_477013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1475878223) ^ 737939111 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 1475878223) ^ 210839746 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 1475878223) ^ 113529094 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 1475878223) ^ 86816366 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 1475878223) ^ 3094 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_1648142747 : Nat.Prime 1648142747 := by
  apply lucas_primality 1648142747 (2 : ZMod 1648142747)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (824071373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (824071373, 1)] : List FactorBlock).map factorBlockValue).prod) = 1648142747 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_824071373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 1648142747) ^ 824071373 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1648142747) ^ 2 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_1787696483 : Nat.Prime 1787696483 := by
  apply lucas_primality 1787696483 (2 : ZMod 1787696483)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (13, 1), (23, 1), (271769, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (13, 1), (23, 1), (271769, 1)] : List FactorBlock).map factorBlockValue).prod) = 1787696483 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_11
      · exact prime_oneHundredFiftySixEX_13
      · exact prime_oneHundredFiftySixEX_23
      · exact prime_oneHundredFiftySixEX_271769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1787696483) ^ 893848241 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1787696483) ^ 162517862 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1787696483) ^ 137515114 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1787696483) ^ 77725934 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1787696483) ^ 6578 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_2318099881 : Nat.Prime 2318099881 := by
  apply lucas_primality 2318099881 (7 : ZMod 2318099881)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (349, 1), (55351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (349, 1), (55351, 1)] : List FactorBlock).map factorBlockValue).prod) = 2318099881 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_5
      · exact prime_oneHundredFiftySixEX_349
      · exact prime_oneHundredFiftySixEX_55351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 2318099881) ^ 1159049940 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (7 : ZMod 2318099881) ^ 772699960 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (7 : ZMod 2318099881) ^ 463619976 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (7 : ZMod 2318099881) ^ 6642120 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (7 : ZMod 2318099881) ^ 41880 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_2416168199 : Nat.Prime 2416168199 := by
  apply lucas_primality 2416168199 (7 : ZMod 2416168199)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (71, 1), (362027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (71, 1), (362027, 1)] : List FactorBlock).map factorBlockValue).prod) = 2416168199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_47
      · exact prime_oneHundredFiftySixEX_71
      · exact prime_oneHundredFiftySixEX_362027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 2416168199) ^ 1208084099 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (7 : ZMod 2416168199) ^ 51407834 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (7 : ZMod 2416168199) ^ 34030538 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (7 : ZMod 2416168199) ^ 6674 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_2851881371 : Nat.Prime 2851881371 := by
  apply lucas_primality 2851881371 (2 : ZMod 2851881371)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (21937549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (21937549, 1)] : List FactorBlock).map factorBlockValue).prod) = 2851881371 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_5
      · exact prime_oneHundredFiftySixEX_13
      · exact prime_oneHundredFiftySixEX_21937549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2851881371) ^ 1425940685 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2851881371) ^ 570376274 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2851881371) ^ 219375490 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2851881371) ^ 130 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_3119242051 : Nat.Prime 3119242051 := by
  apply lucas_primality 3119242051 (3 : ZMod 3119242051)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (6931649, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (6931649, 1)] : List FactorBlock).map factorBlockValue).prod) = 3119242051 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_5
      · exact prime_oneHundredFiftySixEX_6931649
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3119242051) ^ 1559621025 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 3119242051) ^ 1039747350 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 3119242051) ^ 623848410 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 3119242051) ^ 450 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_3371100101 : Nat.Prime 3371100101 := by
  apply lucas_primality 3371100101 (7 : ZMod 3371100101)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (827, 1), (40763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (827, 1), (40763, 1)] : List FactorBlock).map factorBlockValue).prod) = 3371100101 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_5
      · exact prime_oneHundredFiftySixEX_827
      · exact prime_oneHundredFiftySixEX_40763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 3371100101) ^ 1685550050 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (7 : ZMod 3371100101) ^ 674220020 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (7 : ZMod 3371100101) ^ 4076300 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (7 : ZMod 3371100101) ^ 82700 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_3944461847 : Nat.Prime 3944461847 := by
  apply lucas_primality 3944461847 (5 : ZMod 3944461847)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (113, 1), (1342567, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (113, 1), (1342567, 1)] : List FactorBlock).map factorBlockValue).prod) = 3944461847 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_13
      · exact prime_oneHundredFiftySixEX_113
      · exact prime_oneHundredFiftySixEX_1342567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 3944461847) ^ 1972230923 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 3944461847) ^ 303420142 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 3944461847) ^ 34906742 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 3944461847) ^ 2938 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_4315154339 : Nat.Prime 4315154339 := by
  apply lucas_primality 4315154339 (2 : ZMod 4315154339)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (23, 1), (967, 1), (8819, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (23, 1), (967, 1), (8819, 1)] : List FactorBlock).map factorBlockValue).prod) = 4315154339 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_11
      · exact prime_oneHundredFiftySixEX_23
      · exact prime_oneHundredFiftySixEX_967
      · exact prime_oneHundredFiftySixEX_8819
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4315154339) ^ 2157577169 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 4315154339) ^ 392286758 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 4315154339) ^ 187615406 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 4315154339) ^ 4462414 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 4315154339) ^ 489302 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_5202374321 : Nat.Prime 5202374321 := by
  apply lucas_primality 5202374321 (3 : ZMod 5202374321)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (11, 1), (13, 2), (34981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (11, 1), (13, 2), (34981, 1)] : List FactorBlock).map factorBlockValue).prod) = 5202374321 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_5
      · exact prime_oneHundredFiftySixEX_11
      · exact prime_oneHundredFiftySixEX_13
      · exact prime_oneHundredFiftySixEX_34981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 5202374321) ^ 2601187160 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 5202374321) ^ 1040474864 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 5202374321) ^ 472943120 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 5202374321) ^ 400182640 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 5202374321) ^ 148720 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_5434050593 : Nat.Prime 5434050593 := by
  apply lucas_primality 5434050593 (3 : ZMod 5434050593)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (313, 1), (542537, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (313, 1), (542537, 1)] : List FactorBlock).map factorBlockValue).prod) = 5434050593 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_313
      · exact prime_oneHundredFiftySixEX_542537
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 5434050593) ^ 2717025296 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 5434050593) ^ 17361184 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 5434050593) ^ 10016 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_6037638679 : Nat.Prime 6037638679 := by
  apply lucas_primality 6037638679 (3 : ZMod 6037638679)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) = 6037638679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_31
      · exact prime_oneHundredFiftySixEX_10820141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6037638679) ^ 3018819339 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 2012546226 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 194762538 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 558 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_6998309863 : Nat.Prime 6998309863 := by
  apply lucas_primality 6998309863 (3 : ZMod 6998309863)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (19, 1), (67, 1), (53897, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (19, 1), (67, 1), (53897, 1)] : List FactorBlock).map factorBlockValue).prod) = 6998309863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_17
      · exact prime_oneHundredFiftySixEX_19
      · exact prime_oneHundredFiftySixEX_67
      · exact prime_oneHundredFiftySixEX_53897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 6998309863) ^ 3499154931 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 6998309863) ^ 2332769954 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 6998309863) ^ 411665286 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 6998309863) ^ 368332098 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 6998309863) ^ 104452386 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 6998309863) ^ 129846 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_7460903881 : Nat.Prime 7460903881 := by
  apply lucas_primality 7460903881 (11 : ZMod 7460903881)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (103, 1), (201211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (103, 1), (201211, 1)] : List FactorBlock).map factorBlockValue).prod) = 7460903881 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_5
      · exact prime_oneHundredFiftySixEX_103
      · exact prime_oneHundredFiftySixEX_201211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 7460903881) ^ 3730451940 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (11 : ZMod 7460903881) ^ 2486967960 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (11 : ZMod 7460903881) ^ 1492180776 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (11 : ZMod 7460903881) ^ 72435960 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (11 : ZMod 7460903881) ^ 37080 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_8508197141 : Nat.Prime 8508197141 := by
  apply lucas_primality 8508197141 (2 : ZMod 8508197141)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (113, 1), (373, 1), (10093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (113, 1), (373, 1), (10093, 1)] : List FactorBlock).map factorBlockValue).prod) = 8508197141 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_5
      · exact prime_oneHundredFiftySixEX_113
      · exact prime_oneHundredFiftySixEX_373
      · exact prime_oneHundredFiftySixEX_10093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8508197141) ^ 4254098570 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 8508197141) ^ 1701639428 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 8508197141) ^ 75293780 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 8508197141) ^ 22810180 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 8508197141) ^ 842980 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_9257508937 : Nat.Prime 9257508937 := by
  apply lucas_primality 9257508937 (5 : ZMod 9257508937)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (13, 1), (9890501, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (13, 1), (9890501, 1)] : List FactorBlock).map factorBlockValue).prod) = 9257508937 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_13
      · exact prime_oneHundredFiftySixEX_9890501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 9257508937) ^ 4628754468 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 9257508937) ^ 3085836312 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 9257508937) ^ 712116072 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 9257508937) ^ 936 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_9489036071 : Nat.Prime 9489036071 := by
  apply lucas_primality 9489036071 (13 : ZMod 9489036071)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (193, 1), (311, 1), (15809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (193, 1), (311, 1), (15809, 1)] : List FactorBlock).map factorBlockValue).prod) = 9489036071 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_5
      · exact prime_oneHundredFiftySixEX_193
      · exact prime_oneHundredFiftySixEX_311
      · exact prime_oneHundredFiftySixEX_15809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 9489036071) ^ 4744518035 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (13 : ZMod 9489036071) ^ 1897807214 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (13 : ZMod 9489036071) ^ 49165990 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (13 : ZMod 9489036071) ^ 30511370 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (13 : ZMod 9489036071) ^ 600230 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_9730061597 : Nat.Prime 9730061597 := by
  apply lucas_primality 9730061597 (2 : ZMod 9730061597)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (211, 1), (569, 1), (20261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (211, 1), (569, 1), (20261, 1)] : List FactorBlock).map factorBlockValue).prod) = 9730061597 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_211
      · exact prime_oneHundredFiftySixEX_569
      · exact prime_oneHundredFiftySixEX_20261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 9730061597) ^ 4865030798 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 9730061597) ^ 46114036 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 9730061597) ^ 17100284 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 9730061597) ^ 480236 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_12886318591 : Nat.Prime 12886318591 := by
  apply lucas_primality 12886318591 (6 : ZMod 12886318591)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (429543953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (429543953, 1)] : List FactorBlock).map factorBlockValue).prod) = 12886318591 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_5
      · exact prime_oneHundredFiftySixEX_429543953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 12886318591) ^ 6443159295 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 12886318591) ^ 4295439530 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 12886318591) ^ 2577263718 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 12886318591) ^ 30 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_13322557151 : Nat.Prime 13322557151 := by
  apply lucas_primality 13322557151 (7 : ZMod 13322557151)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (7, 1), (71, 1), (97, 1), (5527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (7, 1), (71, 1), (97, 1), (5527, 1)] : List FactorBlock).map factorBlockValue).prod) = 13322557151 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_5
      · exact prime_oneHundredFiftySixEX_7
      · exact prime_oneHundredFiftySixEX_71
      · exact prime_oneHundredFiftySixEX_97
      · exact prime_oneHundredFiftySixEX_5527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 13322557151) ^ 6661278575 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (7 : ZMod 13322557151) ^ 2664511430 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (7 : ZMod 13322557151) ^ 1903222450 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (7 : ZMod 13322557151) ^ 187641650 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (7 : ZMod 13322557151) ^ 137345950 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (7 : ZMod 13322557151) ^ 2410450 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_14026441951 : Nat.Prime 14026441951 := by
  apply lucas_primality 14026441951 (3 : ZMod 14026441951)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (5, 2), (3463319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (5, 2), (3463319, 1)] : List FactorBlock).map factorBlockValue).prod) = 14026441951 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_5
      · exact prime_oneHundredFiftySixEX_3463319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 14026441951) ^ 7013220975 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 14026441951) ^ 4675480650 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 14026441951) ^ 2805288390 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 14026441951) ^ 4050 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_14750067271 : Nat.Prime 14750067271 := by
  apply lucas_primality 14750067271 (15 : ZMod 14750067271)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (19, 1), (101, 1), (256211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (19, 1), (101, 1), (256211, 1)] : List FactorBlock).map factorBlockValue).prod) = 14750067271 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_5
      · exact prime_oneHundredFiftySixEX_19
      · exact prime_oneHundredFiftySixEX_101
      · exact prime_oneHundredFiftySixEX_256211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 14750067271) ^ 7375033635 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (15 : ZMod 14750067271) ^ 4916689090 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (15 : ZMod 14750067271) ^ 2950013454 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (15 : ZMod 14750067271) ^ 776319330 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (15 : ZMod 14750067271) ^ 146040270 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (15 : ZMod 14750067271) ^ 57570 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_15743483669 : Nat.Prime 15743483669 := by
  apply lucas_primality 15743483669 (2 : ZMod 15743483669)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (103, 1), (3473849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (103, 1), (3473849, 1)] : List FactorBlock).map factorBlockValue).prod) = 15743483669 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_11
      · exact prime_oneHundredFiftySixEX_103
      · exact prime_oneHundredFiftySixEX_3473849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 15743483669) ^ 7871741834 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 15743483669) ^ 1431225788 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 15743483669) ^ 152849356 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 15743483669) ^ 4532 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_16377364331 : Nat.Prime 16377364331 := by
  apply lucas_primality 16377364331 (6 : ZMod 16377364331)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (193, 1), (8485681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (193, 1), (8485681, 1)] : List FactorBlock).map factorBlockValue).prod) = 16377364331 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_5
      · exact prime_oneHundredFiftySixEX_193
      · exact prime_oneHundredFiftySixEX_8485681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 16377364331) ^ 8188682165 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 16377364331) ^ 3275472866 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 16377364331) ^ 84856810 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 16377364331) ^ 1930 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_16514973161 : Nat.Prime 16514973161 := by
  apply lucas_primality 16514973161 (3 : ZMod 16514973161)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (7, 1), (349, 1), (169003, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (7, 1), (349, 1), (169003, 1)] : List FactorBlock).map factorBlockValue).prod) = 16514973161 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_5
      · exact prime_oneHundredFiftySixEX_7
      · exact prime_oneHundredFiftySixEX_349
      · exact prime_oneHundredFiftySixEX_169003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 16514973161) ^ 8257486580 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 16514973161) ^ 3302994632 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 16514973161) ^ 2359281880 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 16514973161) ^ 47320840 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 16514973161) ^ 97720 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_21200988013 : Nat.Prime 21200988013 := by
  apply lucas_primality 21200988013 (2 : ZMod 21200988013)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (37, 1), (1103, 1), (43291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (37, 1), (1103, 1), (43291, 1)] : List FactorBlock).map factorBlockValue).prod) = 21200988013 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_37
      · exact prime_oneHundredFiftySixEX_1103
      · exact prime_oneHundredFiftySixEX_43291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 21200988013) ^ 10600494006 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 21200988013) ^ 7066996004 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 21200988013) ^ 572999676 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 21200988013) ^ 19221204 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 21200988013) ^ 489732 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_24859917239 : Nat.Prime 24859917239 := by
  apply lucas_primality 24859917239 (11 : ZMod 24859917239)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 2), (1151, 1), (63901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 2), (1151, 1), (63901, 1)] : List FactorBlock).map factorBlockValue).prod) = 24859917239 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_13
      · exact prime_oneHundredFiftySixEX_1151
      · exact prime_oneHundredFiftySixEX_63901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 24859917239) ^ 12429958619 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (11 : ZMod 24859917239) ^ 1912301326 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (11 : ZMod 24859917239) ^ 21598538 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (11 : ZMod 24859917239) ^ 389038 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_25198931287 : Nat.Prime 25198931287 := by
  apply lucas_primality 25198931287 (3 : ZMod 25198931287)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (1399940627, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (1399940627, 1)] : List FactorBlock).map factorBlockValue).prod) = 25198931287 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_1399940627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 25198931287) ^ 12599465643 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 25198931287) ^ 8399643762 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 25198931287) ^ 18 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_27259443481 : Nat.Prime 27259443481 := by
  apply lucas_primality 27259443481 (17 : ZMod 27259443481)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (101, 1), (137, 1), (16417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (101, 1), (137, 1), (16417, 1)] : List FactorBlock).map factorBlockValue).prod) = 27259443481 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_5
      · exact prime_oneHundredFiftySixEX_101
      · exact prime_oneHundredFiftySixEX_137
      · exact prime_oneHundredFiftySixEX_16417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 27259443481) ^ 13629721740 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (17 : ZMod 27259443481) ^ 9086481160 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (17 : ZMod 27259443481) ^ 5451888696 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (17 : ZMod 27259443481) ^ 269895480 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (17 : ZMod 27259443481) ^ 198974040 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (17 : ZMod 27259443481) ^ 1660440 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_32754728663 : Nat.Prime 32754728663 := by
  apply lucas_primality 32754728663 (5 : ZMod 32754728663)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (16377364331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (16377364331, 1)] : List FactorBlock).map factorBlockValue).prod) = 32754728663 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_16377364331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 32754728663) ^ 16377364331 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 32754728663) ^ 2 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_34671681157 : Nat.Prime 34671681157 := by
  apply lucas_primality 34671681157 (2 : ZMod 34671681157)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (19, 1), (21724111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (19, 1), (21724111, 1)] : List FactorBlock).map factorBlockValue).prod) = 34671681157 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_7
      · exact prime_oneHundredFiftySixEX_19
      · exact prime_oneHundredFiftySixEX_21724111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 34671681157) ^ 17335840578 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 34671681157) ^ 11557227052 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 34671681157) ^ 4953097308 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 34671681157) ^ 1824825324 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 34671681157) ^ 1596 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_38958363881 : Nat.Prime 38958363881 := by
  apply lucas_primality 38958363881 (3 : ZMod 38958363881)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (2767, 1), (351991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (2767, 1), (351991, 1)] : List FactorBlock).map factorBlockValue).prod) = 38958363881 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_5
      · exact prime_oneHundredFiftySixEX_2767
      · exact prime_oneHundredFiftySixEX_351991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 38958363881) ^ 19479181940 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 38958363881) ^ 7791672776 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 38958363881) ^ 14079640 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 38958363881) ^ 110680 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_47612670971 : Nat.Prime 47612670971 := by
  apply lucas_primality 47612670971 (2 : ZMod 47612670971)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13411, 1), (355027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13411, 1), (355027, 1)] : List FactorBlock).map factorBlockValue).prod) = 47612670971 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_5
      · exact prime_oneHundredFiftySixEX_13411
      · exact prime_oneHundredFiftySixEX_355027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 47612670971) ^ 23806335485 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 47612670971) ^ 9522534194 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 47612670971) ^ 3550270 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 47612670971) ^ 134110 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_65207015611 : Nat.Prime 65207015611 := by
  apply lucas_primality 65207015611 (10 : ZMod 65207015611)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (19, 1), (10399843, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (19, 1), (10399843, 1)] : List FactorBlock).map factorBlockValue).prod) = 65207015611 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_5
      · exact prime_oneHundredFiftySixEX_11
      · exact prime_oneHundredFiftySixEX_19
      · exact prime_oneHundredFiftySixEX_10399843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 65207015611) ^ 32603507805 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (10 : ZMod 65207015611) ^ 21735671870 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (10 : ZMod 65207015611) ^ 13041403122 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (10 : ZMod 65207015611) ^ 5927910510 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (10 : ZMod 65207015611) ^ 3431948190 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (10 : ZMod 65207015611) ^ 6270 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_65807759629 : Nat.Prime 65807759629 := by
  apply lucas_primality 65807759629 (6 : ZMod 65807759629)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (13, 1), (17, 1), (41, 1), (201743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (13, 1), (17, 1), (41, 1), (201743, 1)] : List FactorBlock).map factorBlockValue).prod) = 65807759629 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_13
      · exact prime_oneHundredFiftySixEX_17
      · exact prime_oneHundredFiftySixEX_41
      · exact prime_oneHundredFiftySixEX_201743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 65807759629) ^ 32903879814 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 65807759629) ^ 21935919876 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 65807759629) ^ 5062135356 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 65807759629) ^ 3871044684 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 65807759629) ^ 1605067308 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 65807759629) ^ 326196 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_108465610171 : Nat.Prime 108465610171 := by
  apply lucas_primality 108465610171 (2 : ZMod 108465610171)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (17, 2), (337, 1), (37123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (17, 2), (337, 1), (37123, 1)] : List FactorBlock).map factorBlockValue).prod) = 108465610171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_5
      · exact prime_oneHundredFiftySixEX_17
      · exact prime_oneHundredFiftySixEX_337
      · exact prime_oneHundredFiftySixEX_37123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 108465610171) ^ 54232805085 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 108465610171) ^ 36155203390 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 108465610171) ^ 21693122034 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 108465610171) ^ 6380330010 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 108465610171) ^ 321856410 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 108465610171) ^ 2921790 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_115669499017 : Nat.Prime 115669499017 := by
  apply lucas_primality 115669499017 (15 : ZMod 115669499017)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (401, 1), (2693, 1), (4463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (401, 1), (2693, 1), (4463, 1)] : List FactorBlock).map factorBlockValue).prod) = 115669499017 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_401
      · exact prime_oneHundredFiftySixEX_2693
      · exact prime_oneHundredFiftySixEX_4463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 115669499017) ^ 57834749508 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (15 : ZMod 115669499017) ^ 38556499672 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (15 : ZMod 115669499017) ^ 288452616 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (15 : ZMod 115669499017) ^ 42951912 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (15 : ZMod 115669499017) ^ 25917432 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_118662433481 : Nat.Prime 118662433481 := by
  apply lucas_primality 118662433481 (6 : ZMod 118662433481)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (71, 1), (79, 1), (263, 1), (2011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (71, 1), (79, 1), (263, 1), (2011, 1)] : List FactorBlock).map factorBlockValue).prod) = 118662433481 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_5
      · exact prime_oneHundredFiftySixEX_71
      · exact prime_oneHundredFiftySixEX_79
      · exact prime_oneHundredFiftySixEX_263
      · exact prime_oneHundredFiftySixEX_2011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 118662433481) ^ 59331216740 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 118662433481) ^ 23732486696 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 118662433481) ^ 1671301880 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 118662433481) ^ 1502056120 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 118662433481) ^ 451187960 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 118662433481) ^ 59006680 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_126385799483 : Nat.Prime 126385799483 := by
  apply lucas_primality 126385799483 (2 : ZMod 126385799483)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (347, 1), (182112103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (347, 1), (182112103, 1)] : List FactorBlock).map factorBlockValue).prod) = 126385799483 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_347
      · exact prime_oneHundredFiftySixEX_182112103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 126385799483) ^ 63192899741 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 126385799483) ^ 364224206 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 126385799483) ^ 694 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_143544239351 : Nat.Prime 143544239351 := by
  apply lucas_primality 143544239351 (13 : ZMod 143544239351)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (71, 2), (569507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (71, 2), (569507, 1)] : List FactorBlock).map factorBlockValue).prod) = 143544239351 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_5
      · exact prime_oneHundredFiftySixEX_71
      · exact prime_oneHundredFiftySixEX_569507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 143544239351) ^ 71772119675 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (13 : ZMod 143544239351) ^ 28708847870 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (13 : ZMod 143544239351) ^ 2021749850 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (13 : ZMod 143544239351) ^ 252050 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_169551237041 : Nat.Prime 169551237041 := by
  apply lucas_primality 169551237041 (3 : ZMod 169551237041)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (401, 1), (5285263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (401, 1), (5285263, 1)] : List FactorBlock).map factorBlockValue).prod) = 169551237041 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_5
      · exact prime_oneHundredFiftySixEX_401
      · exact prime_oneHundredFiftySixEX_5285263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 169551237041) ^ 84775618520 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 169551237041) ^ 33910247408 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 169551237041) ^ 422821040 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 169551237041) ^ 32080 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_233750183287 : Nat.Prime 233750183287 := by
  apply lucas_primality 233750183287 (3 : ZMod 233750183287)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (38958363881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (38958363881, 1)] : List FactorBlock).map factorBlockValue).prod) = 233750183287 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_38958363881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 233750183287) ^ 116875091643 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 233750183287) ^ 77916727762 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 233750183287) ^ 6 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_243364641461 : Nat.Prime 243364641461 := by
  apply lucas_primality 243364641461 (2 : ZMod 243364641461)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (19, 1), (640433267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (19, 1), (640433267, 1)] : List FactorBlock).map factorBlockValue).prod) = 243364641461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_5
      · exact prime_oneHundredFiftySixEX_19
      · exact prime_oneHundredFiftySixEX_640433267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 243364641461) ^ 121682320730 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 243364641461) ^ 48672928292 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 243364641461) ^ 12808665340 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 243364641461) ^ 380 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_256319107423 : Nat.Prime 256319107423 := by
  apply lucas_primality 256319107423 (6 : ZMod 256319107423)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (19, 1), (53, 1), (491, 1), (12343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (19, 1), (53, 1), (491, 1), (12343, 1)] : List FactorBlock).map factorBlockValue).prod) = 256319107423 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_7
      · exact prime_oneHundredFiftySixEX_19
      · exact prime_oneHundredFiftySixEX_53
      · exact prime_oneHundredFiftySixEX_491
      · exact prime_oneHundredFiftySixEX_12343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 256319107423) ^ 128159553711 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 256319107423) ^ 85439702474 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 256319107423) ^ 36617015346 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 256319107423) ^ 13490479338 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 256319107423) ^ 4836209574 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 256319107423) ^ 522034842 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 256319107423) ^ 20766354 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_263231038517 : Nat.Prime 263231038517 := by
  apply lucas_primality 263231038517 (2 : ZMod 263231038517)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (65807759629, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (65807759629, 1)] : List FactorBlock).map factorBlockValue).prod) = 263231038517 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_65807759629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 263231038517) ^ 131615519258 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 263231038517) ^ 4 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_340992992917 : Nat.Prime 340992992917 := by
  apply lucas_primality 340992992917 (2 : ZMod 340992992917)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (17, 1), (61908677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (17, 1), (61908677, 1)] : List FactorBlock).map factorBlockValue).prod) = 340992992917 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_17
      · exact prime_oneHundredFiftySixEX_61908677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 340992992917) ^ 170496496458 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 340992992917) ^ 113664330972 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 340992992917) ^ 20058411348 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 340992992917) ^ 5508 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_365563501469 : Nat.Prime 365563501469 := by
  apply lucas_primality 365563501469 (3 : ZMod 365563501469)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (53, 1), (2081, 1), (75329, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (53, 1), (2081, 1), (75329, 1)] : List FactorBlock).map factorBlockValue).prod) = 365563501469 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_11
      · exact prime_oneHundredFiftySixEX_53
      · exact prime_oneHundredFiftySixEX_2081
      · exact prime_oneHundredFiftySixEX_75329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 365563501469) ^ 182781750734 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 365563501469) ^ 33233045588 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 365563501469) ^ 6897424556 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 365563501469) ^ 175667228 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 365563501469) ^ 4852892 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_384101989309 : Nat.Prime 384101989309 := by
  apply lucas_primality 384101989309 (2 : ZMod 384101989309)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (241, 1), (311, 1), (15817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (241, 1), (311, 1), (15817, 1)] : List FactorBlock).map factorBlockValue).prod) = 384101989309 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_241
      · exact prime_oneHundredFiftySixEX_311
      · exact prime_oneHundredFiftySixEX_15817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 384101989309) ^ 192050994654 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 384101989309) ^ 128033996436 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 384101989309) ^ 1593784188 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 384101989309) ^ 1235054628 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 384101989309) ^ 24284124 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_392154261859 : Nat.Prime 392154261859 := by
  apply lucas_primality 392154261859 (10 : ZMod 392154261859)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (37, 1), (1367, 1), (430739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (37, 1), (1367, 1), (430739, 1)] : List FactorBlock).map factorBlockValue).prod) = 392154261859 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_37
      · exact prime_oneHundredFiftySixEX_1367
      · exact prime_oneHundredFiftySixEX_430739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 392154261859) ^ 196077130929 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (10 : ZMod 392154261859) ^ 130718087286 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (10 : ZMod 392154261859) ^ 10598763834 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (10 : ZMod 392154261859) ^ 286872174 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (10 : ZMod 392154261859) ^ 910422 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_415165977371 : Nat.Prime 415165977371 := by
  apply lucas_primality 415165977371 (2 : ZMod 415165977371)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (691, 1), (60081907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (691, 1), (60081907, 1)] : List FactorBlock).map factorBlockValue).prod) = 415165977371 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_5
      · exact prime_oneHundredFiftySixEX_691
      · exact prime_oneHundredFiftySixEX_60081907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 415165977371) ^ 207582988685 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 415165977371) ^ 83033195474 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 415165977371) ^ 600819070 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 415165977371) ^ 6910 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_462677996069 : Nat.Prime 462677996069 := by
  apply lucas_primality 462677996069 (2 : ZMod 462677996069)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (115669499017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (115669499017, 1)] : List FactorBlock).map factorBlockValue).prod) = 462677996069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_115669499017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 462677996069) ^ 231338998034 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 462677996069) ^ 4 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_711906617041 : Nat.Prime 711906617041 := by
  apply lucas_primality 711906617041 (29 : ZMod 711906617041)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (23581, 1), (125791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (23581, 1), (125791, 1)] : List FactorBlock).map factorBlockValue).prod) = 711906617041 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_5
      · exact prime_oneHundredFiftySixEX_23581
      · exact prime_oneHundredFiftySixEX_125791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (29 : ZMod 711906617041) ^ 355953308520 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (29 : ZMod 711906617041) ^ 237302205680 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (29 : ZMod 711906617041) ^ 142381323408 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (29 : ZMod 711906617041) ^ 30189840 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (29 : ZMod 711906617041) ^ 5659440 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_745409496757 : Nat.Prime 745409496757 := by
  apply lucas_primality 745409496757 (2 : ZMod 745409496757)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (89, 1), (697948967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (89, 1), (697948967, 1)] : List FactorBlock).map factorBlockValue).prod) = 745409496757 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_89
      · exact prime_oneHundredFiftySixEX_697948967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 745409496757) ^ 372704748378 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 745409496757) ^ 248469832252 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 745409496757) ^ 8375387604 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 745409496757) ^ 1068 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_749523766273 : Nat.Prime 749523766273 := by
  apply lucas_primality 749523766273 (5 : ZMod 749523766273)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 10), (3, 1), (47, 1), (821, 1), (6323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 10), (3, 1), (47, 1), (821, 1), (6323, 1)] : List FactorBlock).map factorBlockValue).prod) = 749523766273 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_47
      · exact prime_oneHundredFiftySixEX_821
      · exact prime_oneHundredFiftySixEX_6323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 749523766273) ^ 374761883136 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 749523766273) ^ 249841255424 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 749523766273) ^ 15947314176 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 749523766273) ^ 912940032 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 749523766273) ^ 118539264 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_1564506913061 : Nat.Prime 1564506913061 := by
  apply lucas_primality 1564506913061 (2 : ZMod 1564506913061)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (13, 1), (281, 1), (3059143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (13, 1), (281, 1), (3059143, 1)] : List FactorBlock).map factorBlockValue).prod) = 1564506913061 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_5
      · exact prime_oneHundredFiftySixEX_7
      · exact prime_oneHundredFiftySixEX_13
      · exact prime_oneHundredFiftySixEX_281
      · exact prime_oneHundredFiftySixEX_3059143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1564506913061) ^ 782253456530 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1564506913061) ^ 312901382612 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1564506913061) ^ 223500987580 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1564506913061) ^ 120346685620 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1564506913061) ^ 5567640260 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1564506913061) ^ 511420 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_2676546708113 : Nat.Prime 2676546708113 := by
  apply lucas_primality 2676546708113 (3 : ZMod 2676546708113)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (107, 1), (28729, 1), (54419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (107, 1), (28729, 1), (54419, 1)] : List FactorBlock).map factorBlockValue).prod) = 2676546708113 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_107
      · exact prime_oneHundredFiftySixEX_28729
      · exact prime_oneHundredFiftySixEX_54419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2676546708113) ^ 1338273354056 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 2676546708113) ^ 25014455216 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 2676546708113) ^ 93165328 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 2676546708113) ^ 49184048 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_3693685767911 : Nat.Prime 3693685767911 := by
  apply lucas_primality 3693685767911 (19 : ZMod 3693685767911)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (71, 1), (5202374321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (71, 1), (5202374321, 1)] : List FactorBlock).map factorBlockValue).prod) = 3693685767911 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_5
      · exact prime_oneHundredFiftySixEX_71
      · exact prime_oneHundredFiftySixEX_5202374321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 3693685767911) ^ 1846842883955 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (19 : ZMod 3693685767911) ^ 738737153582 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (19 : ZMod 3693685767911) ^ 52023743210 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (19 : ZMod 3693685767911) ^ 710 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_4014078193691 : Nat.Prime 4014078193691 := by
  apply lucas_primality 4014078193691 (2 : ZMod 4014078193691)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (829, 1), (1051, 1), (460711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (829, 1), (1051, 1), (460711, 1)] : List FactorBlock).map factorBlockValue).prod) = 4014078193691 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_5
      · exact prime_oneHundredFiftySixEX_829
      · exact prime_oneHundredFiftySixEX_1051
      · exact prime_oneHundredFiftySixEX_460711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4014078193691) ^ 2007039096845 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 4014078193691) ^ 802815638738 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 4014078193691) ^ 4842072610 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 4014078193691) ^ 3819294190 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 4014078193691) ^ 8712790 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_4067900353939 : Nat.Prime 4067900353939 := by
  apply lucas_primality 4067900353939 (3 : ZMod 4067900353939)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (263, 1), (151640213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (263, 1), (151640213, 1)] : List FactorBlock).map factorBlockValue).prod) = 4067900353939 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_17
      · exact prime_oneHundredFiftySixEX_263
      · exact prime_oneHundredFiftySixEX_151640213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4067900353939) ^ 2033950176969 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 4067900353939) ^ 1355966784646 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 4067900353939) ^ 239288256114 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 4067900353939) ^ 15467301726 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 4067900353939) ^ 26826 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_5506709036351 : Nat.Prime 5506709036351 := by
  apply lucas_primality 5506709036351 (17 : ZMod 5506709036351)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (47, 1), (3373, 1), (694717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (47, 1), (3373, 1), (694717, 1)] : List FactorBlock).map factorBlockValue).prod) = 5506709036351 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_5
      · exact prime_oneHundredFiftySixEX_47
      · exact prime_oneHundredFiftySixEX_3373
      · exact prime_oneHundredFiftySixEX_694717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 5506709036351) ^ 2753354518175 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (17 : ZMod 5506709036351) ^ 1101341807270 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (17 : ZMod 5506709036351) ^ 117164022050 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (17 : ZMod 5506709036351) ^ 1632584950 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (17 : ZMod 5506709036351) ^ 7926550 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_5782770656261 : Nat.Prime 5782770656261 := by
  apply lucas_primality 5782770656261 (2 : ZMod 5782770656261)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (13, 1), (17, 1), (23447, 1), (55799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (13, 1), (17, 1), (23447, 1), (55799, 1)] : List FactorBlock).map factorBlockValue).prod) = 5782770656261 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_5
      · exact prime_oneHundredFiftySixEX_13
      · exact prime_oneHundredFiftySixEX_17
      · exact prime_oneHundredFiftySixEX_23447
      · exact prime_oneHundredFiftySixEX_55799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5782770656261) ^ 2891385328130 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 5782770656261) ^ 1156554131252 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 5782770656261) ^ 444828512020 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 5782770656261) ^ 340162979780 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 5782770656261) ^ 246631580 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 5782770656261) ^ 103635740 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_7177211967551 : Nat.Prime 7177211967551 := by
  apply lucas_primality 7177211967551 (13 : ZMod 7177211967551)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (143544239351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (143544239351, 1)] : List FactorBlock).map factorBlockValue).prod) = 7177211967551 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_5
      · exact prime_oneHundredFiftySixEX_143544239351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 7177211967551) ^ 3588605983775 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (13 : ZMod 7177211967551) ^ 1435442393510 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (13 : ZMod 7177211967551) ^ 50 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_7197701603837 : Nat.Prime 7197701603837 := by
  apply lucas_primality 7197701603837 (2 : ZMod 7197701603837)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (79, 1), (211, 1), (271, 1), (398341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (79, 1), (211, 1), (271, 1), (398341, 1)] : List FactorBlock).map factorBlockValue).prod) = 7197701603837 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_79
      · exact prime_oneHundredFiftySixEX_211
      · exact prime_oneHundredFiftySixEX_271
      · exact prime_oneHundredFiftySixEX_398341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7197701603837) ^ 3598850801918 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 7197701603837) ^ 91110146884 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 7197701603837) ^ 34112329876 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 7197701603837) ^ 26559784516 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 7197701603837) ^ 18069196 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_13971226936099 : Nat.Prime 13971226936099 := by
  apply lucas_primality 13971226936099 (2 : ZMod 13971226936099)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (21617, 1), (6336347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (21617, 1), (6336347, 1)] : List FactorBlock).map factorBlockValue).prod) = 13971226936099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_17
      · exact prime_oneHundredFiftySixEX_21617
      · exact prime_oneHundredFiftySixEX_6336347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 13971226936099) ^ 6985613468049 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 13971226936099) ^ 4657075645366 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 13971226936099) ^ 821836878594 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 13971226936099) ^ 646307394 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 13971226936099) ^ 2204934 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_19041345201559 : Nat.Prime 19041345201559 := by
  apply lucas_primality 19041345201559 (3 : ZMod 19041345201559)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (373, 1), (8508197141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (373, 1), (8508197141, 1)] : List FactorBlock).map factorBlockValue).prod) = 19041345201559 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_373
      · exact prime_oneHundredFiftySixEX_8508197141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 19041345201559) ^ 9520672600779 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 19041345201559) ^ 6347115067186 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 19041345201559) ^ 51049182846 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 19041345201559) ^ 2238 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_19211985866123 : Nat.Prime 19211985866123 := by
  apply lucas_primality 19211985866123 (2 : ZMod 19211985866123)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (47, 1), (1613, 1), (18101393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (47, 1), (1613, 1), (18101393, 1)] : List FactorBlock).map factorBlockValue).prod) = 19211985866123 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_7
      · exact prime_oneHundredFiftySixEX_47
      · exact prime_oneHundredFiftySixEX_1613
      · exact prime_oneHundredFiftySixEX_18101393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 19211985866123) ^ 9605992933061 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 19211985866123) ^ 2744569409446 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 19211985866123) ^ 408765656726 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 19211985866123) ^ 11910716594 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 19211985866123) ^ 1061354 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_27920119256221 : Nat.Prime 27920119256221 := by
  apply lucas_primality 27920119256221 (7 : ZMod 27920119256221)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (631, 1), (797, 1), (925291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (631, 1), (797, 1), (925291, 1)] : List FactorBlock).map factorBlockValue).prod) = 27920119256221 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_5
      · exact prime_oneHundredFiftySixEX_631
      · exact prime_oneHundredFiftySixEX_797
      · exact prime_oneHundredFiftySixEX_925291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 27920119256221) ^ 13960059628110 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (7 : ZMod 27920119256221) ^ 9306706418740 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (7 : ZMod 27920119256221) ^ 5584023851244 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (7 : ZMod 27920119256221) ^ 44247415620 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (7 : ZMod 27920119256221) ^ 35031517260 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (7 : ZMod 27920119256221) ^ 30174420 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_29816700622001 : Nat.Prime 29816700622001 := by
  apply lucas_primality 29816700622001 (6 : ZMod 29816700622001)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 3), (17, 1), (353, 1), (2484311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 3), (17, 1), (353, 1), (2484311, 1)] : List FactorBlock).map factorBlockValue).prod) = 29816700622001 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_5
      · exact prime_oneHundredFiftySixEX_17
      · exact prime_oneHundredFiftySixEX_353
      · exact prime_oneHundredFiftySixEX_2484311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 29816700622001) ^ 14908350311000 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 29816700622001) ^ 5963340124400 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 29816700622001) ^ 1753923566000 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 29816700622001) ^ 84466574000 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 29816700622001) ^ 12002000 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_32434382548033 : Nat.Prime 32434382548033 := by
  apply lucas_primality 32434382548033 (5 : ZMod 32434382548033)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (61, 1), (7057, 1), (392423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (61, 1), (7057, 1), (392423, 1)] : List FactorBlock).map factorBlockValue).prod) = 32434382548033 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_61
      · exact prime_oneHundredFiftySixEX_7057
      · exact prime_oneHundredFiftySixEX_392423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 32434382548033) ^ 16217191274016 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 32434382548033) ^ 10811460849344 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 32434382548033) ^ 531711189312 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 32434382548033) ^ 4596058176 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 32434382548033) ^ 82651584 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_33312673606897 : Nat.Prime 33312673606897 := by
  apply lucas_primality 33312673606897 (7 : ZMod 33312673606897)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (31, 1), (151, 2), (327289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (31, 1), (151, 2), (327289, 1)] : List FactorBlock).map factorBlockValue).prod) = 33312673606897 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_31
      · exact prime_oneHundredFiftySixEX_151
      · exact prime_oneHundredFiftySixEX_327289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 33312673606897) ^ 16656336803448 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (7 : ZMod 33312673606897) ^ 11104224535632 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (7 : ZMod 33312673606897) ^ 1074602374416 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (7 : ZMod 33312673606897) ^ 220613732496 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (7 : ZMod 33312673606897) ^ 101783664 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_35449576648411 : Nat.Prime 35449576648411 := by
  apply lucas_primality 35449576648411 (3 : ZMod 35449576648411)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (101, 1), (137, 1), (85398031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (101, 1), (137, 1), (85398031, 1)] : List FactorBlock).map factorBlockValue).prod) = 35449576648411 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_5
      · exact prime_oneHundredFiftySixEX_101
      · exact prime_oneHundredFiftySixEX_137
      · exact prime_oneHundredFiftySixEX_85398031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 35449576648411) ^ 17724788324205 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 35449576648411) ^ 11816525549470 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 35449576648411) ^ 7089915329682 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 35449576648411) ^ 350985907410 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 35449576648411) ^ 258756033930 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 35449576648411) ^ 415110 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_39758057268073 : Nat.Prime 39758057268073 := by
  apply lucas_primality 39758057268073 (5 : ZMod 39758057268073)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (13, 1), (317, 1), (557, 1), (65609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (13, 1), (317, 1), (557, 1), (65609, 1)] : List FactorBlock).map factorBlockValue).prod) = 39758057268073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_11
      · exact prime_oneHundredFiftySixEX_13
      · exact prime_oneHundredFiftySixEX_317
      · exact prime_oneHundredFiftySixEX_557
      · exact prime_oneHundredFiftySixEX_65609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 39758057268073) ^ 19879028634036 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 39758057268073) ^ 13252685756024 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 39758057268073) ^ 3614368842552 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 39758057268073) ^ 3058312097544 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 39758057268073) ^ 125419739016 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 39758057268073) ^ 71378917896 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 39758057268073) ^ 605984808 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_45752552594669 : Nat.Prime 45752552594669 := by
  apply lucas_primality 45752552594669 (2 : ZMod 45752552594669)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (47, 1), (243364641461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (47, 1), (243364641461, 1)] : List FactorBlock).map factorBlockValue).prod) = 45752552594669 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_47
      · exact prime_oneHundredFiftySixEX_243364641461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 45752552594669) ^ 22876276297334 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 45752552594669) ^ 973458565844 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 45752552594669) ^ 188 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_49538551476619 : Nat.Prime 49538551476619 := by
  apply lucas_primality 49538551476619 (2 : ZMod 49538551476619)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (119237, 1), (23081273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (119237, 1), (23081273, 1)] : List FactorBlock).map factorBlockValue).prod) = 49538551476619 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_119237
      · exact prime_oneHundredFiftySixEX_23081273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 49538551476619) ^ 24769275738309 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 49538551476619) ^ 16512850492206 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 49538551476619) ^ 415462914 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 49538551476619) ^ 2146266 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_51350336634101 : Nat.Prime 51350336634101 := by
  apply lucas_primality 51350336634101 (2 : ZMod 51350336634101)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (7, 1), (17, 1), (4315154339, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (7, 1), (17, 1), (4315154339, 1)] : List FactorBlock).map factorBlockValue).prod) = 51350336634101 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_5
      · exact prime_oneHundredFiftySixEX_7
      · exact prime_oneHundredFiftySixEX_17
      · exact prime_oneHundredFiftySixEX_4315154339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 51350336634101) ^ 25675168317050 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 51350336634101) ^ 10270067326820 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 51350336634101) ^ 7335762376300 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 51350336634101) ^ 3020608037300 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 51350336634101) ^ 11900 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_52688903207623 : Nat.Prime 52688903207623 := by
  apply lucas_primality 52688903207623 (3 : ZMod 52688903207623)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (107, 1), (7460903881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (107, 1), (7460903881, 1)] : List FactorBlock).map factorBlockValue).prod) = 52688903207623 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_11
      · exact prime_oneHundredFiftySixEX_107
      · exact prime_oneHundredFiftySixEX_7460903881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 52688903207623) ^ 26344451603811 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 52688903207623) ^ 17562967735874 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 52688903207623) ^ 4789900291602 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 52688903207623) ^ 492419656146 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 52688903207623) ^ 7062 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_53124688297339 : Nat.Prime 53124688297339 := by
  apply lucas_primality 53124688297339 (2 : ZMod 53124688297339)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (23, 1), (173, 1), (17683, 1), (17977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (23, 1), (173, 1), (17683, 1), (17977, 1)] : List FactorBlock).map factorBlockValue).prod) = 53124688297339 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_7
      · exact prime_oneHundredFiftySixEX_23
      · exact prime_oneHundredFiftySixEX_173
      · exact prime_oneHundredFiftySixEX_17683
      · exact prime_oneHundredFiftySixEX_17977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 53124688297339) ^ 26562344148669 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 53124688297339) ^ 17708229432446 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 53124688297339) ^ 7589241185334 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 53124688297339) ^ 2309769056406 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 53124688297339) ^ 307079123106 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 53124688297339) ^ 3004280286 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 53124688297339) ^ 2955147594 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_77487648889403 : Nat.Prime 77487648889403 := by
  apply lucas_primality 77487648889403 (2 : ZMod 77487648889403)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (643, 1), (3739, 1), (555697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (643, 1), (3739, 1), (555697, 1)] : List FactorBlock).map factorBlockValue).prod) = 77487648889403 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_29
      · exact prime_oneHundredFiftySixEX_643
      · exact prime_oneHundredFiftySixEX_3739
      · exact prime_oneHundredFiftySixEX_555697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 77487648889403) ^ 38743824444701 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 77487648889403) ^ 2671987892738 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 77487648889403) ^ 120509562814 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 77487648889403) ^ 20724163918 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 77487648889403) ^ 139442266 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_97471289066149 : Nat.Prime 97471289066149 := by
  apply lucas_primality 97471289066149 (2 : ZMod 97471289066149)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5591, 1), (484266823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5591, 1), (484266823, 1)] : List FactorBlock).map factorBlockValue).prod) = 97471289066149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_5591
      · exact prime_oneHundredFiftySixEX_484266823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 97471289066149) ^ 48735644533074 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 97471289066149) ^ 32490429688716 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 97471289066149) ^ 17433605628 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 97471289066149) ^ 201276 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_103160826000937 : Nat.Prime 103160826000937 := by
  apply lucas_primality 103160826000937 (5 : ZMod 103160826000937)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 6), (11, 1), (17, 1), (19, 1), (271, 1), (18371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 6), (11, 1), (17, 1), (19, 1), (271, 1), (18371, 1)] : List FactorBlock).map factorBlockValue).prod) = 103160826000937 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_11
      · exact prime_oneHundredFiftySixEX_17
      · exact prime_oneHundredFiftySixEX_19
      · exact prime_oneHundredFiftySixEX_271
      · exact prime_oneHundredFiftySixEX_18371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 103160826000937) ^ 51580413000468 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 103160826000937) ^ 34386942000312 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 103160826000937) ^ 9378256909176 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 103160826000937) ^ 6068283882408 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 103160826000937) ^ 5429517157944 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 103160826000937) ^ 380667254616 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 103160826000937) ^ 5615417016 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_115342509540833 : Nat.Prime 115342509540833 := by
  apply lucas_primality 115342509540833 (3 : ZMod 115342509540833)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (7, 1), (2777, 1), (185423809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (7, 1), (2777, 1), (185423809, 1)] : List FactorBlock).map factorBlockValue).prod) = 115342509540833 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_7
      · exact prime_oneHundredFiftySixEX_2777
      · exact prime_oneHundredFiftySixEX_185423809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 115342509540833) ^ 57671254770416 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 115342509540833) ^ 16477501362976 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 115342509540833) ^ 41534933216 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 115342509540833) ^ 622048 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_115465670140633 : Nat.Prime 115465670140633 := by
  apply lucas_primality 115465670140633 (11 : ZMod 115465670140633)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 3), (14026441951, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 3), (14026441951, 1)] : List FactorBlock).map factorBlockValue).prod) = 115465670140633 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_7
      · exact prime_oneHundredFiftySixEX_14026441951
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 115465670140633) ^ 57732835070316 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (11 : ZMod 115465670140633) ^ 38488556713544 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (11 : ZMod 115465670140633) ^ 16495095734376 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (11 : ZMod 115465670140633) ^ 8232 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_130417135331503 : Nat.Prime 130417135331503 := by
  apply lucas_primality 130417135331503 (3 : ZMod 130417135331503)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 1), (749523766273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 1), (749523766273, 1)] : List FactorBlock).map factorBlockValue).prod) = 130417135331503 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_29
      · exact prime_oneHundredFiftySixEX_749523766273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 130417135331503) ^ 65208567665751 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 130417135331503) ^ 43472378443834 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 130417135331503) ^ 4497142597638 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 130417135331503) ^ 174 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_176600617985551 : Nat.Prime 176600617985551 := by
  apply lucas_primality 176600617985551 (3 : ZMod 176600617985551)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (11, 2), (9730061597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (11, 2), (9730061597, 1)] : List FactorBlock).map factorBlockValue).prod) = 176600617985551 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_5
      · exact prime_oneHundredFiftySixEX_11
      · exact prime_oneHundredFiftySixEX_9730061597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 176600617985551) ^ 88300308992775 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 176600617985551) ^ 58866872661850 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 176600617985551) ^ 35320123597110 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 176600617985551) ^ 16054601635050 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 176600617985551) ^ 18150 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_190245315638867 : Nat.Prime 190245315638867 := by
  apply lucas_primality 190245315638867 (2 : ZMod 190245315638867)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (773, 1), (51503, 1), (125753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (773, 1), (51503, 1), (125753, 1)] : List FactorBlock).map factorBlockValue).prod) = 190245315638867 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_19
      · exact prime_oneHundredFiftySixEX_773
      · exact prime_oneHundredFiftySixEX_51503
      · exact prime_oneHundredFiftySixEX_125753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 190245315638867) ^ 95122657819433 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 190245315638867) ^ 10012911349414 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 190245315638867) ^ 246112956842 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 190245315638867) ^ 3693868622 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 190245315638867) ^ 1512849122 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_240844691621461 : Nat.Prime 240844691621461 := by
  apply lucas_primality 240844691621461 (2 : ZMod 240844691621461)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (4014078193691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (4014078193691, 1)] : List FactorBlock).map factorBlockValue).prod) = 240844691621461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_5
      · exact prime_oneHundredFiftySixEX_4014078193691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 240844691621461) ^ 120422345810730 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 240844691621461) ^ 80281563873820 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 240844691621461) ^ 48168938324292 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 240844691621461) ^ 60 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_258862483991359 : Nat.Prime 258862483991359 := by
  apply lucas_primality 258862483991359 (6 : ZMod 258862483991359)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (10789, 1), (102534983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (10789, 1), (102534983, 1)] : List FactorBlock).map factorBlockValue).prod) = 258862483991359 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_13
      · exact prime_oneHundredFiftySixEX_10789
      · exact prime_oneHundredFiftySixEX_102534983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 258862483991359) ^ 129431241995679 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 258862483991359) ^ 86287494663786 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 258862483991359) ^ 19912498768566 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 258862483991359) ^ 23993186022 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 258862483991359) ^ 2524626 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_259117257738133 : Nat.Prime 259117257738133 := by
  apply lucas_primality 259117257738133 (5 : ZMod 259117257738133)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7197701603837, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7197701603837, 1)] : List FactorBlock).map factorBlockValue).prod) = 259117257738133 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_7197701603837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 259117257738133) ^ 129558628869066 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 259117257738133) ^ 86372419246044 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 259117257738133) ^ 36 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_267494201311979 : Nat.Prime 267494201311979 := by
  apply lucas_primality 267494201311979 (6 : ZMod 267494201311979)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (97, 1), (107, 1), (12886318591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (97, 1), (107, 1), (12886318591, 1)] : List FactorBlock).map factorBlockValue).prod) = 267494201311979 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_97
      · exact prime_oneHundredFiftySixEX_107
      · exact prime_oneHundredFiftySixEX_12886318591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 267494201311979) ^ 133747100655989 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 267494201311979) ^ 2757672178474 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 267494201311979) ^ 2499945806654 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 267494201311979) ^ 20758 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_314803210756169 : Nat.Prime 314803210756169 := by
  apply lucas_primality 314803210756169 (3 : ZMod 314803210756169)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (113, 1), (971, 1), (1721, 1), (208387, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (113, 1), (971, 1), (1721, 1), (208387, 1)] : List FactorBlock).map factorBlockValue).prod) = 314803210756169 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_113
      · exact prime_oneHundredFiftySixEX_971
      · exact prime_oneHundredFiftySixEX_1721
      · exact prime_oneHundredFiftySixEX_208387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 314803210756169) ^ 157401605378084 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 314803210756169) ^ 2785869121736 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 314803210756169) ^ 324205160408 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 314803210756169) ^ 182918774408 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 314803210756169) ^ 1510666264 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_366020420757353 : Nat.Prime 366020420757353 := by
  apply lucas_primality 366020420757353 (3 : ZMod 366020420757353)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (45752552594669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (45752552594669, 1)] : List FactorBlock).map factorBlockValue).prod) = 366020420757353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_45752552594669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 366020420757353) ^ 183010210378676 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 366020420757353) ^ 8 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_400875657510611 : Nat.Prime 400875657510611 := by
  apply lucas_primality 400875657510611 (2 : ZMod 400875657510611)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (10163, 1), (3944461847, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (10163, 1), (3944461847, 1)] : List FactorBlock).map factorBlockValue).prod) = 400875657510611 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_5
      · exact prime_oneHundredFiftySixEX_10163
      · exact prime_oneHundredFiftySixEX_3944461847
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 400875657510611) ^ 200437828755305 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 400875657510611) ^ 80175131502122 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 400875657510611) ^ 39444618470 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 400875657510611) ^ 101630 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_540255582298987 : Nat.Prime 540255582298987 := by
  apply lucas_primality 540255582298987 (3 : ZMod 540255582298987)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (59, 1), (1741, 1), (13921, 1), (62969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (59, 1), (1741, 1), (13921, 1), (62969, 1)] : List FactorBlock).map factorBlockValue).prod) = 540255582298987 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_59
      · exact prime_oneHundredFiftySixEX_1741
      · exact prime_oneHundredFiftySixEX_13921
      · exact prime_oneHundredFiftySixEX_62969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 540255582298987) ^ 270127791149493 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 540255582298987) ^ 180085194099662 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 540255582298987) ^ 9156874276254 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 540255582298987) ^ 310313372946 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 540255582298987) ^ 38808676266 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 540255582298987) ^ 8579707194 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_685168690790093 : Nat.Prime 685168690790093 := by
  apply lucas_primality 685168690790093 (2 : ZMod 685168690790093)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (136849, 1), (1251687427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (136849, 1), (1251687427, 1)] : List FactorBlock).map factorBlockValue).prod) = 685168690790093 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_136849
      · exact prime_oneHundredFiftySixEX_1251687427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 685168690790093) ^ 342584345395046 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 685168690790093) ^ 5006749708 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 685168690790093) ^ 547396 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_1187826903350189 : Nat.Prime 1187826903350189 := by
  apply lucas_primality 1187826903350189 (2 : ZMod 1187826903350189)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (73, 1), (4067900353939, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (73, 1), (4067900353939, 1)] : List FactorBlock).map factorBlockValue).prod) = 1187826903350189 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_73
      · exact prime_oneHundredFiftySixEX_4067900353939
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1187826903350189) ^ 593913451675094 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1187826903350189) ^ 16271601415756 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1187826903350189) ^ 292 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_1214933700155953 : Nat.Prime 1214933700155953 := by
  apply lucas_primality 1214933700155953 (5 : ZMod 1214933700155953)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (7, 1), (1214749, 1), (2976643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (7, 1), (1214749, 1), (2976643, 1)] : List FactorBlock).map factorBlockValue).prod) = 1214933700155953 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_7
      · exact prime_oneHundredFiftySixEX_1214749
      · exact prime_oneHundredFiftySixEX_2976643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1214933700155953) ^ 607466850077976 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 1214933700155953) ^ 404977900051984 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 1214933700155953) ^ 173561957165136 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 1214933700155953) ^ 1000152048 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 1214933700155953) ^ 408155664 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_1789103977804019 : Nat.Prime 1789103977804019 := by
  apply lucas_primality 1789103977804019 (2 : ZMod 1789103977804019)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (947, 1), (121721, 1), (7760507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (947, 1), (121721, 1), (7760507, 1)] : List FactorBlock).map factorBlockValue).prod) = 1789103977804019 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_947
      · exact prime_oneHundredFiftySixEX_121721
      · exact prime_oneHundredFiftySixEX_7760507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1789103977804019) ^ 894551988902009 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1789103977804019) ^ 1889233345094 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1789103977804019) ^ 14698400258 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 1789103977804019) ^ 230539574 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_2399981386688101 : Nat.Prime 2399981386688101 := by
  apply lucas_primality 2399981386688101 (2 : ZMod 2399981386688101)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 2), (79, 1), (347, 1), (439, 1), (221587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 2), (79, 1), (347, 1), (439, 1), (221587, 1)] : List FactorBlock).map factorBlockValue).prod) = 2399981386688101 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_5
      · exact prime_oneHundredFiftySixEX_79
      · exact prime_oneHundredFiftySixEX_347
      · exact prime_oneHundredFiftySixEX_439
      · exact prime_oneHundredFiftySixEX_221587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2399981386688101) ^ 1199990693344050 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2399981386688101) ^ 799993795562700 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2399981386688101) ^ 479996277337620 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2399981386688101) ^ 30379511223900 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2399981386688101) ^ 6916372872300 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2399981386688101) ^ 5466927987900 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2399981386688101) ^ 10830876300 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_2682504973779523 : Nat.Prime 2682504973779523 := by
  apply lucas_primality 2682504973779523 (2 : ZMod 2682504973779523)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1223, 1), (365563501469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1223, 1), (365563501469, 1)] : List FactorBlock).map factorBlockValue).prod) = 2682504973779523 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_1223
      · exact prime_oneHundredFiftySixEX_365563501469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2682504973779523) ^ 1341252486889761 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2682504973779523) ^ 894168324593174 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2682504973779523) ^ 2193381008814 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2682504973779523) ^ 7338 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_2826609318187651 : Nat.Prime 2826609318187651 := by
  apply lucas_primality 2826609318187651 (2 : ZMod 2826609318187651)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (5, 2), (71119, 1), (9813527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (5, 2), (71119, 1), (9813527, 1)] : List FactorBlock).map factorBlockValue).prod) = 2826609318187651 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_5
      · exact prime_oneHundredFiftySixEX_71119
      · exact prime_oneHundredFiftySixEX_9813527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2826609318187651) ^ 1413304659093825 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2826609318187651) ^ 942203106062550 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2826609318187651) ^ 565321863637530 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2826609318187651) ^ 39744784350 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2826609318187651) ^ 288031950 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_3018803507790583 : Nat.Prime 3018803507790583 := by
  apply lucas_primality 3018803507790583 (3 : ZMod 3018803507790583)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1283, 1), (392154261859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1283, 1), (392154261859, 1)] : List FactorBlock).map factorBlockValue).prod) = 3018803507790583 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_1283
      · exact prime_oneHundredFiftySixEX_392154261859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3018803507790583) ^ 1509401753895291 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 3018803507790583) ^ 1006267835930194 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 3018803507790583) ^ 2352925571154 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 3018803507790583) ^ 7698 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_5942642162310803 : Nat.Prime 5942642162310803 := by
  apply lucas_primality 5942642162310803 (2 : ZMod 5942642162310803)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (83, 1), (113017, 1), (24366007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (83, 1), (113017, 1), (24366007, 1)] : List FactorBlock).map factorBlockValue).prod) = 5942642162310803 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_13
      · exact prime_oneHundredFiftySixEX_83
      · exact prime_oneHundredFiftySixEX_113017
      · exact prime_oneHundredFiftySixEX_24366007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5942642162310803) ^ 2971321081155401 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 5942642162310803) ^ 457126320177754 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 5942642162310803) ^ 71598098341094 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 5942642162310803) ^ 52581843106 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 5942642162310803) ^ 243890686 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_7602760547159623 : Nat.Prime 7602760547159623 := by
  apply lucas_primality 7602760547159623 (3 : ZMod 7602760547159623)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (97471289066149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (97471289066149, 1)] : List FactorBlock).map factorBlockValue).prod) = 7602760547159623 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_13
      · exact prime_oneHundredFiftySixEX_97471289066149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 7602760547159623) ^ 3801380273579811 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 7602760547159623) ^ 2534253515719874 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 7602760547159623) ^ 584827734396894 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 7602760547159623) ^ 78 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_8173464402104317 : Nat.Prime 8173464402104317 := by
  apply lucas_primality 8173464402104317 (14 : ZMod 8173464402104317)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (32434382548033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (32434382548033, 1)] : List FactorBlock).map factorBlockValue).prod) = 8173464402104317 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_7
      · exact prime_oneHundredFiftySixEX_32434382548033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 8173464402104317) ^ 4086732201052158 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (14 : ZMod 8173464402104317) ^ 2724488134034772 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (14 : ZMod 8173464402104317) ^ 1167637771729188 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (14 : ZMod 8173464402104317) ^ 252 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_8560070626452379 : Nat.Prime 8560070626452379 := by
  apply lucas_primality 8560070626452379 (2 : ZMod 8560070626452379)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (1093, 1), (118662433481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (1093, 1), (118662433481, 1)] : List FactorBlock).map factorBlockValue).prod) = 8560070626452379 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_11
      · exact prime_oneHundredFiftySixEX_1093
      · exact prime_oneHundredFiftySixEX_118662433481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8560070626452379) ^ 4280035313226189 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 8560070626452379) ^ 2853356875484126 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 8560070626452379) ^ 778188238768398 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 8560070626452379) ^ 7831720609746 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 8560070626452379) ^ 72138 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_9194337137883169 : Nat.Prime 9194337137883169 := by
  apply lucas_primality 9194337137883169 (19 : ZMod 9194337137883169)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 3), (23, 1), (462677996069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 3), (23, 1), (462677996069, 1)] : List FactorBlock).map factorBlockValue).prod) = 9194337137883169 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_23
      · exact prime_oneHundredFiftySixEX_462677996069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 9194337137883169) ^ 4597168568941584 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (19 : ZMod 9194337137883169) ^ 3064779045961056 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (19 : ZMod 9194337137883169) ^ 399753788603616 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (19 : ZMod 9194337137883169) ^ 19872 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_11164177654478881 : Nat.Prime 11164177654478881 := by
  apply lucas_primality 11164177654478881 (11 : ZMod 11164177654478881)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 1), (53597, 1), (433955323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 1), (53597, 1), (433955323, 1)] : List FactorBlock).map factorBlockValue).prod) = 11164177654478881 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_5
      · exact prime_oneHundredFiftySixEX_53597
      · exact prime_oneHundredFiftySixEX_433955323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 11164177654478881) ^ 5582088827239440 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (11 : ZMod 11164177654478881) ^ 3721392551492960 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (11 : ZMod 11164177654478881) ^ 2232835530895776 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (11 : ZMod 11164177654478881) ^ 208298555040 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (11 : ZMod 11164177654478881) ^ 25726560 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_11905620066913247 : Nat.Prime 11905620066913247 := by
  apply lucas_primality 11905620066913247 (5 : ZMod 11905620066913247)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (587, 1), (508271, 1), (19952099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (587, 1), (508271, 1), (19952099, 1)] : List FactorBlock).map factorBlockValue).prod) = 11905620066913247 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_587
      · exact prime_oneHundredFiftySixEX_508271
      · exact prime_oneHundredFiftySixEX_19952099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 11905620066913247) ^ 5952810033456623 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 11905620066913247) ^ 20282146621658 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 11905620066913247) ^ 23423764226 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 11905620066913247) ^ 596710154 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_13474097402382917 : Nat.Prime 13474097402382917 := by
  apply lucas_primality 13474097402382917 (2 : ZMod 13474097402382917)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (259117257738133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (259117257738133, 1)] : List FactorBlock).map factorBlockValue).prod) = 13474097402382917 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_13
      · exact prime_oneHundredFiftySixEX_259117257738133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 13474097402382917) ^ 6737048701191458 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 13474097402382917) ^ 1036469030952532 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 13474097402382917) ^ 52 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_16279918539612547 : Nat.Prime 16279918539612547 := by
  apply lucas_primality 16279918539612547 (7 : ZMod 16279918539612547)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (13, 1), (29816700622001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (13, 1), (29816700622001, 1)] : List FactorBlock).map factorBlockValue).prod) = 16279918539612547 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_7
      · exact prime_oneHundredFiftySixEX_13
      · exact prime_oneHundredFiftySixEX_29816700622001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 16279918539612547) ^ 8139959269806273 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (7 : ZMod 16279918539612547) ^ 5426639513204182 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (7 : ZMod 16279918539612547) ^ 2325702648516078 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (7 : ZMod 16279918539612547) ^ 1252301426124042 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (7 : ZMod 16279918539612547) ^ 546 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_23956794459495151 : Nat.Prime 23956794459495151 := by
  apply lucas_primality 23956794459495151 (6 : ZMod 23956794459495151)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (11, 1), (10531, 1), (1378717061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (11, 1), (10531, 1), (1378717061, 1)] : List FactorBlock).map factorBlockValue).prod) = 23956794459495151 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_5
      · exact prime_oneHundredFiftySixEX_11
      · exact prime_oneHundredFiftySixEX_10531
      · exact prime_oneHundredFiftySixEX_1378717061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 23956794459495151) ^ 11978397229747575 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 23956794459495151) ^ 7985598153165050 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 23956794459495151) ^ 4791358891899030 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 23956794459495151) ^ 2177890405408650 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 23956794459495151) ^ 2274883150650 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 23956794459495151) ^ 17376150 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_25862387424264449 : Nat.Prime 25862387424264449 := by
  apply lucas_primality 25862387424264449 (3 : ZMod 25862387424264449)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (7583, 1), (13322557151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (7583, 1), (13322557151, 1)] : List FactorBlock).map factorBlockValue).prod) = 25862387424264449 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_7583
      · exact prime_oneHundredFiftySixEX_13322557151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 25862387424264449) ^ 12931193712132224 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 25862387424264449) ^ 3410574630656 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 25862387424264449) ^ 1941248 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_71914646389345273 : Nat.Prime 71914646389345273 := by
  apply lucas_primality 71914646389345273 (5 : ZMod 71914646389345273)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (4273, 1), (233750183287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (4273, 1), (233750183287, 1)] : List FactorBlock).map factorBlockValue).prod) = 71914646389345273 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_4273
      · exact prime_oneHundredFiftySixEX_233750183287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 71914646389345273) ^ 35957323194672636 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 71914646389345273) ^ 23971548796448424 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 71914646389345273) ^ 16830013196664 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 71914646389345273) ^ 307656 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_79145060909254229 : Nat.Prime 79145060909254229 := by
  apply lucas_primality 79145060909254229 (2 : ZMod 79145060909254229)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (2826609318187651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (2826609318187651, 1)] : List FactorBlock).map factorBlockValue).prod) = 79145060909254229 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_7
      · exact prime_oneHundredFiftySixEX_2826609318187651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 79145060909254229) ^ 39572530454627114 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 79145060909254229) ^ 11306437272750604 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 79145060909254229) ^ 28 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_88424436268679879 : Nat.Prime 88424436268679879 := by
  apply lucas_primality 88424436268679879 (7 : ZMod 88424436268679879)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2677099, 1), (16514973161, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2677099, 1), (16514973161, 1)] : List FactorBlock).map factorBlockValue).prod) = 88424436268679879 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_2677099
      · exact prime_oneHundredFiftySixEX_16514973161
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 88424436268679879) ^ 44212218134339939 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (7 : ZMod 88424436268679879) ^ 33029946322 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (7 : ZMod 88424436268679879) ^ 5354198 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_101014991469007579 : Nat.Prime 101014991469007579 := by
  apply lucas_primality 101014991469007579 (2 : ZMod 101014991469007579)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (67, 1), (27920119256221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (67, 1), (27920119256221, 1)] : List FactorBlock).map factorBlockValue).prod) = 101014991469007579 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_67
      · exact prime_oneHundredFiftySixEX_27920119256221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 101014991469007579) ^ 50507495734503789 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 101014991469007579) ^ 33671663823002526 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 101014991469007579) ^ 1507686439835934 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 101014991469007579) ^ 3618 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_143982983799976589 : Nat.Prime 143982983799976589 := by
  apply lucas_primality 143982983799976589 (2 : ZMod 143982983799976589)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (22284553, 1), (95016347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (22284553, 1), (95016347, 1)] : List FactorBlock).map factorBlockValue).prod) = 143982983799976589 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_17
      · exact prime_oneHundredFiftySixEX_22284553
      · exact prime_oneHundredFiftySixEX_95016347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 143982983799976589) ^ 71991491899988294 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 143982983799976589) ^ 8469587282351564 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 143982983799976589) ^ 6461111596 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 143982983799976589) ^ 1515349604 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_177112743868002511 : Nat.Prime 177112743868002511 := by
  apply lucas_primality 177112743868002511 (6 : ZMod 177112743868002511)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (281, 1), (678593, 1), (10320283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (281, 1), (678593, 1), (10320283, 1)] : List FactorBlock).map factorBlockValue).prod) = 177112743868002511 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_5
      · exact prime_oneHundredFiftySixEX_281
      · exact prime_oneHundredFiftySixEX_678593
      · exact prime_oneHundredFiftySixEX_10320283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 177112743868002511) ^ 88556371934001255 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 177112743868002511) ^ 59037581289334170 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 177112743868002511) ^ 35422548773600502 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 177112743868002511) ^ 630294462163710 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 177112743868002511) ^ 260999957070 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 177112743868002511) ^ 17161616970 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_182693727494674037 : Nat.Prime 182693727494674037 := by
  apply lucas_primality 182693727494674037 (2 : ZMod 182693727494674037)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (109, 2), (3727, 1), (1031457307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (109, 2), (3727, 1), (1031457307, 1)] : List FactorBlock).map factorBlockValue).prod) = 182693727494674037 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_109
      · exact prime_oneHundredFiftySixEX_3727
      · exact prime_oneHundredFiftySixEX_1031457307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 182693727494674037) ^ 91346863747337018 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 182693727494674037) ^ 1676089243070404 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 182693727494674037) ^ 49018977057868 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 182693727494674037) ^ 177121948 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_198950482390006177 : Nat.Prime 198950482390006177 := by
  apply lucas_primality 198950482390006177 (5 : ZMod 198950482390006177)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (47, 1), (52757, 1), (835787389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (47, 1), (52757, 1), (835787389, 1)] : List FactorBlock).map factorBlockValue).prod) = 198950482390006177 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_47
      · exact prime_oneHundredFiftySixEX_52757
      · exact prime_oneHundredFiftySixEX_835787389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 198950482390006177) ^ 99475241195003088 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 198950482390006177) ^ 66316827463335392 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 198950482390006177) ^ 4232988987021408 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 198950482390006177) ^ 3771072699168 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 198950482390006177) ^ 238039584 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_265946010870138941 : Nat.Prime 265946010870138941 := by
  apply lucas_primality 265946010870138941 (2 : ZMod 265946010870138941)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (11, 2), (131, 1), (631, 1), (12073, 1), (110119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (11, 2), (131, 1), (631, 1), (12073, 1), (110119, 1)] : List FactorBlock).map factorBlockValue).prod) = 265946010870138941 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_5
      · exact prime_oneHundredFiftySixEX_11
      · exact prime_oneHundredFiftySixEX_131
      · exact prime_oneHundredFiftySixEX_631
      · exact prime_oneHundredFiftySixEX_12073
      · exact prime_oneHundredFiftySixEX_110119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 265946010870138941) ^ 132973005435069470 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 265946010870138941) ^ 53189202174027788 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 265946010870138941) ^ 24176910079103540 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 265946010870138941) ^ 2030122220382740 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 265946010870138941) ^ 421467529112740 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 265946010870138941) ^ 22028162914780 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 265946010870138941) ^ 2415078332260 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_350326532461955843 : Nat.Prime 350326532461955843 := by
  apply lucas_primality 350326532461955843 (2 : ZMod 350326532461955843)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (13474097402382917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (13474097402382917, 1)] : List FactorBlock).map factorBlockValue).prod) = 350326532461955843 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_13
      · exact prime_oneHundredFiftySixEX_13474097402382917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 350326532461955843) ^ 175163266230977921 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 350326532461955843) ^ 26948194804765834 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 350326532461955843) ^ 26 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_467644591344983909 : Nat.Prime 467644591344983909 := by
  apply lucas_primality 467644591344983909 (2 : ZMod 467644591344983909)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (4733, 1), (7919, 1), (3119242051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (4733, 1), (7919, 1), (3119242051, 1)] : List FactorBlock).map factorBlockValue).prod) = 467644591344983909 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_4733
      · exact prime_oneHundredFiftySixEX_7919
      · exact prime_oneHundredFiftySixEX_3119242051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 467644591344983909) ^ 233822295672491954 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 467644591344983909) ^ 98805111207476 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 467644591344983909) ^ 59053490509532 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 467644591344983909) ^ 149922508 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_638983830804654331 : Nat.Prime 638983830804654331 := by
  apply lucas_primality 638983830804654331 (10 : ZMod 638983830804654331)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (19, 1), (59, 1), (13729, 1), (153773531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (19, 1), (59, 1), (13729, 1), (153773531, 1)] : List FactorBlock).map factorBlockValue).prod) = 638983830804654331 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_5
      · exact prime_oneHundredFiftySixEX_19
      · exact prime_oneHundredFiftySixEX_59
      · exact prime_oneHundredFiftySixEX_13729
      · exact prime_oneHundredFiftySixEX_153773531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 638983830804654331) ^ 319491915402327165 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (10 : ZMod 638983830804654331) ^ 212994610268218110 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (10 : ZMod 638983830804654331) ^ 127796766160930866 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (10 : ZMod 638983830804654331) ^ 33630727937087070 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (10 : ZMod 638983830804654331) ^ 10830234420417870 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (10 : ZMod 638983830804654331) ^ 46542634627770 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (10 : ZMod 638983830804654331) ^ 4155356430 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_689576496218686451 : Nat.Prime 689576496218686451 := by
  apply lucas_primality 689576496218686451 (2 : ZMod 689576496218686451)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (11, 3), (43, 1), (619, 1), (653, 1), (596159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (11, 3), (43, 1), (619, 1), (653, 1), (596159, 1)] : List FactorBlock).map factorBlockValue).prod) = 689576496218686451 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_5
      · exact prime_oneHundredFiftySixEX_11
      · exact prime_oneHundredFiftySixEX_43
      · exact prime_oneHundredFiftySixEX_619
      · exact prime_oneHundredFiftySixEX_653
      · exact prime_oneHundredFiftySixEX_596159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 689576496218686451) ^ 344788248109343225 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 689576496218686451) ^ 137915299243737290 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 689576496218686451) ^ 62688772383516950 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 689576496218686451) ^ 16036662702760150 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 689576496218686451) ^ 1114016956734550 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 689576496218686451) ^ 1056013011054650 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 689576496218686451) ^ 1156698961550 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_767125153289140397 : Nat.Prime 767125153289140397 := by
  apply lucas_primality 767125153289140397 (2 : ZMod 767125153289140397)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (32531, 1), (256319107423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (32531, 1), (256319107423, 1)] : List FactorBlock).map factorBlockValue).prod) = 767125153289140397 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_23
      · exact prime_oneHundredFiftySixEX_32531
      · exact prime_oneHundredFiftySixEX_256319107423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 767125153289140397) ^ 383562576644570198 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 767125153289140397) ^ 33353267534310452 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 767125153289140397) ^ 23581357882916 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 767125153289140397) ^ 2992852 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_797308364437574333 : Nat.Prime 797308364437574333 := by
  apply lucas_primality 797308364437574333 (2 : ZMod 797308364437574333)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (37, 1), (19297753, 1), (39880429, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (37, 1), (19297753, 1), (39880429, 1)] : List FactorBlock).map factorBlockValue).prod) = 797308364437574333 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_7
      · exact prime_oneHundredFiftySixEX_37
      · exact prime_oneHundredFiftySixEX_19297753
      · exact prime_oneHundredFiftySixEX_39880429
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 797308364437574333) ^ 398654182218787166 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 797308364437574333) ^ 113901194919653476 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 797308364437574333) ^ 21548874714529036 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 797308364437574333) ^ 41316124444 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 797308364437574333) ^ 19992472108 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_1473596414167950607 : Nat.Prime 1473596414167950607 := by
  apply lucas_primality 1473596414167950607 (3 : ZMod 1473596414167950607)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (109, 1), (173, 1), (883, 1), (14750067271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (109, 1), (173, 1), (883, 1), (14750067271, 1)] : List FactorBlock).map factorBlockValue).prod) = 1473596414167950607 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_109
      · exact prime_oneHundredFiftySixEX_173
      · exact prime_oneHundredFiftySixEX_883
      · exact prime_oneHundredFiftySixEX_14750067271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1473596414167950607) ^ 736798207083975303 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1473596414167950607) ^ 491198804722650202 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1473596414167950607) ^ 13519233157504134 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1473596414167950607) ^ 8517898347791622 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1473596414167950607) ^ 1668852111175482 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1473596414167950607) ^ 99904386 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_1492065108799822793 : Nat.Prime 1492065108799822793 := by
  apply lucas_primality 1492065108799822793 (3 : ZMod 1492065108799822793)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (23, 1), (47981, 1), (88873, 1), (1901651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (23, 1), (47981, 1), (88873, 1), (1901651, 1)] : List FactorBlock).map factorBlockValue).prod) = 1492065108799822793 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_23
      · exact prime_oneHundredFiftySixEX_47981
      · exact prime_oneHundredFiftySixEX_88873
      · exact prime_oneHundredFiftySixEX_1901651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1492065108799822793) ^ 746032554399911396 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1492065108799822793) ^ 64872396034774904 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1492065108799822793) ^ 31096998995432 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1492065108799822793) ^ 16788733460104 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1492065108799822793) ^ 784615635992 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_2220502305087140441 : Nat.Prime 2220502305087140441 := by
  apply lucas_primality 2220502305087140441 (3 : ZMod 2220502305087140441)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (101, 1), (191, 1), (48017, 1), (59929613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (101, 1), (191, 1), (48017, 1), (59929613, 1)] : List FactorBlock).map factorBlockValue).prod) = 2220502305087140441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_5
      · exact prime_oneHundredFiftySixEX_101
      · exact prime_oneHundredFiftySixEX_191
      · exact prime_oneHundredFiftySixEX_48017
      · exact prime_oneHundredFiftySixEX_59929613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2220502305087140441) ^ 1110251152543570220 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 444100461017428088 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 21985171337496440 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 11625666518780840 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 46244086575320 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 37051837880 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_2716591753548710909 : Nat.Prime 2716591753548710909 := by
  apply lucas_primality 2716591753548710909 (2 : ZMod 2716591753548710909)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (43, 1), (1214933700155953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (43, 1), (1214933700155953, 1)] : List FactorBlock).map factorBlockValue).prod) = 2716591753548710909 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_13
      · exact prime_oneHundredFiftySixEX_43
      · exact prime_oneHundredFiftySixEX_1214933700155953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2716591753548710909) ^ 1358295876774355454 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2716591753548710909) ^ 208968596426823916 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2716591753548710909) ^ 63176552408109556 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2716591753548710909) ^ 2236 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_2825652830745808043 : Nat.Prime 2825652830745808043 := by
  apply lucas_primality 2825652830745808043 (2 : ZMod 2825652830745808043)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (23, 1), (293, 1), (1745927, 1), (2450593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (23, 1), (293, 1), (1745927, 1), (2450593, 1)] : List FactorBlock).map factorBlockValue).prod) = 2825652830745808043 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_7
      · exact prime_oneHundredFiftySixEX_23
      · exact prime_oneHundredFiftySixEX_293
      · exact prime_oneHundredFiftySixEX_1745927
      · exact prime_oneHundredFiftySixEX_2450593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2825652830745808043) ^ 1412826415372904021 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2825652830745808043) ^ 403664690106544006 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2825652830745808043) ^ 122854470901991654 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2825652830745808043) ^ 9643866316538594 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2825652830745808043) ^ 1618425530246 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 2825652830745808043) ^ 1153048601194 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_2927544154246713619 : Nat.Prime 2927544154246713619 := by
  apply lucas_primality 2927544154246713619 (3 : ZMod 2927544154246713619)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (19, 1), (8560070626452379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (19, 1), (8560070626452379, 1)] : List FactorBlock).map factorBlockValue).prod) = 2927544154246713619 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_19
      · exact prime_oneHundredFiftySixEX_8560070626452379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2927544154246713619) ^ 1463772077123356809 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 2927544154246713619) ^ 975848051415571206 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 2927544154246713619) ^ 154081271276142822 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 2927544154246713619) ^ 342 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_3014995691311940443 : Nat.Prime 3014995691311940443 := by
  apply lucas_primality 3014995691311940443 (2 : ZMod 3014995691311940443)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (321187, 1), (1564506913061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (321187, 1), (1564506913061, 1)] : List FactorBlock).map factorBlockValue).prod) = 3014995691311940443 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_321187
      · exact prime_oneHundredFiftySixEX_1564506913061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3014995691311940443) ^ 1507497845655970221 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 3014995691311940443) ^ 1004998563770646814 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 3014995691311940443) ^ 9387041478366 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 3014995691311940443) ^ 1927122 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_3297234682738046579 : Nat.Prime 3297234682738046579 := by
  apply lucas_primality 3297234682738046579 (2 : ZMod 3297234682738046579)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (11467, 1), (66377, 1), (196906361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (11467, 1), (66377, 1), (196906361, 1)] : List FactorBlock).map factorBlockValue).prod) = 3297234682738046579 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_11
      · exact prime_oneHundredFiftySixEX_11467
      · exact prime_oneHundredFiftySixEX_66377
      · exact prime_oneHundredFiftySixEX_196906361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3297234682738046579) ^ 1648617341369023289 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 3297234682738046579) ^ 299748607521640598 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 3297234682738046579) ^ 287541177530134 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 3297234682738046579) ^ 49674355314914 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 3297234682738046579) ^ 16745191298 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_7270706726899630967 : Nat.Prime 7270706726899630967 := by
  apply lucas_primality 7270706726899630967 (5 : ZMod 7270706726899630967)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (337, 1), (15373, 1), (134171, 1), (747139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (337, 1), (15373, 1), (134171, 1), (747139, 1)] : List FactorBlock).map factorBlockValue).prod) = 7270706726899630967 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_7
      · exact prime_oneHundredFiftySixEX_337
      · exact prime_oneHundredFiftySixEX_15373
      · exact prime_oneHundredFiftySixEX_134171
      · exact prime_oneHundredFiftySixEX_747139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 7270706726899630967) ^ 3635353363449815483 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 7270706726899630967) ^ 1038672389557090138 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 7270706726899630967) ^ 21574797409197718 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 7270706726899630967) ^ 472953016776142 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 7270706726899630967) ^ 54189852702146 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 7270706726899630967) ^ 9731397674194 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_9051852206305875919 : Nat.Prime 9051852206305875919 := by
  apply lucas_primality 9051852206305875919 (3 : ZMod 9051852206305875919)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (9829, 1), (23719, 1), (924447929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (9829, 1), (23719, 1), (924447929, 1)] : List FactorBlock).map factorBlockValue).prod) = 9051852206305875919 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_7
      · exact prime_oneHundredFiftySixEX_9829
      · exact prime_oneHundredFiftySixEX_23719
      · exact prime_oneHundredFiftySixEX_924447929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 9051852206305875919) ^ 4525926103152937959 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 9051852206305875919) ^ 3017284068768625306 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 9051852206305875919) ^ 1293121743757982274 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 9051852206305875919) ^ 920933177973942 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 9051852206305875919) ^ 381628745153922 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 9051852206305875919) ^ 9791630142 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_9310276483619584019 : Nat.Prime 9310276483619584019 := by
  apply lucas_primality 9310276483619584019 (2 : ZMod 9310276483619584019)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13, 2), (101, 1), (37573, 1), (1036932751, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13, 2), (101, 1), (37573, 1), (1036932751, 1)] : List FactorBlock).map factorBlockValue).prod) = 9310276483619584019 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_7
      · exact prime_oneHundredFiftySixEX_13
      · exact prime_oneHundredFiftySixEX_101
      · exact prime_oneHundredFiftySixEX_37573
      · exact prime_oneHundredFiftySixEX_1036932751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9310276483619584019) ^ 4655138241809792009 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 9310276483619584019) ^ 1330039497659940574 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 9310276483619584019) ^ 716175114124583386 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 9310276483619584019) ^ 92180955283362218 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 9310276483619584019) ^ 247791671775466 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 9310276483619584019) ^ 8978669518 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_12917038922669744117 : Nat.Prime 12917038922669744117 := by
  apply lucas_primality 12917038922669744117 (2 : ZMod 12917038922669744117)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29772199, 1), (108465610171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29772199, 1), (108465610171, 1)] : List FactorBlock).map factorBlockValue).prod) = 12917038922669744117 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_29772199
      · exact prime_oneHundredFiftySixEX_108465610171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 12917038922669744117) ^ 6458519461334872058 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 12917038922669744117) ^ 433862440684 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 12917038922669744117) ^ 119088796 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_13311937837557174217 : Nat.Prime 13311937837557174217 := by
  apply lucas_primality 13311937837557174217 (5 : ZMod 13311937837557174217)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (4253, 1), (130417135331503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (4253, 1), (130417135331503, 1)] : List FactorBlock).map factorBlockValue).prod) = 13311937837557174217 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_4253
      · exact prime_oneHundredFiftySixEX_130417135331503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 13311937837557174217) ^ 6655968918778587108 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 13311937837557174217) ^ 4437312612519058072 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 13311937837557174217) ^ 3130011247956072 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 13311937837557174217) ^ 102072 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_20633663004195807739 : Nat.Prime 20633663004195807739 := by
  apply lucas_primality 20633663004195807739 (2 : ZMod 20633663004195807739)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (6491, 1), (176600617985551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (6491, 1), (176600617985551, 1)] : List FactorBlock).map factorBlockValue).prod) = 20633663004195807739 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_6491
      · exact prime_oneHundredFiftySixEX_176600617985551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 20633663004195807739) ^ 10316831502097903869 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 20633663004195807739) ^ 6877887668065269246 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 20633663004195807739) ^ 3178811123739918 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 20633663004195807739) ^ 116838 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_38447018787178690537 : Nat.Prime 38447018787178690537 := by
  apply lucas_primality 38447018787178690537 (5 : ZMod 38447018787178690537)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (499, 1), (38333, 1), (41513, 1), (2017409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (499, 1), (38333, 1), (41513, 1), (2017409, 1)] : List FactorBlock).map factorBlockValue).prod) = 38447018787178690537 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_499
      · exact prime_oneHundredFiftySixEX_38333
      · exact prime_oneHundredFiftySixEX_41513
      · exact prime_oneHundredFiftySixEX_2017409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 38447018787178690537) ^ 19223509393589345268 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 38447018787178690537) ^ 12815672929059563512 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 38447018787178690537) ^ 77048133842041464 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 38447018787178690537) ^ 1002974429008392 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 38447018787178690537) ^ 926144070223272 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 38447018787178690537) ^ 19057622320104 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_42376090025613958487 : Nat.Prime 42376090025613958487 := by
  apply lucas_primality 42376090025613958487 (5 : ZMod 42376090025613958487)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (37, 1), (1049, 1), (1446257, 1), (16411201, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (37, 1), (1049, 1), (1446257, 1), (16411201, 1)] : List FactorBlock).map factorBlockValue).prod) = 42376090025613958487 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_23
      · exact prime_oneHundredFiftySixEX_37
      · exact prime_oneHundredFiftySixEX_1049
      · exact prime_oneHundredFiftySixEX_1446257
      · exact prime_oneHundredFiftySixEX_16411201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 42376090025613958487) ^ 21188045012806979243 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 42376090025613958487) ^ 1842438696765824282 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 42376090025613958487) ^ 1145299730421998878 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 42376090025613958487) ^ 40396653980566214 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 42376090025613958487) ^ 29300525442998 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 42376090025613958487) ^ 2582144355286 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_43392789259089243619 : Nat.Prime 43392789259089243619 := by
  apply lucas_primality 43392789259089243619 (2 : ZMod 43392789259089243619)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (317, 1), (433, 1), (52688903207623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (317, 1), (433, 1), (52688903207623, 1)] : List FactorBlock).map factorBlockValue).prod) = 43392789259089243619 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_317
      · exact prime_oneHundredFiftySixEX_433
      · exact prime_oneHundredFiftySixEX_52688903207623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 43392789259089243619) ^ 21696394629544621809 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 43392789259089243619) ^ 14464263086363081206 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 43392789259089243619) ^ 136885770533404554 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 43392789259089243619) ^ 100214293900898946 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 43392789259089243619) ^ 823566 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_56118296425536623357 : Nat.Prime 56118296425536623357 := by
  apply lucas_primality 56118296425536623357 (2 : ZMod 56118296425536623357)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (431, 1), (433, 1), (5782770656261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (431, 1), (433, 1), (5782770656261, 1)] : List FactorBlock).map factorBlockValue).prod) = 56118296425536623357 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_13
      · exact prime_oneHundredFiftySixEX_431
      · exact prime_oneHundredFiftySixEX_433
      · exact prime_oneHundredFiftySixEX_5782770656261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 56118296425536623357) ^ 28059148212768311678 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 56118296425536623357) ^ 4316792032733586412 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 56118296425536623357) ^ 130204864096372676 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 56118296425536623357) ^ 129603455948121532 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 56118296425536623357) ^ 9704396 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_105131039647847779157 : Nat.Prime 105131039647847779157 := by
  apply lucas_primality 105131039647847779157 (2 : ZMod 105131039647847779157)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (31, 1), (173, 1), (1831, 1), (2676546708113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (31, 1), (173, 1), (1831, 1), (2676546708113, 1)] : List FactorBlock).map factorBlockValue).prod) = 105131039647847779157 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_31
      · exact prime_oneHundredFiftySixEX_173
      · exact prime_oneHundredFiftySixEX_1831
      · exact prime_oneHundredFiftySixEX_2676546708113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 105131039647847779157) ^ 52565519823923889578 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 105131039647847779157) ^ 3391323859607992876 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 105131039647847779157) ^ 607693870796807972 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 105131039647847779157) ^ 57417279982440076 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 105131039647847779157) ^ 39278612 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_124478453735397502303 : Nat.Prime 124478453735397502303 := by
  apply lucas_primality 124478453735397502303 (19 : ZMod 124478453735397502303)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (404017, 1), (51350336634101, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (404017, 1), (51350336634101, 1)] : List FactorBlock).map factorBlockValue).prod) = 124478453735397502303 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_404017
      · exact prime_oneHundredFiftySixEX_51350336634101
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 124478453735397502303) ^ 62239226867698751151 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (19 : ZMod 124478453735397502303) ^ 41492817911799167434 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (19 : ZMod 124478453735397502303) ^ 308102019804606 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (19 : ZMod 124478453735397502303) ^ 2424102 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_218189037145273558283 : Nat.Prime 218189037145273558283 := by
  apply lucas_primality 218189037145273558283 (2 : ZMod 218189037145273558283)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (41, 1), (71914646389345273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (41, 1), (71914646389345273, 1)] : List FactorBlock).map factorBlockValue).prod) = 218189037145273558283 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_37
      · exact prime_oneHundredFiftySixEX_41
      · exact prime_oneHundredFiftySixEX_71914646389345273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 218189037145273558283) ^ 109094518572636779141 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 218189037145273558283) ^ 5897001003926312386 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 218189037145273558283) ^ 5321683832811550202 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 218189037145273558283) ^ 3034 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_236188911554202791671 : Nat.Prime 236188911554202791671 := by
  apply lucas_primality 236188911554202791671 (6 : ZMod 236188911554202791671)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (23, 1), (37, 1), (1289, 1), (7177211967551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (23, 1), (37, 1), (1289, 1), (7177211967551, 1)] : List FactorBlock).map factorBlockValue).prod) = 236188911554202791671 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_5
      · exact prime_oneHundredFiftySixEX_23
      · exact prime_oneHundredFiftySixEX_37
      · exact prime_oneHundredFiftySixEX_1289
      · exact prime_oneHundredFiftySixEX_7177211967551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 236188911554202791671) ^ 118094455777101395835 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 236188911554202791671) ^ 78729637184734263890 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 236188911554202791671) ^ 47237782310840558334 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 236188911554202791671) ^ 10269083111052295290 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 236188911554202791671) ^ 6383484096059534910 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 236188911554202791671) ^ 183234221531577030 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 236188911554202791671) ^ 32908170 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_256223811061086791179 : Nat.Prime 256223811061086791179 := by
  apply lucas_primality 256223811061086791179 (2 : ZMod 256223811061086791179)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (6863, 1), (366020420757353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (6863, 1), (366020420757353, 1)] : List FactorBlock).map factorBlockValue).prod) = 256223811061086791179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_17
      · exact prime_oneHundredFiftySixEX_6863
      · exact prime_oneHundredFiftySixEX_366020420757353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 256223811061086791179) ^ 128111905530543395589 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 85407937020362263726 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 15071988885946281834 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 37334082917250006 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 700026 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_313010856169636387583 : Nat.Prime 313010856169636387583 := by
  apply lucas_primality 313010856169636387583 (5 : ZMod 313010856169636387583)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1447, 1), (32084053, 1), (3371100101, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1447, 1), (32084053, 1), (3371100101, 1)] : List FactorBlock).map factorBlockValue).prod) = 313010856169636387583 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_1447
      · exact prime_oneHundredFiftySixEX_32084053
      · exact prime_oneHundredFiftySixEX_3371100101
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 313010856169636387583) ^ 156505428084818193791 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 313010856169636387583) ^ 216317108617578706 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 313010856169636387583) ^ 9755963692294 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 313010856169636387583) ^ 92851249382 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_514981769046947239237 : Nat.Prime 514981769046947239237 := by
  apply lucas_primality 514981769046947239237 (2 : ZMod 514981769046947239237)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (509, 1), (69337351, 1), (1215977617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (509, 1), (69337351, 1), (1215977617, 1)] : List FactorBlock).map factorBlockValue).prod) = 514981769046947239237 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_509
      · exact prime_oneHundredFiftySixEX_69337351
      · exact prime_oneHundredFiftySixEX_1215977617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 514981769046947239237) ^ 257490884523473619618 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 514981769046947239237) ^ 171660589682315746412 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 514981769046947239237) ^ 1011752002056870804 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 514981769046947239237) ^ 7427191284636 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 514981769046947239237) ^ 423512539908 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_601135034269270369663 : Nat.Prime 601135034269270369663 := by
  apply lucas_primality 601135034269270369663 (3 : ZMod 601135034269270369663)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (101, 1), (142641539, 1), (2318099881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (101, 1), (142641539, 1), (2318099881, 1)] : List FactorBlock).map factorBlockValue).prod) = 601135034269270369663 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_101
      · exact prime_oneHundredFiftySixEX_142641539
      · exact prime_oneHundredFiftySixEX_2318099881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 601135034269270369663) ^ 300567517134635184831 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 601135034269270369663) ^ 200378344756423456554 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 601135034269270369663) ^ 5951832022468023462 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 601135034269270369663) ^ 4214305583658 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 601135034269270369663) ^ 259322317902 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_1974953228379788548193 : Nat.Prime 1974953228379788548193 := by
  apply lucas_primality 1974953228379788548193 (3 : ZMod 1974953228379788548193)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (7, 1), (43, 1), (5087, 1), (22469, 1), (23833, 1), (75269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (7, 1), (43, 1), (5087, 1), (22469, 1), (23833, 1), (75269, 1)] : List FactorBlock).map factorBlockValue).prod) = 1974953228379788548193 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_7
      · exact prime_oneHundredFiftySixEX_43
      · exact prime_oneHundredFiftySixEX_5087
      · exact prime_oneHundredFiftySixEX_22469
      · exact prime_oneHundredFiftySixEX_23833
      · exact prime_oneHundredFiftySixEX_75269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1974953228379788548193) ^ 987476614189894274096 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1974953228379788548193) ^ 282136175482826935456 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1974953228379788548193) ^ 45929144846041594144 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1974953228379788548193) ^ 388235350575936416 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1974953228379788548193) ^ 87896801298668768 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1974953228379788548193) ^ 82866329391171424 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1974953228379788548193) ^ 26238600597587168 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_3074685732733041494149 : Nat.Prime 3074685732733041494149 := by
  apply lucas_primality 3074685732733041494149 (2 : ZMod 3074685732733041494149)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (256223811061086791179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (256223811061086791179, 1)] : List FactorBlock).map factorBlockValue).prod) = 3074685732733041494149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_256223811061086791179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3074685732733041494149) ^ 1537342866366520747074 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 3074685732733041494149) ^ 1024895244244347164716 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 3074685732733041494149) ^ 12 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_5746208106092056929421 : Nat.Prime 5746208106092056929421 := by
  apply lucas_primality 5746208106092056929421 (2 : ZMod 5746208106092056929421)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (1381, 1), (230703019, 1), (300595963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (1381, 1), (230703019, 1), (300595963, 1)] : List FactorBlock).map factorBlockValue).prod) = 5746208106092056929421 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_5
      · exact prime_oneHundredFiftySixEX_1381
      · exact prime_oneHundredFiftySixEX_230703019
      · exact prime_oneHundredFiftySixEX_300595963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5746208106092056929421) ^ 2873104053046028464710 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 5746208106092056929421) ^ 1915402702030685643140 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 5746208106092056929421) ^ 1149241621218411385884 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 5746208106092056929421) ^ 4160903769798737820 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 5746208106092056929421) ^ 24907381494180 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 5746208106092056929421) ^ 19116052154340 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_10099452370000124779513 : Nat.Prime 10099452370000124779513 := by
  apply lucas_primality 10099452370000124779513 (7 : ZMod 10099452370000124779513)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (643, 1), (1259, 1), (2353297, 1), (220888517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (643, 1), (1259, 1), (2353297, 1), (220888517, 1)] : List FactorBlock).map factorBlockValue).prod) = 10099452370000124779513 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_643
      · exact prime_oneHundredFiftySixEX_1259
      · exact prime_oneHundredFiftySixEX_2353297
      · exact prime_oneHundredFiftySixEX_220888517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 10099452370000124779513) ^ 5049726185000062389756 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (7 : ZMod 10099452370000124779513) ^ 3366484123333374926504 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (7 : ZMod 10099452370000124779513) ^ 15706768849144828584 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (7 : ZMod 10099452370000124779513) ^ 8021804900714952168 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (7 : ZMod 10099452370000124779513) ^ 4291618257279096 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (7 : ZMod 10099452370000124779513) ^ 45721943843736 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_15650542808481819379151 : Nat.Prime 15650542808481819379151 := by
  apply lucas_primality 15650542808481819379151 (23 : ZMod 15650542808481819379151)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (313010856169636387583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (313010856169636387583, 1)] : List FactorBlock).map factorBlockValue).prod) = 15650542808481819379151 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_5
      · exact prime_oneHundredFiftySixEX_313010856169636387583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (23 : ZMod 15650542808481819379151) ^ 7825271404240909689575 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (23 : ZMod 15650542808481819379151) ^ 3130108561696363875830 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (23 : ZMod 15650542808481819379151) ^ 50 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_22415780398476041206859 : Nat.Prime 22415780398476041206859 := by
  apply lucas_primality 22415780398476041206859 (2 : ZMod 22415780398476041206859)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (15743483669, 1), (711906617041, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (15743483669, 1), (711906617041, 1)] : List FactorBlock).map factorBlockValue).prod) = 22415780398476041206859 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_15743483669
      · exact prime_oneHundredFiftySixEX_711906617041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 22415780398476041206859) ^ 11207890199238020603429 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 22415780398476041206859) ^ 1423813234082 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 22415780398476041206859) ^ 31486967338 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_42366396508405186569217 : Nat.Prime 42366396508405186569217 := by
  apply lucas_primality 42366396508405186569217 (11 : ZMod 42366396508405186569217)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 10), (3, 1), (283, 1), (29567803, 1), (1648142747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 10), (3, 1), (283, 1), (29567803, 1), (1648142747, 1)] : List FactorBlock).map factorBlockValue).prod) = 42366396508405186569217 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_283
      · exact prime_oneHundredFiftySixEX_29567803
      · exact prime_oneHundredFiftySixEX_1648142747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 42366396508405186569217) ^ 21183198254202593284608 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (11 : ZMod 42366396508405186569217) ^ 14122132169468395523072 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (11 : ZMod 42366396508405186569217) ^ 149704581301785111552 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (11 : ZMod 42366396508405186569217) ^ 1432855748815872 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (11 : ZMod 42366396508405186569217) ^ 25705538300928 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_47886543588161587791203 : Nat.Prime 47886543588161587791203 := by
  apply lucas_primality 47886543588161587791203 (2 : ZMod 47886543588161587791203)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (14201963, 1), (240844691621461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (14201963, 1), (240844691621461, 1)] : List FactorBlock).map factorBlockValue).prod) = 47886543588161587791203 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_7
      · exact prime_oneHundredFiftySixEX_14201963
      · exact prime_oneHundredFiftySixEX_240844691621461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 47886543588161587791203) ^ 23943271794080793895601 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 47886543588161587791203) ^ 6840934798308798255886 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 47886543588161587791203) ^ 3371825682700454 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 47886543588161587791203) ^ 198827482 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_97087758339807459492347 : Nat.Prime 97087758339807459492347 := by
  apply lucas_primality 97087758339807459492347 (2 : ZMod 97087758339807459492347)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (19469, 1), (285501439, 1), (671798731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (19469, 1), (285501439, 1), (671798731, 1)] : List FactorBlock).map factorBlockValue).prod) = 97087758339807459492347 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_13
      · exact prime_oneHundredFiftySixEX_19469
      · exact prime_oneHundredFiftySixEX_285501439
      · exact prime_oneHundredFiftySixEX_671798731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 97087758339807459492347) ^ 48543879169903729746173 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 97087758339807459492347) ^ 7468289103062112268642 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 97087758339807459492347) ^ 4986787114890721634 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 97087758339807459492347) ^ 340060486839814 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 97087758339807459492347) ^ 144519115413166 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_114270582252405377601457 : Nat.Prime 114270582252405377601457 := by
  apply lucas_primality 114270582252405377601457 (5 : ZMod 114270582252405377601457)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (263, 1), (9051852206305875919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (263, 1), (9051852206305875919, 1)] : List FactorBlock).map factorBlockValue).prod) = 114270582252405377601457 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_263
      · exact prime_oneHundredFiftySixEX_9051852206305875919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 114270582252405377601457) ^ 57135291126202688800728 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 114270582252405377601457) ^ 38090194084135125867152 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 114270582252405377601457) ^ 434488905902682044112 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 114270582252405377601457) ^ 12624 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_229589818627293672856543 : Nat.Prime 229589818627293672856543 := by
  apply lucas_primality 229589818627293672856543 (3 : ZMod 229589818627293672856543)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (1279, 1), (767125153289140397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (1279, 1), (767125153289140397, 1)] : List FactorBlock).map factorBlockValue).prod) = 229589818627293672856543 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_13
      · exact prime_oneHundredFiftySixEX_1279
      · exact prime_oneHundredFiftySixEX_767125153289140397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 229589818627293672856543) ^ 114794909313646836428271 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 229589818627293672856543) ^ 76529939542431224285514 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 229589818627293672856543) ^ 17660755279022590219734 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 229589818627293672856543) ^ 179507285869658852898 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 229589818627293672856543) ^ 299286 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_770016716502825657637901 : Nat.Prime 770016716502825657637901 := by
  apply lucas_primality 770016716502825657637901 (2 : ZMod 770016716502825657637901)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (2663, 1), (15199, 1), (190245315638867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (2663, 1), (15199, 1), (190245315638867, 1)] : List FactorBlock).map factorBlockValue).prod) = 770016716502825657637901 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_5
      · exact prime_oneHundredFiftySixEX_2663
      · exact prime_oneHundredFiftySixEX_15199
      · exact prime_oneHundredFiftySixEX_190245315638867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 770016716502825657637901) ^ 385008358251412828818950 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 770016716502825657637901) ^ 154003343300565131527580 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 770016716502825657637901) ^ 289153855239513953300 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 770016716502825657637901) ^ 50662327554630282100 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 770016716502825657637901) ^ 4047493700 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_878899926231809511221431 : Nat.Prime 878899926231809511221431 := by
  apply lucas_primality 878899926231809511221431 (6 : ZMod 878899926231809511221431)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 1), (797, 1), (125287, 1), (13971226936099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 1), (797, 1), (125287, 1), (13971226936099, 1)] : List FactorBlock).map factorBlockValue).prod) = 878899926231809511221431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_5
      · exact prime_oneHundredFiftySixEX_7
      · exact prime_oneHundredFiftySixEX_797
      · exact prime_oneHundredFiftySixEX_125287
      · exact prime_oneHundredFiftySixEX_13971226936099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 878899926231809511221431) ^ 439449963115904755610715 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 878899926231809511221431) ^ 292966642077269837073810 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 878899926231809511221431) ^ 175779985246361902244286 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 878899926231809511221431) ^ 125557132318829930174490 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 878899926231809511221431) ^ 1102760258760112310190 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 878899926231809511221431) ^ 7015092756884668890 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 878899926231809511221431) ^ 62907855570 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_970131469449799584938207 : Nat.Prime 970131469449799584938207 := by
  apply lucas_primality 970131469449799584938207 (5 : ZMod 970131469449799584938207)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (2969, 1), (471139, 1), (49538551476619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (2969, 1), (471139, 1), (49538551476619, 1)] : List FactorBlock).map factorBlockValue).prod) = 970131469449799584938207 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_7
      · exact prime_oneHundredFiftySixEX_2969
      · exact prime_oneHundredFiftySixEX_471139
      · exact prime_oneHundredFiftySixEX_49538551476619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 970131469449799584938207) ^ 485065734724899792469103 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 970131469449799584938207) ^ 138590209921399940705458 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 970131469449799584938207) ^ 326753610457999186574 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 970131469449799584938207) ^ 2059119430677145354 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (5 : ZMod 970131469449799584938207) ^ 19583363674 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_1616562660356212627677907 : Nat.Prime 1616562660356212627677907 := by
  apply lucas_primality 1616562660356212627677907 (3 : ZMod 1616562660356212627677907)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 1), (71171, 1), (921517, 1), (65207015611, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 1), (71171, 1), (921517, 1), (65207015611, 1)] : List FactorBlock).map factorBlockValue).prod) = 1616562660356212627677907 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_7
      · exact prime_oneHundredFiftySixEX_71171
      · exact prime_oneHundredFiftySixEX_921517
      · exact prime_oneHundredFiftySixEX_65207015611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1616562660356212627677907) ^ 808281330178106313838953 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1616562660356212627677907) ^ 538854220118737542559302 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1616562660356212627677907) ^ 230937522908030375382558 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1616562660356212627677907) ^ 22713783147015113286 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1616562660356212627677907) ^ 1754240736043081818 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 1616562660356212627677907) ^ 24791238261846 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_3754450653856369568678699 : Nat.Prime 3754450653856369568678699 := by
  apply lucas_primality 3754450653856369568678699 (2 : ZMod 3754450653856369568678699)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (307, 1), (5503, 1), (101014991469007579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (307, 1), (5503, 1), (101014991469007579, 1)] : List FactorBlock).map factorBlockValue).prod) = 3754450653856369568678699 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_11
      · exact prime_oneHundredFiftySixEX_307
      · exact prime_oneHundredFiftySixEX_5503
      · exact prime_oneHundredFiftySixEX_101014991469007579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3754450653856369568678699) ^ 1877225326928184784339349 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 3754450653856369568678699) ^ 341313695805124506243518 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 3754450653856369568678699) ^ 12229480957186871559214 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 3754450653856369568678699) ^ 682255252381677188566 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 3754450653856369568678699) ^ 37167262 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_4073810746361855823377563 : Nat.Prime 4073810746361855823377563 := by
  apply lucas_primality 4073810746361855823377563 (2 : ZMod 4073810746361855823377563)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (97, 1), (151, 1), (233, 1), (198950482390006177, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (97, 1), (151, 1), (233, 1), (198950482390006177, 1)] : List FactorBlock).map factorBlockValue).prod) = 4073810746361855823377563 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_97
      · exact prime_oneHundredFiftySixEX_151
      · exact prime_oneHundredFiftySixEX_233
      · exact prime_oneHundredFiftySixEX_198950482390006177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4073810746361855823377563) ^ 2036905373180927911688781 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 4073810746361855823377563) ^ 1357936915453951941125854 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 4073810746361855823377563) ^ 41998048931565523952346 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 4073810746361855823377563) ^ 26978879114979177638262 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 4073810746361855823377563) ^ 17484166293398522847114 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 4073810746361855823377563) ^ 20476506 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_4236639650840518656921701 : Nat.Prime 4236639650840518656921701 := by
  apply lucas_primality 4236639650840518656921701 (2 : ZMod 4236639650840518656921701)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (42366396508405186569217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (42366396508405186569217, 1)] : List FactorBlock).map factorBlockValue).prod) = 4236639650840518656921701 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_5
      · exact prime_oneHundredFiftySixEX_42366396508405186569217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4236639650840518656921701) ^ 2118319825420259328460850 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 4236639650840518656921701) ^ 847327930168103731384340 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 4236639650840518656921701) ^ 100 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_4686051982317198503271823 : Nat.Prime 4686051982317198503271823 := by
  apply lucas_primality 4686051982317198503271823 (3 : ZMod 4686051982317198503271823)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (11, 1), (17707, 1), (120619, 1), (3693685767911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (11, 1), (17707, 1), (120619, 1), (3693685767911, 1)] : List FactorBlock).map factorBlockValue).prod) = 4686051982317198503271823 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_11
      · exact prime_oneHundredFiftySixEX_17707
      · exact prime_oneHundredFiftySixEX_120619
      · exact prime_oneHundredFiftySixEX_3693685767911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4686051982317198503271823) ^ 2343025991158599251635911 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 4686051982317198503271823) ^ 1562017327439066167757274 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 4686051982317198503271823) ^ 426004725665199863933802 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 4686051982317198503271823) ^ 264644038081956203946 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 4686051982317198503271823) ^ 38850031772085645738 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 4686051982317198503271823) ^ 1268665576002 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_5476058014252977989660701 : Nat.Prime 5476058014252977989660701 := by
  apply lucas_primality 5476058014252977989660701 (6 : ZMod 5476058014252977989660701)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 2), (220589, 1), (9194337137883169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 2), (220589, 1), (9194337137883169, 1)] : List FactorBlock).map factorBlockValue).prod) = 5476058014252977989660701 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_5
      · exact prime_oneHundredFiftySixEX_220589
      · exact prime_oneHundredFiftySixEX_9194337137883169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 5476058014252977989660701) ^ 2738029007126488994830350 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 5476058014252977989660701) ^ 1825352671417659329886900 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 5476058014252977989660701) ^ 1095211602850595597932140 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 5476058014252977989660701) ^ 24824710272284556300 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 5476058014252977989660701) ^ 595590300 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_9246647644642549819100191 : Nat.Prime 9246647644642549819100191 := by
  apply lucas_primality 9246647644642549819100191 (6 : ZMod 9246647644642549819100191)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (296773, 1), (942261469, 1), (1102217329, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (296773, 1), (942261469, 1), (1102217329, 1)] : List FactorBlock).map factorBlockValue).prod) = 9246647644642549819100191 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_5
      · exact prime_oneHundredFiftySixEX_296773
      · exact prime_oneHundredFiftySixEX_942261469
      · exact prime_oneHundredFiftySixEX_1102217329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 9246647644642549819100191) ^ 4623323822321274909550095 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 9246647644642549819100191) ^ 3082215881547516606366730 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 9246647644642549819100191) ^ 1849329528928509963820038 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 9246647644642549819100191) ^ 31157307587423889030 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 9246647644642549819100191) ^ 9813250301379510 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (6 : ZMod 9246647644642549819100191) ^ 8389132888186110 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_17291733913373363837593513 : Nat.Prime 17291733913373363837593513 := by
  apply lucas_primality 17291733913373363837593513 (10 : ZMod 17291733913373363837593513)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 1), (19, 1), (82284739, 1), (35449576648411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 1), (19, 1), (82284739, 1), (35449576648411, 1)] : List FactorBlock).map factorBlockValue).prod) = 17291733913373363837593513 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_13
      · exact prime_oneHundredFiftySixEX_19
      · exact prime_oneHundredFiftySixEX_82284739
      · exact prime_oneHundredFiftySixEX_35449576648411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 17291733913373363837593513) ^ 8645866956686681918796756 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (10 : ZMod 17291733913373363837593513) ^ 5763911304457787945864504 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (10 : ZMod 17291733913373363837593513) ^ 1330133377951797218276424 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (10 : ZMod 17291733913373363837593513) ^ 910091258598598096715448 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (10 : ZMod 17291733913373363837593513) ^ 210145090371780408 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (10 : ZMod 17291733913373363837593513) ^ 487783932792 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_23039804362278613203219539 : Nat.Prime 23039804362278613203219539 := by
  apply lucas_primality 23039804362278613203219539 (2 : ZMod 23039804362278613203219539)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (307, 1), (1974953228379788548193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (307, 1), (1974953228379788548193, 1)] : List FactorBlock).map factorBlockValue).prod) = 23039804362278613203219539 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_19
      · exact prime_oneHundredFiftySixEX_307
      · exact prime_oneHundredFiftySixEX_1974953228379788548193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 23039804362278613203219539) ^ 11519902181139306601609769 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 23039804362278613203219539) ^ 1212621282225190168590502 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 23039804362278613203219539) ^ 75048222678431964831334 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 23039804362278613203219539) ^ 11666 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_27568555144998549879188701 : Nat.Prime 27568555144998549879188701 := by
  apply lucas_primality 27568555144998549879188701 (2 : ZMod 27568555144998549879188701)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 2), (346417, 1), (88424436268679879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 2), (346417, 1), (88424436268679879, 1)] : List FactorBlock).map factorBlockValue).prod) = 27568555144998549879188701 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_5
      · exact prime_oneHundredFiftySixEX_346417
      · exact prime_oneHundredFiftySixEX_88424436268679879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 27568555144998549879188701) ^ 13784277572499274939594350 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 27568555144998549879188701) ^ 9189518381666183293062900 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 27568555144998549879188701) ^ 5513711028999709975837740 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 27568555144998549879188701) ^ 79581992641811891100 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 27568555144998549879188701) ^ 311775300 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_403574691291116627334294113 : Nat.Prime 403574691291116627334294113 := by
  apply lucas_primality 403574691291116627334294113 (3 : ZMod 403574691291116627334294113)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (13, 1), (970131469449799584938207, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (13, 1), (970131469449799584938207, 1)] : List FactorBlock).map factorBlockValue).prod) = 403574691291116627334294113 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_13
      · exact prime_oneHundredFiftySixEX_970131469449799584938207
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 403574691291116627334294113) ^ 201787345645558313667147056 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 403574691291116627334294113) ^ 31044207022393586718022624 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (3 : ZMod 403574691291116627334294113) ^ 416 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_468105669847818016984193933 : Nat.Prime 468105669847818016984193933 := by
  apply lucas_primality 468105669847818016984193933 (2 : ZMod 468105669847818016984193933)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (37, 1), (2309, 1), (2535473, 1), (540255582298987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (37, 1), (2309, 1), (2535473, 1), (540255582298987, 1)] : List FactorBlock).map factorBlockValue).prod) = 468105669847818016984193933 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_37
      · exact prime_oneHundredFiftySixEX_2309
      · exact prime_oneHundredFiftySixEX_2535473
      · exact prime_oneHundredFiftySixEX_540255582298987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 468105669847818016984193933) ^ 234052834923909008492096966 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 468105669847818016984193933) ^ 12651504590481568026599836 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 468105669847818016984193933) ^ 202730909418717200945948 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 468105669847818016984193933) ^ 184622620650197425484 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 468105669847818016984193933) ^ 866452259236 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_703945167633741598060200037 : Nat.Prime 703945167633741598060200037 := by
  apply lucas_primality 703945167633741598060200037 (2 : ZMod 703945167633741598060200037)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (2617, 1), (22415780398476041206859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (2617, 1), (22415780398476041206859, 1)] : List FactorBlock).map factorBlockValue).prod) = 703945167633741598060200037 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_2617
      · exact prime_oneHundredFiftySixEX_22415780398476041206859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 703945167633741598060200037) ^ 351972583816870799030100018 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 703945167633741598060200037) ^ 234648389211247199353400012 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 703945167633741598060200037) ^ 268989364781712494482308 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 703945167633741598060200037) ^ 31404 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_6359780480001389610061117573 : Nat.Prime 6359780480001389610061117573 := by
  apply lucas_primality 6359780480001389610061117573 (2 : ZMod 6359780480001389610061117573)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 5), (127, 1), (357817, 1), (143982983799976589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 5), (127, 1), (357817, 1), (143982983799976589, 1)] : List FactorBlock).map factorBlockValue).prod) = 6359780480001389610061117573 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_127
      · exact prime_oneHundredFiftySixEX_357817
      · exact prime_oneHundredFiftySixEX_143982983799976589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6359780480001389610061117573) ^ 3179890240000694805030558786 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 6359780480001389610061117573) ^ 2119926826667129870020372524 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 6359780480001389610061117573) ^ 50077011653554248898119036 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 6359780480001389610061117573) ^ 17773835452204310052516 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 6359780480001389610061117573) ^ 44170361748 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_184433633920040298691772409637 : Nat.Prime 184433633920040298691772409637 := by
  apply lucas_primality 184433633920040298691772409637 (2 : ZMod 184433633920040298691772409637)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (47, 1), (160183, 1), (7631857, 1), (267494201311979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (47, 1), (160183, 1), (7631857, 1), (267494201311979, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409637 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_3
      · exact prime_oneHundredFiftySixEX_47
      · exact prime_oneHundredFiftySixEX_160183
      · exact prime_oneHundredFiftySixEX_7631857
      · exact prime_oneHundredFiftySixEX_267494201311979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 184433633920040298691772409637) ^ 92216816960020149345886204818 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 184433633920040298691772409637) ^ 61477877973346766230590803212 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 184433633920040298691772409637) ^ 3924119870639155291314306588 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 184433633920040298691772409637) ^ 1151393305906621168861692 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 184433633920040298691772409637) ^ 24166285337898796936548 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 184433633920040298691772409637) ^ 689486474904684 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_184433633920040298691772409659 : Nat.Prime 184433633920040298691772409659 := by
  apply lucas_primality 184433633920040298691772409659 (2 : ZMod 184433633920040298691772409659)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5333, 1), (17291733913373363837593513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5333, 1), (17291733913373363837593513, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409659 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_5333
      · exact prime_oneHundredFiftySixEX_17291733913373363837593513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 184433633920040298691772409659) ^ 92216816960020149345886204829 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 184433633920040298691772409659) ^ 34583467826746727675187026 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 184433633920040298691772409659) ^ 10666 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftySixEX_184433633920040298691772409701 : Nat.Prime 184433633920040298691772409701 := by
  apply lucas_primality 184433633920040298691772409701 (2 : ZMod 184433633920040298691772409701)
  · rw [← oneHundredFiftySixEXFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (11, 1), (701, 1), (374317, 1), (638983830804654331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (11, 1), (701, 1), (374317, 1), (638983830804654331, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409701 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftySixEX_2
      · exact prime_oneHundredFiftySixEX_5
      · exact prime_oneHundredFiftySixEX_11
      · exact prime_oneHundredFiftySixEX_701
      · exact prime_oneHundredFiftySixEX_374317
      · exact prime_oneHundredFiftySixEX_638983830804654331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 184433633920040298691772409701) ^ 92216816960020149345886204850 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 184433633920040298691772409701) ^ 36886726784008059738354481940 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 184433633920040298691772409701) ^ 16766693992730936244706582700 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 184433633920040298691772409701) ^ 263100761654836374738619700 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 184433633920040298691772409701) ^ 492720431933468954634100 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide
    · change (2 : ZMod 184433633920040298691772409701) ^ 288635838700 ≠ 1
      rw [← oneHundredFiftySixEXFastPow_eq_pow]
      decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409600 : Nat.totient 184433633920040298691772409600 = 45398783408065799221592064000 := by
  rw [← show ((([(2, 8), (3, 1), (5, 2), (13, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409600 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_2, prime_oneHundredFiftySixEX_3, prime_oneHundredFiftySixEX_5, prime_oneHundredFiftySixEX_13, prime_oneHundredFiftySixEX_171401, prime_oneHundredFiftySixEX_714027719, prime_oneHundredFiftySixEX_6037638679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409601 : Nat.totient 184433633920040298691772409601 = 167666307844417692320774412000 := by
  rw [← show ((([(11, 2), (265261, 1), (5746208106092056929421, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409601 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_11, prime_oneHundredFiftySixEX_265261, prime_oneHundredFiftySixEX_5746208106092056929421]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409602 : Nat.totient 184433633920040298691772409602 = 91748711290172331328902010672 := by
  rw [← show ((([(2, 1), (197, 1), (468105669847818016984193933, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409602 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_2, prime_oneHundredFiftySixEX_197, prime_oneHundredFiftySixEX_468105669847818016984193933]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409603 : Nat.totient 184433633920040298691772409603 = 122955739565693079480011607744 := by
  rw [← show ((([(3, 1), (8532299, 1), (62402203, 1), (115465670140633, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409603 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_3, prime_oneHundredFiftySixEX_8532299, prime_oneHundredFiftySixEX_62402203, prime_oneHundredFiftySixEX_115465670140633]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409604 : Nat.totient 184433633920040298691772409604 = 91814066674002363255652253664 := by
  rw [← show ((([(2, 2), (229, 1), (1617523, 1), (124478453735397502303, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409604 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_2, prime_oneHundredFiftySixEX_229, prime_oneHundredFiftySixEX_1617523, prime_oneHundredFiftySixEX_124478453735397502303]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409605 : Nat.totient 184433633920040298691772409605 = 123329778223937792197682933760 := by
  rw [← show ((([(5, 1), (7, 1), (41, 2), (2297, 1), (188459, 1), (4906547, 1), (1475878223, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409605 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_5, prime_oneHundredFiftySixEX_7, prime_oneHundredFiftySixEX_41, prime_oneHundredFiftySixEX_2297, prime_oneHundredFiftySixEX_188459, prime_oneHundredFiftySixEX_4906547, prime_oneHundredFiftySixEX_1475878223]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409606 : Nat.totient 184433633920040298691772409606 = 57636161252176004770974793728 := by
  rw [← show ((([(2, 1), (3, 2), (17, 1), (257, 1), (251897, 1), (9310276483619584019, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409606 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_2, prime_oneHundredFiftySixEX_3, prime_oneHundredFiftySixEX_17, prime_oneHundredFiftySixEX_257, prime_oneHundredFiftySixEX_251897, prime_oneHundredFiftySixEX_9310276483619584019]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409607 : Nat.totient 184433633920040298691772409607 = 184431693970915002922735824000 := by
  rw [← show ((([(114001, 1), (572549, 1), (2825652830745808043, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409607 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_114001, prime_oneHundredFiftySixEX_572549, prime_oneHundredFiftySixEX_2825652830745808043]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409608 : Nat.totient 184433633920040298691772409608 = 92177970798293669027965936512 := by
  rw [← show ((([(2, 3), (2399, 1), (226777, 1), (42376090025613958487, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409608 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_2, prime_oneHundredFiftySixEX_2399, prime_oneHundredFiftySixEX_226777, prime_oneHundredFiftySixEX_42376090025613958487]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409609 : Nat.totient 184433633920040298691772409609 = 120620976239504396953014681600 := by
  rw [← show ((([(3, 1), (61, 1), (379, 1), (15425269, 1), (284376793, 1), (606209761, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409609 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_3, prime_oneHundredFiftySixEX_61, prime_oneHundredFiftySixEX_379, prime_oneHundredFiftySixEX_15425269, prime_oneHundredFiftySixEX_284376793, prime_oneHundredFiftySixEX_606209761]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409610 : Nat.totient 184433633920040298691772409610 = 73772333474128274905325894400 := by
  rw [← show ((([(2, 1), (5, 1), (66239, 1), (11622449, 1), (23956794459495151, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409610 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_2, prime_oneHundredFiftySixEX_5, prime_oneHundredFiftySixEX_66239, prime_oneHundredFiftySixEX_11622449, prime_oneHundredFiftySixEX_23956794459495151]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409611 : Nat.totient 184433633920040298691772409611 = 184012058189791270631344688640 := by
  rw [← show ((([(443, 1), (71473, 1), (77933, 1), (591391, 1), (126385799483, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409611 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_443, prime_oneHundredFiftySixEX_71473, prime_oneHundredFiftySixEX_77933, prime_oneHundredFiftySixEX_591391, prime_oneHundredFiftySixEX_126385799483]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409612 : Nat.totient 184433633920040298691772409612 = 47748807158513766903664035840 := by
  rw [← show ((([(2, 2), (3, 1), (7, 1), (11, 1), (317, 1), (9719, 1), (6998309863, 1), (9257508937, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409612 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_2, prime_oneHundredFiftySixEX_3, prime_oneHundredFiftySixEX_7, prime_oneHundredFiftySixEX_11, prime_oneHundredFiftySixEX_317, prime_oneHundredFiftySixEX_9719, prime_oneHundredFiftySixEX_6998309863, prime_oneHundredFiftySixEX_9257508937]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409613 : Nat.totient 184433633920040298691772409613 = 155773010830546118621268457920 := by
  rw [← show ((([(13, 1), (19, 1), (31, 1), (503, 1), (47886543588161587791203, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409613 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_13, prime_oneHundredFiftySixEX_19, prime_oneHundredFiftySixEX_31, prime_oneHundredFiftySixEX_503, prime_oneHundredFiftySixEX_47886543588161587791203]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409614 : Nat.totient 184433633920040298691772409614 = 91050524250600512608912685952 := by
  rw [← show ((([(2, 1), (103, 1), (337, 1), (880051639, 1), (3018803507790583, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409614 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_2, prime_oneHundredFiftySixEX_103, prime_oneHundredFiftySixEX_337, prime_oneHundredFiftySixEX_880051639, prime_oneHundredFiftySixEX_3018803507790583]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409615 : Nat.totient 184433633920040298691772409615 = 91541766969988510535684273664 := by
  rw [← show ((([(3, 3), (5, 1), (23, 1), (37, 1), (28607, 1), (56118296425536623357, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409615 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_3, prime_oneHundredFiftySixEX_5, prime_oneHundredFiftySixEX_23, prime_oneHundredFiftySixEX_37, prime_oneHundredFiftySixEX_28607, prime_oneHundredFiftySixEX_56118296425536623357]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409616 : Nat.totient 184433633920040298691772409616 = 91301308593018878480681318400 := by
  rw [← show ((([(2, 4), (101, 1), (50287, 1), (139409, 1), (16279918539612547, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409616 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_2, prime_oneHundredFiftySixEX_101, prime_oneHundredFiftySixEX_50287, prime_oneHundredFiftySixEX_139409, prime_oneHundredFiftySixEX_16279918539612547]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409617 : Nat.totient 184433633920040298691772409617 = 178073853440038909081711292016 := by
  rw [← show ((([(29, 1), (6359780480001389610061117573, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409617 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_29, prime_oneHundredFiftySixEX_6359780480001389610061117573]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409618 : Nat.totient 184433633920040298691772409618 = 61472865932407640599857561600 := by
  rw [← show ((([(2, 1), (3, 1), (14051, 1), (172313, 1), (237467, 1), (3638827, 1), (14692609, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409618 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_2, prime_oneHundredFiftySixEX_3, prime_oneHundredFiftySixEX_14051, prime_oneHundredFiftySixEX_172313, prime_oneHundredFiftySixEX_237467, prime_oneHundredFiftySixEX_3638827, prime_oneHundredFiftySixEX_14692609]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409619 : Nat.totient 184433633920040298691772409619 = 158081351831164096210430318400 := by
  rw [← show ((([(7, 1), (34217, 1), (770016716502825657637901, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409619 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_7, prime_oneHundredFiftySixEX_34217, prime_oneHundredFiftySixEX_770016716502825657637901]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409620 : Nat.totient 184433633920040298691772409620 = 73769329132746767142208413696 := by
  rw [← show ((([(2, 2), (5, 1), (17903, 1), (19916623, 1), (25862387424264449, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409620 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_2, prime_oneHundredFiftySixEX_5, prime_oneHundredFiftySixEX_17903, prime_oneHundredFiftySixEX_19916623, prime_oneHundredFiftySixEX_25862387424264449]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409621 : Nat.totient 184433633920040298691772409621 = 122867611605991029068616586944 := by
  rw [← show ((([(3, 1), (1427, 1), (62039, 1), (21200988013, 1), (32754728663, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409621 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_3, prime_oneHundredFiftySixEX_1427, prime_oneHundredFiftySixEX_62039, prime_oneHundredFiftySixEX_21200988013, prime_oneHundredFiftySixEX_32754728663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409622 : Nat.totient 184433633920040298691772409622 = 90467579645480686864447999008 := by
  rw [← show ((([(2, 1), (59, 1), (487, 1), (973373, 1), (3297234682738046579, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409622 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_2, prime_oneHundredFiftySixEX_59, prime_oneHundredFiftySixEX_487, prime_oneHundredFiftySixEX_973373, prime_oneHundredFiftySixEX_3297234682738046579]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409623 : Nat.totient 184433633920040298691772409623 = 157801321922332901887872000000 := by
  rw [← show ((([(11, 1), (17, 1), (96601, 1), (129001, 1), (79145060909254229, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409623 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_11, prime_oneHundredFiftySixEX_17, prime_oneHundredFiftySixEX_96601, prime_oneHundredFiftySixEX_129001, prime_oneHundredFiftySixEX_79145060909254229]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409624 : Nat.totient 184433633920040298691772409624 = 61035590494854777143133512640 := by
  rw [← show ((([(2, 3), (3, 2), (139, 1), (104050223, 1), (177112743868002511, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409624 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_2, prime_oneHundredFiftySixEX_3, prime_oneHundredFiftySixEX_139, prime_oneHundredFiftySixEX_104050223, prime_oneHundredFiftySixEX_177112743868002511]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409625 : Nat.totient 184433633920040298691772409625 = 147546907136022586054008831600 := by
  rw [← show ((([(5, 3), (19041345201559, 1), (77487648889403, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409625 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_5, prime_oneHundredFiftySixEX_19041345201559, prime_oneHundredFiftySixEX_77487648889403]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409626 : Nat.totient 184433633920040298691772409626 = 72899475481371208098750289920 := by
  rw [← show ((([(2, 1), (7, 1), (13, 1), (1153, 1), (878899926231809511221431, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409626 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_2, prime_oneHundredFiftySixEX_7, prime_oneHundredFiftySixEX_13, prime_oneHundredFiftySixEX_1153, prime_oneHundredFiftySixEX_878899926231809511221431]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409627 : Nat.totient 184433633920040298691772409627 = 122878082486196327369468940320 := by
  rw [← show ((([(3, 1), (1583, 1), (146030803, 1), (265946010870138941, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409627 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_3, prime_oneHundredFiftySixEX_1583, prime_oneHundredFiftySixEX_146030803, prime_oneHundredFiftySixEX_265946010870138941]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409628 : Nat.totient 184433633920040298691772409628 = 90481886988344837872330752000 := by
  rw [← show ((([(2, 2), (97, 2), (233, 1), (239, 1), (7351, 1), (35410211, 1), (338070989, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409628 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_2, prime_oneHundredFiftySixEX_97, prime_oneHundredFiftySixEX_233, prime_oneHundredFiftySixEX_239, prime_oneHundredFiftySixEX_7351, prime_oneHundredFiftySixEX_35410211, prime_oneHundredFiftySixEX_338070989]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409629 : Nat.totient 184433633920040298691772409629 = 183746902607529514306509240000 := by
  rw [← show ((([(269, 1), (171251, 1), (5843287, 1), (685168690790093, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409629 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_269, prime_oneHundredFiftySixEX_171251, prime_oneHundredFiftySixEX_5843287, prime_oneHundredFiftySixEX_685168690790093]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409630 : Nat.totient 184433633920040298691772409630 = 49169369877394563283451188896 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (3803, 1), (1616562660356212627677907, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409630 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_2, prime_oneHundredFiftySixEX_3, prime_oneHundredFiftySixEX_5, prime_oneHundredFiftySixEX_3803, prime_oneHundredFiftySixEX_1616562660356212627677907]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409631 : Nat.totient 184433633920040298691772409631 = 180096204328570498051818693504 := by
  rw [← show ((([(53, 1), (277, 1), (883, 1), (1871339, 1), (7602760547159623, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409631 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_53, prime_oneHundredFiftySixEX_277, prime_oneHundredFiftySixEX_883, prime_oneHundredFiftySixEX_1871339, prime_oneHundredFiftySixEX_7602760547159623]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409632 : Nat.totient 184433633920040298691772409632 = 87363300277398514919738895360 := by
  rw [← show ((([(2, 5), (19, 1), (169551237041, 1), (1789103977804019, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409632 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_2, prime_oneHundredFiftySixEX_19, prime_oneHundredFiftySixEX_169551237041, prime_oneHundredFiftySixEX_1789103977804019]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409633 : Nat.totient 184433633920040298691772409633 = 105238128926878483437935028000 := by
  rw [← show ((([(3, 2), (7, 1), (691, 1), (4236639650840518656921701, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409633 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_3, prime_oneHundredFiftySixEX_7, prime_oneHundredFiftySixEX_691, prime_oneHundredFiftySixEX_4236639650840518656921701]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409634 : Nat.totient 184433633920040298691772409634 = 83786609443831509238500177360 := by
  rw [← show ((([(2, 1), (11, 1), (1789, 1), (4686051982317198503271823, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409634 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_2, prime_oneHundredFiftySixEX_11, prime_oneHundredFiftySixEX_1789, prime_oneHundredFiftySixEX_4686051982317198503271823]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409635 : Nat.totient 184433633920040298691772409635 = 146987405704482416966346854400 := by
  rw [← show ((([(5, 1), (281, 1), (4271, 1), (773052649, 1), (39758057268073, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409635 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_5, prime_oneHundredFiftySixEX_281, prime_oneHundredFiftySixEX_4271, prime_oneHundredFiftySixEX_773052649, prime_oneHundredFiftySixEX_39758057268073]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409636 : Nat.totient 184433633920040298691772409636 = 60169454500621025853093993984 := by
  rw [← show ((([(2, 2), (3, 1), (47, 1), (160183, 1), (7631857, 1), (267494201311979, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409636 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_2, prime_oneHundredFiftySixEX_3, prime_oneHundredFiftySixEX_47, prime_oneHundredFiftySixEX_160183, prime_oneHundredFiftySixEX_7631857, prime_oneHundredFiftySixEX_267494201311979]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409637 : Nat.totient 184433633920040298691772409637 = 184433633920040298691772409636 := by
  rw [← show ((([(184433633920040298691772409637, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409637 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_184433633920040298691772409637]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409638 : Nat.totient 184433633920040298691772409638 = 88207332579774952575709708800 := by
  rw [← show ((([(2, 1), (23, 1), (3703267, 1), (3813401, 1), (14341337, 1), (19796807, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409638 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_2, prime_oneHundredFiftySixEX_23, prime_oneHundredFiftySixEX_3703267, prime_oneHundredFiftySixEX_3813401, prime_oneHundredFiftySixEX_14341337, prime_oneHundredFiftySixEX_19796807]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409639 : Nat.totient 184433633920040298691772409639 = 113482609899660887919182472960 := by
  rw [← show ((([(3, 1), (13, 1), (7561, 1), (2416168199, 1), (258862483991359, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409639 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_3, prime_oneHundredFiftySixEX_13, prime_oneHundredFiftySixEX_7561, prime_oneHundredFiftySixEX_2416168199, prime_oneHundredFiftySixEX_258862483991359]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409640 : Nat.totient 184433633920040298691772409640 = 58070900561453651142770688000 := by
  rw [← show ((([(2, 3), (5, 1), (7, 1), (17, 1), (43, 1), (1439, 1), (3001, 1), (38398499, 1), (5434050593, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409640 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_2, prime_oneHundredFiftySixEX_5, prime_oneHundredFiftySixEX_7, prime_oneHundredFiftySixEX_17, prime_oneHundredFiftySixEX_43, prime_oneHundredFiftySixEX_1439, prime_oneHundredFiftySixEX_3001, prime_oneHundredFiftySixEX_38398499, prime_oneHundredFiftySixEX_5434050593]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409641 : Nat.totient 184433633920040298691772409641 = 184030059228749182064438115072 := by
  rw [← show ((([(457, 1), (403574691291116627334294113, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409641 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_457, prime_oneHundredFiftySixEX_403574691291116627334294113]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409642 : Nat.totient 184433633920040298691772409642 = 61473401264985303981504862080 := by
  rw [← show ((([(2, 1), (3, 3), (14107, 1), (517721, 1), (467644591344983909, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409642 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_2, prime_oneHundredFiftySixEX_3, prime_oneHundredFiftySixEX_14107, prime_oneHundredFiftySixEX_517721, prime_oneHundredFiftySixEX_467644591344983909]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409643 : Nat.totient 184433633920040298691772409643 = 181680859126466820716905226016 := by
  rw [← show ((([(67, 1), (5345317, 1), (514981769046947239237, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409643 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_67, prime_oneHundredFiftySixEX_5345317, prime_oneHundredFiftySixEX_514981769046947239237]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409644 : Nat.totient 184433633920040298691772409644 = 89173485908598720434184600000 := by
  rw [← show ((([(2, 2), (31, 1), (1301, 1), (2851881371, 1), (400875657510611, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409644 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_2, prime_oneHundredFiftySixEX_31, prime_oneHundredFiftySixEX_1301, prime_oneHundredFiftySixEX_2851881371, prime_oneHundredFiftySixEX_400875657510611]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409645 : Nat.totient 184433633920040298691772409645 = 88298640745297495733980953600 := by
  rw [← show ((([(3, 1), (5, 1), (11, 1), (83, 1), (2357, 1), (9967, 1), (12040139, 1), (47612670971, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409645 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_3, prime_oneHundredFiftySixEX_5, prime_oneHundredFiftySixEX_11, prime_oneHundredFiftySixEX_83, prime_oneHundredFiftySixEX_2357, prime_oneHundredFiftySixEX_9967, prime_oneHundredFiftySixEX_12040139, prime_oneHundredFiftySixEX_47612670971]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409646 : Nat.totient 184433633920040298691772409646 = 86865294351840299037879494400 := by
  rw [← show ((([(2, 1), (29, 1), (41, 1), (9489036071, 1), (8173464402104317, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409646 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_2, prime_oneHundredFiftySixEX_29, prime_oneHundredFiftySixEX_41, prime_oneHundredFiftySixEX_9489036071, prime_oneHundredFiftySixEX_8173464402104317]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409647 : Nat.totient 184433633920040298691772409647 = 156608532940988649111408461952 := by
  rw [← show ((([(7, 2), (107, 1), (340992992917, 1), (103160826000937, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409647 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_7, prime_oneHundredFiftySixEX_107, prime_oneHundredFiftySixEX_340992992917, prime_oneHundredFiftySixEX_103160826000937]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409648 : Nat.totient 184433633920040298691772409648 = 61477877973344387747660439552 := by
  rw [← show ((([(2, 4), (3, 1), (33312673606897, 1), (115342509540833, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409648 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_2, prime_oneHundredFiftySixEX_3, prime_oneHundredFiftySixEX_33312673606897, prime_oneHundredFiftySixEX_115342509540833]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409649 : Nat.totient 184433633920040298691772409649 = 181967322314518773407198284032 := by
  rw [← show ((([(79, 1), (1997, 1), (4603, 1), (187843, 1), (18100919, 1), (74696173, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409649 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_79, prime_oneHundredFiftySixEX_1997, prime_oneHundredFiftySixEX_4603, prime_oneHundredFiftySixEX_187843, prime_oneHundredFiftySixEX_18100919, prime_oneHundredFiftySixEX_74696173]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409650 : Nat.totient 184433633920040298691772409650 = 73346972985610224796494074880 := by
  rw [← show ((([(2, 1), (5, 2), (173, 1), (1650673, 1), (12917038922669744117, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409650 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_2, prime_oneHundredFiftySixEX_5, prime_oneHundredFiftySixEX_173, prime_oneHundredFiftySixEX_1650673, prime_oneHundredFiftySixEX_12917038922669744117]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409651 : Nat.totient 184433633920040298691772409651 = 116334232405341251676177824640 := by
  rw [← show ((([(3, 2), (19, 1), (919, 1), (4969, 1), (236188911554202791671, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409651 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_3, prime_oneHundredFiftySixEX_19, prime_oneHundredFiftySixEX_919, prime_oneHundredFiftySixEX_4969, prime_oneHundredFiftySixEX_236188911554202791671]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409652 : Nat.totient 184433633920040298691772409652 = 82819931676784100601026153472 := by
  rw [← show ((([(2, 2), (13, 1), (37, 1), (31177, 1), (3074685732733041494149, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409652 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_2, prime_oneHundredFiftySixEX_13, prime_oneHundredFiftySixEX_37, prime_oneHundredFiftySixEX_31177, prime_oneHundredFiftySixEX_3074685732733041494149]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409653 : Nat.totient 184433633920040298691772409653 = 183403278422802742767616438128 := by
  rw [← show ((([(179, 1), (384101989309, 1), (2682504973779523, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409653 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_179, prime_oneHundredFiftySixEX_384101989309, prime_oneHundredFiftySixEX_2682504973779523]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409654 : Nat.totient 184433633920040298691772409654 = 52384654940601522564201888000 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (191, 1), (1831, 1), (8521, 1), (1473596414167950607, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409654 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_2, prime_oneHundredFiftySixEX_3, prime_oneHundredFiftySixEX_7, prime_oneHundredFiftySixEX_191, prime_oneHundredFiftySixEX_1831, prime_oneHundredFiftySixEX_8521, prime_oneHundredFiftySixEX_1473596414167950607]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409655 : Nat.totient 184433633920040298691772409655 = 147057327625231798842583559040 := by
  rw [← show ((([(5, 1), (587, 1), (619, 1), (555671, 1), (182693727494674037, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409655 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_5, prime_oneHundredFiftySixEX_587, prime_oneHundredFiftySixEX_619, prime_oneHundredFiftySixEX_555671, prime_oneHundredFiftySixEX_182693727494674037]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409656 : Nat.totient 184433633920040298691772409656 = 83828899140364585008428121600 := by
  rw [← show ((([(2, 3), (11, 1), (18341, 1), (114270582252405377601457, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409656 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_2, prime_oneHundredFiftySixEX_11, prime_oneHundredFiftySixEX_18341, prime_oneHundredFiftySixEX_114270582252405377601457]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409657 : Nat.totient 184433633920040298691772409657 = 115450010629832750209481834496 := by
  rw [← show ((([(3, 1), (17, 1), (769, 1), (1097, 1), (6709, 1), (25356953, 1), (25198931287, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409657 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_3, prime_oneHundredFiftySixEX_17, prime_oneHundredFiftySixEX_769, prime_oneHundredFiftySixEX_1097, prime_oneHundredFiftySixEX_6709, prime_oneHundredFiftySixEX_25356953, prime_oneHundredFiftySixEX_25198931287]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409658 : Nat.totient 184433633920040298691772409658 = 92199525226106775982048605984 := by
  rw [← show ((([(2, 1), (5333, 1), (17291733913373363837593513, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409658 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_2, prime_oneHundredFiftySixEX_5333, prime_oneHundredFiftySixEX_17291733913373363837593513]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409659 : Nat.totient 184433633920040298691772409659 = 184433633920040298691772409658 := by
  rw [← show ((([(184433633920040298691772409659, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409659 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_184433633920040298691772409659]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409660 : Nat.totient 184433633920040298691772409660 = 49182302238155293563830539008 := by
  rw [← show ((([(2, 2), (3, 2), (5, 1), (349996873, 1), (2927544154246713619, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409660 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_2, prime_oneHundredFiftySixEX_3, prime_oneHundredFiftySixEX_5, prime_oneHundredFiftySixEX_349996873, prime_oneHundredFiftySixEX_2927544154246713619]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409661 : Nat.totient 184433633920040298691772409661 = 151182433676377419506576179200 := by
  rw [← show ((([(7, 1), (23, 1), (5009, 1), (3378589, 1), (74913961, 1), (903576841, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409661 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_7, prime_oneHundredFiftySixEX_23, prime_oneHundredFiftySixEX_5009, prime_oneHundredFiftySixEX_3378589, prime_oneHundredFiftySixEX_74913961, prime_oneHundredFiftySixEX_903576841]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409662 : Nat.totient 184433633920040298691772409662 = 92216816959669822550193210472 := by
  rw [← show ((([(2, 1), (263231038517, 1), (350326532461955843, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409662 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_2, prime_oneHundredFiftySixEX_263231038517, prime_oneHundredFiftySixEX_350326532461955843]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409663 : Nat.totient 184433633920040298691772409663 = 122675636485984415909705159040 := by
  rw [← show ((([(3, 1), (439, 1), (3227281, 1), (43392789259089243619, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409663 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_3, prime_oneHundredFiftySixEX_439, prime_oneHundredFiftySixEX_3227281, prime_oneHundredFiftySixEX_43392789259089243619]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409664 : Nat.totient 184433633920040298691772409664 = 91180672945888408772381859840 := by
  rw [← show ((([(2, 6), (89, 1), (27259443481, 1), (1187826903350189, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409664 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_2, prime_oneHundredFiftySixEX_89, prime_oneHundredFiftySixEX_27259443481, prime_oneHundredFiftySixEX_1187826903350189]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409665 : Nat.totient 184433633920040298691772409665 = 136197144409672127436333290496 := by
  rw [← show ((([(5, 1), (13, 1), (213150073, 1), (13311937837557174217, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409665 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_5, prime_oneHundredFiftySixEX_13, prime_oneHundredFiftySixEX_213150073, prime_oneHundredFiftySixEX_13311937837557174217]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409666 : Nat.totient 184433633920040298691772409666 = 60608584965191211365874444288 := by
  rw [← show ((([(2, 1), (3, 1), (73, 1), (2293, 1), (88423, 1), (59899309, 1), (34671681157, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409666 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_2, prime_oneHundredFiftySixEX_3, prime_oneHundredFiftySixEX_73, prime_oneHundredFiftySixEX_2293, prime_oneHundredFiftySixEX_88423, prime_oneHundredFiftySixEX_59899309, prime_oneHundredFiftySixEX_34671681157]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409667 : Nat.totient 184433633920040298691772409667 = 167666538208324173741652571200 := by
  rw [← show ((([(11, 1), (446921, 1), (6313019, 1), (5942642162310803, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409667 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_11, prime_oneHundredFiftySixEX_446921, prime_oneHundredFiftySixEX_6313019, prime_oneHundredFiftySixEX_5942642162310803]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409668 : Nat.totient 184433633920040298691772409668 = 78186424209721260734467584000 := by
  rw [← show ((([(2, 2), (7, 1), (149, 1), (241, 1), (266009, 1), (689576496218686451, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409668 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_2, prime_oneHundredFiftySixEX_7, prime_oneHundredFiftySixEX_149, prime_oneHundredFiftySixEX_241, prime_oneHundredFiftySixEX_266009, prime_oneHundredFiftySixEX_689576496218686451]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409669 : Nat.totient 184433633920040298691772409669 = 122955753870554517950334260544 := by
  rw [← show ((([(3, 4), (59223277, 1), (38447018787178690537, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409669 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_3, prime_oneHundredFiftySixEX_59223277, prime_oneHundredFiftySixEX_38447018787178690537]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409670 : Nat.totient 184433633920040298691772409670 = 67760909463330594239700787200 := by
  rw [← show ((([(2, 1), (5, 1), (19, 1), (61, 1), (71, 1), (4423, 1), (160969, 1), (314803210756169, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409670 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_2, prime_oneHundredFiftySixEX_5, prime_oneHundredFiftySixEX_19, prime_oneHundredFiftySixEX_61, prime_oneHundredFiftySixEX_71, prime_oneHundredFiftySixEX_4423, prime_oneHundredFiftySixEX_160969, prime_oneHundredFiftySixEX_314803210756169]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409671 : Nat.totient 184433633920040298691772409671 = 183447089422906232881721321376 := by
  rw [← show ((([(359, 1), (389, 1), (24859917239, 1), (53124688297339, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409671 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_359, prime_oneHundredFiftySixEX_389, prime_oneHundredFiftySixEX_24859917239, prime_oneHundredFiftySixEX_53124688297339]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409672 : Nat.totient 184433633920040298691772409672 = 61277616918457031252478042432 := by
  rw [← show ((([(2, 3), (3, 1), (307, 1), (8302403, 1), (3014995691311940443, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409672 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_2, prime_oneHundredFiftySixEX_3, prime_oneHundredFiftySixEX_307, prime_oneHundredFiftySixEX_8302403, prime_oneHundredFiftySixEX_3014995691311940443]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409673 : Nat.totient 184433633920040298691772409673 = 184433536832281958884311017668 := by
  rw [← show ((([(1899659, 1), (97087758339807459492347, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409673 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_1899659, prime_oneHundredFiftySixEX_97087758339807459492347]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409674 : Nat.totient 184433633920040298691772409674 = 86788624878215045038538580672 := by
  rw [← show ((([(2, 1), (17, 1), (23627, 1), (229589818627293672856543, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409674 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_2, prime_oneHundredFiftySixEX_17, prime_oneHundredFiftySixEX_23627, prime_oneHundredFiftySixEX_229589818627293672856543]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409675 : Nat.totient 184433633920040298691772409675 = 78779202326791213801881600000 := by
  rw [← show ((([(3, 1), (5, 2), (7, 1), (29, 2), (31, 1), (10071353, 1), (15054001, 1), (88875769, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409675 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_3, prime_oneHundredFiftySixEX_5, prime_oneHundredFiftySixEX_7, prime_oneHundredFiftySixEX_29, prime_oneHundredFiftySixEX_31, prime_oneHundredFiftySixEX_10071353, prime_oneHundredFiftySixEX_15054001, prime_oneHundredFiftySixEX_88875769]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409676 : Nat.totient 184433633920040298691772409676 = 92209308058712436606748822880 := by
  rw [← show ((([(2, 2), (12281, 1), (3754450653856369568678699, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409676 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_2, prime_oneHundredFiftySixEX_12281, prime_oneHundredFiftySixEX_3754450653856369568678699]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409677 : Nat.totient 184433633920040298691772409677 = 184309990574406364715119990848 := by
  rw [← show ((([(1877, 1), (7309, 1), (1129187, 1), (11905620066913247, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409677 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_1877, prime_oneHundredFiftySixEX_7309, prime_oneHundredFiftySixEX_1129187, prime_oneHundredFiftySixEX_11905620066913247]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409678 : Nat.totient 184433633920040298691772409678 = 51477183719686484517305088000 := by
  rw [← show ((([(2, 1), (3, 2), (11, 1), (13, 1), (461, 1), (69997, 1), (2220502305087140441, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409678 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_2, prime_oneHundredFiftySixEX_3, prime_oneHundredFiftySixEX_11, prime_oneHundredFiftySixEX_13, prime_oneHundredFiftySixEX_461, prime_oneHundredFiftySixEX_69997, prime_oneHundredFiftySixEX_2220502305087140441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409679 : Nat.totient 184433633920040298691772409679 = 183732292317286182650028055200 := by
  rw [← show ((([(263, 1), (2532919, 1), (371422451, 1), (745409496757, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409679 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_263, prime_oneHundredFiftySixEX_2532919, prime_oneHundredFiftySixEX_371422451, prime_oneHundredFiftySixEX_745409496757]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409680 : Nat.totient 184433633920040298691772409680 = 73598219711560024181039808000 := by
  rw [← show ((([(2, 4), (5, 1), (421, 1), (5476058014252977989660701, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409680 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_2, prime_oneHundredFiftySixEX_5, prime_oneHundredFiftySixEX_421, prime_oneHundredFiftySixEX_5476058014252977989660701]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409681 : Nat.totient 184433633920040298691772409681 = 120319156244461806769737600000 := by
  rw [← show ((([(3, 1), (59, 1), (251, 1), (3823, 1), (4027, 1), (15901, 1), (57397, 1), (295456519, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409681 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_3, prime_oneHundredFiftySixEX_59, prime_oneHundredFiftySixEX_251, prime_oneHundredFiftySixEX_3823, prime_oneHundredFiftySixEX_4027, prime_oneHundredFiftySixEX_15901, prime_oneHundredFiftySixEX_57397, prime_oneHundredFiftySixEX_295456519]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409682 : Nat.totient 184433633920040298691772409682 = 79042984656597333710184557520 := by
  rw [← show ((([(2, 1), (7, 1), (60378061, 1), (218189037145273558283, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409682 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_2, prime_oneHundredFiftySixEX_7, prime_oneHundredFiftySixEX_60378061, prime_oneHundredFiftySixEX_218189037145273558283]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409683 : Nat.totient 184433633920040298691772409683 = 174693746608837106188889272320 := by
  rw [← show ((([(43, 1), (47, 1), (109, 1), (624089, 1), (3231313, 1), (415165977371, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409683 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_43, prime_oneHundredFiftySixEX_47, prime_oneHundredFiftySixEX_109, prime_oneHundredFiftySixEX_624089, prime_oneHundredFiftySixEX_3231313, prime_oneHundredFiftySixEX_415165977371]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409684 : Nat.totient 184433633920040298691772409684 = 57694918757531316786648634368 := by
  rw [← show ((([(2, 2), (3, 1), (23, 1), (53, 1), (119929, 1), (105131039647847779157, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409684 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_2, prime_oneHundredFiftySixEX_3, prime_oneHundredFiftySixEX_23, prime_oneHundredFiftySixEX_53, prime_oneHundredFiftySixEX_119929, prime_oneHundredFiftySixEX_105131039647847779157]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409685 : Nat.totient 184433633920040298691772409685 = 147546907053497586929483910864 := by
  rw [← show ((([(5, 1), (1787696483, 1), (20633663004195807739, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409685 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_5, prime_oneHundredFiftySixEX_1787696483, prime_oneHundredFiftySixEX_20633663004195807739]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409686 : Nat.totient 184433633920040298691772409686 = 92207570312375506796067094680 := by
  rw [← show ((([(2, 1), (9973, 1), (9246647644642549819100191, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409686 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_2, prime_oneHundredFiftySixEX_9973, prime_oneHundredFiftySixEX_9246647644642549819100191]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409687 : Nat.totient 184433633920040298691772409687 = 119956833324975295245815877120 := by
  rw [← show ((([(3, 2), (41, 1), (68744369, 1), (7270706726899630967, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409687 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_3, prime_oneHundredFiftySixEX_41, prime_oneHundredFiftySixEX_68744369, prime_oneHundredFiftySixEX_7270706726899630967]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409688 : Nat.totient 184433633920040298691772409688 = 92216754357848915418602796000 := by
  rw [← show ((([(2, 3), (1473061, 1), (15650542808481819379151, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409688 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_2, prime_oneHundredFiftySixEX_1473061, prime_oneHundredFiftySixEX_15650542808481819379151]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409689 : Nat.totient 184433633920040298691772409689 = 132470820948909030938717310720 := by
  rw [← show ((([(7, 1), (11, 1), (19, 1), (37, 1), (4273343, 1), (797308364437574333, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409689 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_7, prime_oneHundredFiftySixEX_11, prime_oneHundredFiftySixEX_19, prime_oneHundredFiftySixEX_37, prime_oneHundredFiftySixEX_4273343, prime_oneHundredFiftySixEX_797308364437574333]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409690 : Nat.totient 184433633920040298691772409690 = 48961753937517424585439131200 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (223, 1), (27568555144998549879188701, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409690 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_2, prime_oneHundredFiftySixEX_3, prime_oneHundredFiftySixEX_5, prime_oneHundredFiftySixEX_223, prime_oneHundredFiftySixEX_27568555144998549879188701]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409691 : Nat.totient 184433633920040298691772409691 = 160231935064870726825760953344 := by
  rw [← show ((([(13, 1), (17, 1), (559319647, 1), (1492065108799822793, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409691 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_13, prime_oneHundredFiftySixEX_17, prime_oneHundredFiftySixEX_559319647, prime_oneHundredFiftySixEX_1492065108799822793]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409692 : Nat.totient 184433633920040298691772409692 = 92216816960015310959141096400 := by
  rw [← show ((([(2, 2), (19211985866123, 1), (2399981386688101, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409692 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_2, prime_oneHundredFiftySixEX_19211985866123, prime_oneHundredFiftySixEX_2399981386688101]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409693 : Nat.totient 184433633920040298691772409693 = 122955755946671193092454576000 := by
  rw [← show ((([(3, 1), (5506709036351, 1), (11164177654478881, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409693 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_3, prime_oneHundredFiftySixEX_5506709036351, prime_oneHundredFiftySixEX_11164177654478881]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409694 : Nat.totient 184433633920040298691772409694 = 91512871792386407747826004680 := by
  rw [← show ((([(2, 1), (131, 1), (703945167633741598060200037, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409694 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_2, prime_oneHundredFiftySixEX_131, prime_oneHundredFiftySixEX_703945167633741598060200037]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409695 : Nat.totient 184433633920040298691772409695 = 147454747918583124500605043200 := by
  rw [← show ((([(5, 1), (1601, 1), (23039804362278613203219539, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409695 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_5, prime_oneHundredFiftySixEX_1601, prime_oneHundredFiftySixEX_23039804362278613203219539]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409696 : Nat.totient 184433633920040298691772409696 = 52688052647779849960313025792 := by
  rw [← show ((([(2, 5), (3, 3), (7, 2), (7247, 1), (601135034269270369663, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409696 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_2, prime_oneHundredFiftySixEX_3, prime_oneHundredFiftySixEX_7, prime_oneHundredFiftySixEX_7247, prime_oneHundredFiftySixEX_601135034269270369663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409697 : Nat.totient 184433633920040298691772409697 = 184413533463749987447309482704 := by
  rw [← show ((([(9187, 1), (7389959, 1), (2716591753548710909, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409697 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_9187, prime_oneHundredFiftySixEX_7389959, prime_oneHundredFiftySixEX_2716591753548710909]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409698 : Nat.totient 184433633920040298691772409698 = 92152251161018738548161653760 := by
  rw [← show ((([(2, 1), (2153, 1), (4241, 1), (10099452370000124779513, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409698 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_2, prime_oneHundredFiftySixEX_2153, prime_oneHundredFiftySixEX_4241, prime_oneHundredFiftySixEX_10099452370000124779513]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409699 : Nat.totient 184433633920040298691772409699 = 122947608325200808749534821160 := by
  rw [← show ((([(3, 1), (15091, 1), (4073810746361855823377563, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409699 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_3, prime_oneHundredFiftySixEX_15091, prime_oneHundredFiftySixEX_4073810746361855823377563]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409700 : Nat.totient 184433633920040298691772409700 = 66970924051212997252718400000 := by
  rw [← show ((([(2, 2), (5, 2), (11, 1), (701, 1), (374317, 1), (638983830804654331, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409700 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_2, prime_oneHundredFiftySixEX_5, prime_oneHundredFiftySixEX_11, prime_oneHundredFiftySixEX_701, prime_oneHundredFiftySixEX_374317, prime_oneHundredFiftySixEX_638983830804654331]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftySixEX_184433633920040298691772409701 : Nat.totient 184433633920040298691772409701 = 184433633920040298691772409700 := by
  rw [← show ((([(184433633920040298691772409701, 1)] : List FactorBlock).map factorBlockValue).prod) = 184433633920040298691772409701 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftySixEX_184433633920040298691772409701]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64OneHundredFiftySixEX : certifiedKill 1 184433633920040298691772409599 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_oneHundredFiftySixEX_184433633920040298691772409600, phi_oneHundredFiftySixEX_184433633920040298691772409601, phi_oneHundredFiftySixEX_184433633920040298691772409602,
    phi_oneHundredFiftySixEX_184433633920040298691772409603, phi_oneHundredFiftySixEX_184433633920040298691772409604, phi_oneHundredFiftySixEX_184433633920040298691772409605,
    phi_oneHundredFiftySixEX_184433633920040298691772409606, phi_oneHundredFiftySixEX_184433633920040298691772409607, phi_oneHundredFiftySixEX_184433633920040298691772409608,
    phi_oneHundredFiftySixEX_184433633920040298691772409609, phi_oneHundredFiftySixEX_184433633920040298691772409610, phi_oneHundredFiftySixEX_184433633920040298691772409611,
    phi_oneHundredFiftySixEX_184433633920040298691772409612, phi_oneHundredFiftySixEX_184433633920040298691772409613, phi_oneHundredFiftySixEX_184433633920040298691772409614,
    phi_oneHundredFiftySixEX_184433633920040298691772409615, phi_oneHundredFiftySixEX_184433633920040298691772409616, phi_oneHundredFiftySixEX_184433633920040298691772409617,
    phi_oneHundredFiftySixEX_184433633920040298691772409618, phi_oneHundredFiftySixEX_184433633920040298691772409619, phi_oneHundredFiftySixEX_184433633920040298691772409620,
    phi_oneHundredFiftySixEX_184433633920040298691772409621, phi_oneHundredFiftySixEX_184433633920040298691772409622, phi_oneHundredFiftySixEX_184433633920040298691772409623,
    phi_oneHundredFiftySixEX_184433633920040298691772409624, phi_oneHundredFiftySixEX_184433633920040298691772409625, phi_oneHundredFiftySixEX_184433633920040298691772409626,
    phi_oneHundredFiftySixEX_184433633920040298691772409627, phi_oneHundredFiftySixEX_184433633920040298691772409628, phi_oneHundredFiftySixEX_184433633920040298691772409629,
    phi_oneHundredFiftySixEX_184433633920040298691772409630, phi_oneHundredFiftySixEX_184433633920040298691772409631, phi_oneHundredFiftySixEX_184433633920040298691772409632,
    phi_oneHundredFiftySixEX_184433633920040298691772409633, phi_oneHundredFiftySixEX_184433633920040298691772409634, phi_oneHundredFiftySixEX_184433633920040298691772409635,
    phi_oneHundredFiftySixEX_184433633920040298691772409636, phi_oneHundredFiftySixEX_184433633920040298691772409637, phi_oneHundredFiftySixEX_184433633920040298691772409638,
    phi_oneHundredFiftySixEX_184433633920040298691772409639, phi_oneHundredFiftySixEX_184433633920040298691772409640, phi_oneHundredFiftySixEX_184433633920040298691772409641,
    phi_oneHundredFiftySixEX_184433633920040298691772409642, phi_oneHundredFiftySixEX_184433633920040298691772409643, phi_oneHundredFiftySixEX_184433633920040298691772409644,
    phi_oneHundredFiftySixEX_184433633920040298691772409645, phi_oneHundredFiftySixEX_184433633920040298691772409646, phi_oneHundredFiftySixEX_184433633920040298691772409647,
    phi_oneHundredFiftySixEX_184433633920040298691772409648, phi_oneHundredFiftySixEX_184433633920040298691772409649, phi_oneHundredFiftySixEX_184433633920040298691772409650,
    phi_oneHundredFiftySixEX_184433633920040298691772409651, phi_oneHundredFiftySixEX_184433633920040298691772409652, phi_oneHundredFiftySixEX_184433633920040298691772409653,
    phi_oneHundredFiftySixEX_184433633920040298691772409654, phi_oneHundredFiftySixEX_184433633920040298691772409655, phi_oneHundredFiftySixEX_184433633920040298691772409656,
    phi_oneHundredFiftySixEX_184433633920040298691772409657, phi_oneHundredFiftySixEX_184433633920040298691772409658, phi_oneHundredFiftySixEX_184433633920040298691772409659,
    phi_oneHundredFiftySixEX_184433633920040298691772409660, phi_oneHundredFiftySixEX_184433633920040298691772409661, phi_oneHundredFiftySixEX_184433633920040298691772409662,
    phi_oneHundredFiftySixEX_184433633920040298691772409663, phi_oneHundredFiftySixEX_184433633920040298691772409664, phi_oneHundredFiftySixEX_184433633920040298691772409665,
    phi_oneHundredFiftySixEX_184433633920040298691772409666, phi_oneHundredFiftySixEX_184433633920040298691772409667, phi_oneHundredFiftySixEX_184433633920040298691772409668,
    phi_oneHundredFiftySixEX_184433633920040298691772409669, phi_oneHundredFiftySixEX_184433633920040298691772409670, phi_oneHundredFiftySixEX_184433633920040298691772409671,
    phi_oneHundredFiftySixEX_184433633920040298691772409672, phi_oneHundredFiftySixEX_184433633920040298691772409673, phi_oneHundredFiftySixEX_184433633920040298691772409674,
    phi_oneHundredFiftySixEX_184433633920040298691772409675, phi_oneHundredFiftySixEX_184433633920040298691772409676, phi_oneHundredFiftySixEX_184433633920040298691772409677,
    phi_oneHundredFiftySixEX_184433633920040298691772409678, phi_oneHundredFiftySixEX_184433633920040298691772409679, phi_oneHundredFiftySixEX_184433633920040298691772409680,
    phi_oneHundredFiftySixEX_184433633920040298691772409681, phi_oneHundredFiftySixEX_184433633920040298691772409682, phi_oneHundredFiftySixEX_184433633920040298691772409683,
    phi_oneHundredFiftySixEX_184433633920040298691772409684, phi_oneHundredFiftySixEX_184433633920040298691772409685, phi_oneHundredFiftySixEX_184433633920040298691772409686,
    phi_oneHundredFiftySixEX_184433633920040298691772409687, phi_oneHundredFiftySixEX_184433633920040298691772409688, phi_oneHundredFiftySixEX_184433633920040298691772409689,
    phi_oneHundredFiftySixEX_184433633920040298691772409690, phi_oneHundredFiftySixEX_184433633920040298691772409691, phi_oneHundredFiftySixEX_184433633920040298691772409692,
    phi_oneHundredFiftySixEX_184433633920040298691772409693, phi_oneHundredFiftySixEX_184433633920040298691772409694, phi_oneHundredFiftySixEX_184433633920040298691772409695,
    phi_oneHundredFiftySixEX_184433633920040298691772409696, phi_oneHundredFiftySixEX_184433633920040298691772409697, phi_oneHundredFiftySixEX_184433633920040298691772409698,
    phi_oneHundredFiftySixEX_184433633920040298691772409699, phi_oneHundredFiftySixEX_184433633920040298691772409700, phi_oneHundredFiftySixEX_184433633920040298691772409701]

end TotientTailPeriodKiller
end Erdos249257
