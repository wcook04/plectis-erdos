import Erdos249257.DiagonalPincerCertificatesT64

/- Kernel-checked off-diagonal certificate at a freely chosen position. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def oneHundredTwentyOneDOFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem oneHundredTwentyOneDOFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : oneHundredTwentyOneDOFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [oneHundredTwentyOneDOFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [oneHundredTwentyOneDOFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then oneHundredTwentyOneDOFastPow a n * oneHundredTwentyOneDOFastPow a n * a else oneHundredTwentyOneDOFastPow a n * oneHundredTwentyOneDOFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_oneHundredTwentyOneDO_2 : Nat.Prime 2 := by norm_num

private theorem prime_oneHundredTwentyOneDO_3 : Nat.Prime 3 := by norm_num

private theorem prime_oneHundredTwentyOneDO_5 : Nat.Prime 5 := by norm_num

private theorem prime_oneHundredTwentyOneDO_7 : Nat.Prime 7 := by norm_num

private theorem prime_oneHundredTwentyOneDO_11 : Nat.Prime 11 := by norm_num

private theorem prime_oneHundredTwentyOneDO_13 : Nat.Prime 13 := by norm_num

private theorem prime_oneHundredTwentyOneDO_17 : Nat.Prime 17 := by norm_num

private theorem prime_oneHundredTwentyOneDO_19 : Nat.Prime 19 := by norm_num

private theorem prime_oneHundredTwentyOneDO_23 : Nat.Prime 23 := by norm_num

private theorem prime_oneHundredTwentyOneDO_29 : Nat.Prime 29 := by norm_num

private theorem prime_oneHundredTwentyOneDO_31 : Nat.Prime 31 := by norm_num

private theorem prime_oneHundredTwentyOneDO_37 : Nat.Prime 37 := by norm_num

private theorem prime_oneHundredTwentyOneDO_41 : Nat.Prime 41 := by norm_num

private theorem prime_oneHundredTwentyOneDO_43 : Nat.Prime 43 := by norm_num

private theorem prime_oneHundredTwentyOneDO_47 : Nat.Prime 47 := by norm_num

private theorem prime_oneHundredTwentyOneDO_53 : Nat.Prime 53 := by norm_num

private theorem prime_oneHundredTwentyOneDO_59 : Nat.Prime 59 := by norm_num

private theorem prime_oneHundredTwentyOneDO_61 : Nat.Prime 61 := by norm_num

private theorem prime_oneHundredTwentyOneDO_67 : Nat.Prime 67 := by norm_num

private theorem prime_oneHundredTwentyOneDO_71 : Nat.Prime 71 := by norm_num

private theorem prime_oneHundredTwentyOneDO_73 : Nat.Prime 73 := by norm_num

private theorem prime_oneHundredTwentyOneDO_79 : Nat.Prime 79 := by norm_num

private theorem prime_oneHundredTwentyOneDO_83 : Nat.Prime 83 := by norm_num

private theorem prime_oneHundredTwentyOneDO_89 : Nat.Prime 89 := by norm_num

private theorem prime_oneHundredTwentyOneDO_97 : Nat.Prime 97 := by norm_num

private theorem prime_oneHundredTwentyOneDO_101 : Nat.Prime 101 := by norm_num

private theorem prime_oneHundredTwentyOneDO_103 : Nat.Prime 103 := by norm_num

private theorem prime_oneHundredTwentyOneDO_107 : Nat.Prime 107 := by norm_num

private theorem prime_oneHundredTwentyOneDO_113 : Nat.Prime 113 := by norm_num

private theorem prime_oneHundredTwentyOneDO_127 : Nat.Prime 127 := by norm_num

private theorem prime_oneHundredTwentyOneDO_131 : Nat.Prime 131 := by norm_num

private theorem prime_oneHundredTwentyOneDO_137 : Nat.Prime 137 := by norm_num

private theorem prime_oneHundredTwentyOneDO_139 : Nat.Prime 139 := by norm_num

private theorem prime_oneHundredTwentyOneDO_149 : Nat.Prime 149 := by norm_num

private theorem prime_oneHundredTwentyOneDO_157 : Nat.Prime 157 := by norm_num

private theorem prime_oneHundredTwentyOneDO_163 : Nat.Prime 163 := by norm_num

private theorem prime_oneHundredTwentyOneDO_167 : Nat.Prime 167 := by norm_num

private theorem prime_oneHundredTwentyOneDO_173 : Nat.Prime 173 := by norm_num

private theorem prime_oneHundredTwentyOneDO_179 : Nat.Prime 179 := by norm_num

private theorem prime_oneHundredTwentyOneDO_181 : Nat.Prime 181 := by norm_num

private theorem prime_oneHundredTwentyOneDO_191 : Nat.Prime 191 := by norm_num

private theorem prime_oneHundredTwentyOneDO_193 : Nat.Prime 193 := by norm_num

private theorem prime_oneHundredTwentyOneDO_197 : Nat.Prime 197 := by norm_num

private theorem prime_oneHundredTwentyOneDO_199 : Nat.Prime 199 := by norm_num

private theorem prime_oneHundredTwentyOneDO_211 : Nat.Prime 211 := by norm_num

private theorem prime_oneHundredTwentyOneDO_229 : Nat.Prime 229 := by norm_num

private theorem prime_oneHundredTwentyOneDO_239 : Nat.Prime 239 := by norm_num

private theorem prime_oneHundredTwentyOneDO_241 : Nat.Prime 241 := by norm_num

private theorem prime_oneHundredTwentyOneDO_251 : Nat.Prime 251 := by norm_num

private theorem prime_oneHundredTwentyOneDO_257 : Nat.Prime 257 := by norm_num

private theorem prime_oneHundredTwentyOneDO_271 : Nat.Prime 271 := by norm_num

private theorem prime_oneHundredTwentyOneDO_277 : Nat.Prime 277 := by norm_num

private theorem prime_oneHundredTwentyOneDO_281 : Nat.Prime 281 := by norm_num

private theorem prime_oneHundredTwentyOneDO_283 : Nat.Prime 283 := by norm_num

private theorem prime_oneHundredTwentyOneDO_307 : Nat.Prime 307 := by norm_num

private theorem prime_oneHundredTwentyOneDO_311 : Nat.Prime 311 := by norm_num

private theorem prime_oneHundredTwentyOneDO_313 : Nat.Prime 313 := by norm_num

private theorem prime_oneHundredTwentyOneDO_317 : Nat.Prime 317 := by norm_num

private theorem prime_oneHundredTwentyOneDO_337 : Nat.Prime 337 := by norm_num

private theorem prime_oneHundredTwentyOneDO_347 : Nat.Prime 347 := by norm_num

private theorem prime_oneHundredTwentyOneDO_349 : Nat.Prime 349 := by norm_num

private theorem prime_oneHundredTwentyOneDO_353 : Nat.Prime 353 := by norm_num

private theorem prime_oneHundredTwentyOneDO_379 : Nat.Prime 379 := by norm_num

private theorem prime_oneHundredTwentyOneDO_389 : Nat.Prime 389 := by norm_num

private theorem prime_oneHundredTwentyOneDO_401 : Nat.Prime 401 := by norm_num

private theorem prime_oneHundredTwentyOneDO_409 : Nat.Prime 409 := by norm_num

private theorem prime_oneHundredTwentyOneDO_419 : Nat.Prime 419 := by norm_num

private theorem prime_oneHundredTwentyOneDO_433 : Nat.Prime 433 := by norm_num

private theorem prime_oneHundredTwentyOneDO_467 : Nat.Prime 467 := by norm_num

private theorem prime_oneHundredTwentyOneDO_503 : Nat.Prime 503 := by norm_num

private theorem prime_oneHundredTwentyOneDO_563 : Nat.Prime 563 := by norm_num

private theorem prime_oneHundredTwentyOneDO_577 : Nat.Prime 577 := by norm_num

private theorem prime_oneHundredTwentyOneDO_587 : Nat.Prime 587 := by norm_num

private theorem prime_oneHundredTwentyOneDO_619 : Nat.Prime 619 := by norm_num

private theorem prime_oneHundredTwentyOneDO_641 : Nat.Prime 641 := by norm_num

private theorem prime_oneHundredTwentyOneDO_647 : Nat.Prime 647 := by norm_num

private theorem prime_oneHundredTwentyOneDO_659 : Nat.Prime 659 := by norm_num

private theorem prime_oneHundredTwentyOneDO_661 : Nat.Prime 661 := by norm_num

private theorem prime_oneHundredTwentyOneDO_673 : Nat.Prime 673 := by norm_num

private theorem prime_oneHundredTwentyOneDO_709 : Nat.Prime 709 := by norm_num

private theorem prime_oneHundredTwentyOneDO_733 : Nat.Prime 733 := by norm_num

private theorem prime_oneHundredTwentyOneDO_751 : Nat.Prime 751 := by norm_num

private theorem prime_oneHundredTwentyOneDO_761 : Nat.Prime 761 := by norm_num

private theorem prime_oneHundredTwentyOneDO_769 : Nat.Prime 769 := by norm_num

private theorem prime_oneHundredTwentyOneDO_787 : Nat.Prime 787 := by norm_num

private theorem prime_oneHundredTwentyOneDO_809 : Nat.Prime 809 := by norm_num

private theorem prime_oneHundredTwentyOneDO_821 : Nat.Prime 821 := by norm_num

private theorem prime_oneHundredTwentyOneDO_839 : Nat.Prime 839 := by norm_num

private theorem prime_oneHundredTwentyOneDO_929 : Nat.Prime 929 := by norm_num

private theorem prime_oneHundredTwentyOneDO_937 : Nat.Prime 937 := by norm_num

private theorem prime_oneHundredTwentyOneDO_967 : Nat.Prime 967 := by norm_num

private theorem prime_oneHundredTwentyOneDO_991 : Nat.Prime 991 := by norm_num

private theorem prime_oneHundredTwentyOneDO_1009 : Nat.Prime 1009 := by norm_num

private theorem prime_oneHundredTwentyOneDO_1021 : Nat.Prime 1021 := by norm_num

private theorem prime_oneHundredTwentyOneDO_1033 : Nat.Prime 1033 := by norm_num

private theorem prime_oneHundredTwentyOneDO_1063 : Nat.Prime 1063 := by norm_num

private theorem prime_oneHundredTwentyOneDO_1069 : Nat.Prime 1069 := by norm_num

private theorem prime_oneHundredTwentyOneDO_1129 : Nat.Prime 1129 := by norm_num

private theorem prime_oneHundredTwentyOneDO_1201 : Nat.Prime 1201 := by norm_num

private theorem prime_oneHundredTwentyOneDO_1217 : Nat.Prime 1217 := by norm_num

private theorem prime_oneHundredTwentyOneDO_1237 : Nat.Prime 1237 := by norm_num

private theorem prime_oneHundredTwentyOneDO_1259 : Nat.Prime 1259 := by norm_num

private theorem prime_oneHundredTwentyOneDO_1279 : Nat.Prime 1279 := by norm_num

private theorem prime_oneHundredTwentyOneDO_1303 : Nat.Prime 1303 := by norm_num

private theorem prime_oneHundredTwentyOneDO_1319 : Nat.Prime 1319 := by norm_num

private theorem prime_oneHundredTwentyOneDO_1321 : Nat.Prime 1321 := by norm_num

private theorem prime_oneHundredTwentyOneDO_1399 : Nat.Prime 1399 := by norm_num

private theorem prime_oneHundredTwentyOneDO_1451 : Nat.Prime 1451 := by norm_num

private theorem prime_oneHundredTwentyOneDO_1459 : Nat.Prime 1459 := by norm_num

private theorem prime_oneHundredTwentyOneDO_1499 : Nat.Prime 1499 := by norm_num

private theorem prime_oneHundredTwentyOneDO_1579 : Nat.Prime 1579 := by norm_num

private theorem prime_oneHundredTwentyOneDO_1583 : Nat.Prime 1583 := by norm_num

private theorem prime_oneHundredTwentyOneDO_1609 : Nat.Prime 1609 := by norm_num

private theorem prime_oneHundredTwentyOneDO_1657 : Nat.Prime 1657 := by norm_num

private theorem prime_oneHundredTwentyOneDO_1741 : Nat.Prime 1741 := by norm_num

private theorem prime_oneHundredTwentyOneDO_1861 : Nat.Prime 1861 := by norm_num

private theorem prime_oneHundredTwentyOneDO_1901 : Nat.Prime 1901 := by norm_num

private theorem prime_oneHundredTwentyOneDO_1907 : Nat.Prime 1907 := by norm_num

private theorem prime_oneHundredTwentyOneDO_1913 : Nat.Prime 1913 := by norm_num

private theorem prime_oneHundredTwentyOneDO_1931 : Nat.Prime 1931 := by norm_num

private theorem prime_oneHundredTwentyOneDO_2003 : Nat.Prime 2003 := by norm_num

private theorem prime_oneHundredTwentyOneDO_2029 : Nat.Prime 2029 := by norm_num

private theorem prime_oneHundredTwentyOneDO_2081 : Nat.Prime 2081 := by norm_num

private theorem prime_oneHundredTwentyOneDO_2087 : Nat.Prime 2087 := by norm_num

private theorem prime_oneHundredTwentyOneDO_2089 : Nat.Prime 2089 := by norm_num

private theorem prime_oneHundredTwentyOneDO_2143 : Nat.Prime 2143 := by norm_num

private theorem prime_oneHundredTwentyOneDO_2239 : Nat.Prime 2239 := by norm_num

private theorem prime_oneHundredTwentyOneDO_2293 : Nat.Prime 2293 := by norm_num

private theorem prime_oneHundredTwentyOneDO_2389 : Nat.Prime 2389 := by norm_num

private theorem prime_oneHundredTwentyOneDO_2549 : Nat.Prime 2549 := by norm_num

private theorem prime_oneHundredTwentyOneDO_2593 : Nat.Prime 2593 := by norm_num

private theorem prime_oneHundredTwentyOneDO_2617 : Nat.Prime 2617 := by norm_num

private theorem prime_oneHundredTwentyOneDO_2687 : Nat.Prime 2687 := by norm_num

private theorem prime_oneHundredTwentyOneDO_2803 : Nat.Prime 2803 := by norm_num

private theorem prime_oneHundredTwentyOneDO_2837 : Nat.Prime 2837 := by norm_num

private theorem prime_oneHundredTwentyOneDO_2969 : Nat.Prime 2969 := by norm_num

private theorem prime_oneHundredTwentyOneDO_3001 : Nat.Prime 3001 := by norm_num

private theorem prime_oneHundredTwentyOneDO_3049 : Nat.Prime 3049 := by norm_num

private theorem prime_oneHundredTwentyOneDO_3191 : Nat.Prime 3191 := by norm_num

private theorem prime_oneHundredTwentyOneDO_3271 : Nat.Prime 3271 := by norm_num

private theorem prime_oneHundredTwentyOneDO_3389 : Nat.Prime 3389 := by norm_num

private theorem prime_oneHundredTwentyOneDO_3457 : Nat.Prime 3457 := by norm_num

private theorem prime_oneHundredTwentyOneDO_3533 : Nat.Prime 3533 := by norm_num

private theorem prime_oneHundredTwentyOneDO_3623 : Nat.Prime 3623 := by norm_num

private theorem prime_oneHundredTwentyOneDO_3767 : Nat.Prime 3767 := by norm_num

private theorem prime_oneHundredTwentyOneDO_3881 : Nat.Prime 3881 := by norm_num

private theorem prime_oneHundredTwentyOneDO_4019 : Nat.Prime 4019 := by norm_num

private theorem prime_oneHundredTwentyOneDO_4051 : Nat.Prime 4051 := by norm_num

private theorem prime_oneHundredTwentyOneDO_4079 : Nat.Prime 4079 := by norm_num

private theorem prime_oneHundredTwentyOneDO_4091 : Nat.Prime 4091 := by norm_num

private theorem prime_oneHundredTwentyOneDO_4133 : Nat.Prime 4133 := by norm_num

private theorem prime_oneHundredTwentyOneDO_4289 : Nat.Prime 4289 := by norm_num

private theorem prime_oneHundredTwentyOneDO_4397 : Nat.Prime 4397 := by norm_num

private theorem prime_oneHundredTwentyOneDO_4513 : Nat.Prime 4513 := by norm_num

private theorem prime_oneHundredTwentyOneDO_4637 : Nat.Prime 4637 := by norm_num

private theorem prime_oneHundredTwentyOneDO_4999 : Nat.Prime 4999 := by norm_num

private theorem prime_oneHundredTwentyOneDO_5507 : Nat.Prime 5507 := by norm_num

private theorem prime_oneHundredTwentyOneDO_5647 : Nat.Prime 5647 := by norm_num

private theorem prime_oneHundredTwentyOneDO_5821 : Nat.Prime 5821 := by norm_num

private theorem prime_oneHundredTwentyOneDO_5953 : Nat.Prime 5953 := by norm_num

private theorem prime_oneHundredTwentyOneDO_6211 : Nat.Prime 6211 := by norm_num

private theorem prime_oneHundredTwentyOneDO_6269 : Nat.Prime 6269 := by norm_num

private theorem prime_oneHundredTwentyOneDO_6451 : Nat.Prime 6451 := by norm_num

private theorem prime_oneHundredTwentyOneDO_6761 : Nat.Prime 6761 := by norm_num

private theorem prime_oneHundredTwentyOneDO_7001 : Nat.Prime 7001 := by norm_num

private theorem prime_oneHundredTwentyOneDO_7459 : Nat.Prime 7459 := by norm_num

private theorem prime_oneHundredTwentyOneDO_7477 : Nat.Prime 7477 := by norm_num

private theorem prime_oneHundredTwentyOneDO_7591 : Nat.Prime 7591 := by norm_num

private theorem prime_oneHundredTwentyOneDO_7691 : Nat.Prime 7691 := by norm_num

private theorem prime_oneHundredTwentyOneDO_7793 : Nat.Prime 7793 := by norm_num

private theorem prime_oneHundredTwentyOneDO_7879 : Nat.Prime 7879 := by norm_num

private theorem prime_oneHundredTwentyOneDO_8069 : Nat.Prime 8069 := by norm_num

private theorem prime_oneHundredTwentyOneDO_8221 : Nat.Prime 8221 := by norm_num

private theorem prime_oneHundredTwentyOneDO_8237 : Nat.Prime 8237 := by norm_num

private theorem prime_oneHundredTwentyOneDO_8263 : Nat.Prime 8263 := by norm_num

private theorem prime_oneHundredTwentyOneDO_8317 : Nat.Prime 8317 := by norm_num

private theorem prime_oneHundredTwentyOneDO_8377 : Nat.Prime 8377 := by norm_num

private theorem prime_oneHundredTwentyOneDO_8597 : Nat.Prime 8597 := by norm_num

private theorem prime_oneHundredTwentyOneDO_8893 : Nat.Prime 8893 := by norm_num

private theorem prime_oneHundredTwentyOneDO_9067 : Nat.Prime 9067 := by norm_num

private theorem prime_oneHundredTwentyOneDO_9199 : Nat.Prime 9199 := by norm_num

private theorem prime_oneHundredTwentyOneDO_9203 : Nat.Prime 9203 := by norm_num

private theorem prime_oneHundredTwentyOneDO_9697 : Nat.Prime 9697 := by norm_num

private theorem prime_oneHundredTwentyOneDO_10459 : Nat.Prime 10459 := by norm_num

private theorem prime_oneHundredTwentyOneDO_10663 : Nat.Prime 10663 := by norm_num

private theorem prime_oneHundredTwentyOneDO_10753 : Nat.Prime 10753 := by norm_num

private theorem prime_oneHundredTwentyOneDO_10861 : Nat.Prime 10861 := by norm_num

private theorem prime_oneHundredTwentyOneDO_10939 : Nat.Prime 10939 := by norm_num

private theorem prime_oneHundredTwentyOneDO_11149 : Nat.Prime 11149 := by norm_num

private theorem prime_oneHundredTwentyOneDO_12379 : Nat.Prime 12379 := by norm_num

private theorem prime_oneHundredTwentyOneDO_12433 : Nat.Prime 12433 := by norm_num

private theorem prime_oneHundredTwentyOneDO_13183 : Nat.Prime 13183 := by norm_num

private theorem prime_oneHundredTwentyOneDO_13309 : Nat.Prime 13309 := by norm_num

private theorem prime_oneHundredTwentyOneDO_13339 : Nat.Prime 13339 := by norm_num

private theorem prime_oneHundredTwentyOneDO_13829 : Nat.Prime 13829 := by norm_num

private theorem prime_oneHundredTwentyOneDO_13901 : Nat.Prime 13901 := by norm_num

private theorem prime_oneHundredTwentyOneDO_14057 : Nat.Prime 14057 := by norm_num

private theorem prime_oneHundredTwentyOneDO_14173 : Nat.Prime 14173 := by norm_num

private theorem prime_oneHundredTwentyOneDO_15227 : Nat.Prime 15227 := by norm_num

private theorem prime_oneHundredTwentyOneDO_15731 : Nat.Prime 15731 := by norm_num

private theorem prime_oneHundredTwentyOneDO_15787 : Nat.Prime 15787 := by norm_num

private theorem prime_oneHundredTwentyOneDO_16091 : Nat.Prime 16091 := by norm_num

private theorem prime_oneHundredTwentyOneDO_17047 : Nat.Prime 17047 := by norm_num

private theorem prime_oneHundredTwentyOneDO_17203 : Nat.Prime 17203 := by norm_num

private theorem prime_oneHundredTwentyOneDO_18541 : Nat.Prime 18541 := by norm_num

private theorem prime_oneHundredTwentyOneDO_19477 : Nat.Prime 19477 := by norm_num

private theorem prime_oneHundredTwentyOneDO_19597 : Nat.Prime 19597 := by norm_num

private theorem prime_oneHundredTwentyOneDO_19753 : Nat.Prime 19753 := by norm_num

private theorem prime_oneHundredTwentyOneDO_19759 : Nat.Prime 19759 := by norm_num

private theorem prime_oneHundredTwentyOneDO_20753 : Nat.Prime 20753 := by norm_num

private theorem prime_oneHundredTwentyOneDO_21617 : Nat.Prime 21617 := by norm_num

private theorem prime_oneHundredTwentyOneDO_22063 : Nat.Prime 22063 := by norm_num

private theorem prime_oneHundredTwentyOneDO_22159 : Nat.Prime 22159 := by norm_num

private theorem prime_oneHundredTwentyOneDO_23753 : Nat.Prime 23753 := by norm_num

private theorem prime_oneHundredTwentyOneDO_25849 : Nat.Prime 25849 := by norm_num

private theorem prime_oneHundredTwentyOneDO_25939 : Nat.Prime 25939 := by norm_num

private theorem prime_oneHundredTwentyOneDO_26113 : Nat.Prime 26113 := by norm_num

private theorem prime_oneHundredTwentyOneDO_26267 : Nat.Prime 26267 := by norm_num

private theorem prime_oneHundredTwentyOneDO_26321 : Nat.Prime 26321 := by norm_num

private theorem prime_oneHundredTwentyOneDO_28181 : Nat.Prime 28181 := by norm_num

private theorem prime_oneHundredTwentyOneDO_28547 : Nat.Prime 28547 := by norm_num

private theorem prime_oneHundredTwentyOneDO_28559 : Nat.Prime 28559 := by norm_num

private theorem prime_oneHundredTwentyOneDO_28573 : Nat.Prime 28573 := by norm_num

private theorem prime_oneHundredTwentyOneDO_30047 : Nat.Prime 30047 := by norm_num

private theorem prime_oneHundredTwentyOneDO_30983 : Nat.Prime 30983 := by norm_num

private theorem prime_oneHundredTwentyOneDO_32009 : Nat.Prime 32009 := by norm_num

private theorem prime_oneHundredTwentyOneDO_32309 : Nat.Prime 32309 := by norm_num

private theorem prime_oneHundredTwentyOneDO_32749 : Nat.Prime 32749 := by norm_num

private theorem prime_oneHundredTwentyOneDO_33199 : Nat.Prime 33199 := by norm_num

private theorem prime_oneHundredTwentyOneDO_34301 : Nat.Prime 34301 := by norm_num

private theorem prime_oneHundredTwentyOneDO_34537 : Nat.Prime 34537 := by norm_num

private theorem prime_oneHundredTwentyOneDO_35381 : Nat.Prime 35381 := by norm_num

private theorem prime_oneHundredTwentyOneDO_36653 : Nat.Prime 36653 := by norm_num

private theorem prime_oneHundredTwentyOneDO_39983 : Nat.Prime 39983 := by norm_num

private theorem prime_oneHundredTwentyOneDO_40559 : Nat.Prime 40559 := by norm_num

private theorem prime_oneHundredTwentyOneDO_42197 : Nat.Prime 42197 := by norm_num

private theorem prime_oneHundredTwentyOneDO_42443 : Nat.Prime 42443 := by norm_num

private theorem prime_oneHundredTwentyOneDO_43759 : Nat.Prime 43759 := by norm_num

private theorem prime_oneHundredTwentyOneDO_45863 : Nat.Prime 45863 := by norm_num

private theorem prime_oneHundredTwentyOneDO_47093 : Nat.Prime 47093 := by norm_num

private theorem prime_oneHundredTwentyOneDO_47459 : Nat.Prime 47459 := by norm_num

private theorem prime_oneHundredTwentyOneDO_52529 : Nat.Prime 52529 := by norm_num

private theorem prime_oneHundredTwentyOneDO_59207 : Nat.Prime 59207 := by norm_num

private theorem prime_oneHundredTwentyOneDO_61471 : Nat.Prime 61471 := by norm_num

private theorem prime_oneHundredTwentyOneDO_61757 : Nat.Prime 61757 := by norm_num

private theorem prime_oneHundredTwentyOneDO_62071 : Nat.Prime 62071 := by norm_num

private theorem prime_oneHundredTwentyOneDO_62401 : Nat.Prime 62401 := by norm_num

private theorem prime_oneHundredTwentyOneDO_67979 : Nat.Prime 67979 := by norm_num

private theorem prime_oneHundredTwentyOneDO_68543 : Nat.Prime 68543 := by norm_num

private theorem prime_oneHundredTwentyOneDO_70051 : Nat.Prime 70051 := by norm_num

private theorem prime_oneHundredTwentyOneDO_70729 : Nat.Prime 70729 := by norm_num

private theorem prime_oneHundredTwentyOneDO_82847 : Nat.Prime 82847 := by norm_num

private theorem prime_oneHundredTwentyOneDO_85607 : Nat.Prime 85607 := by norm_num

private theorem prime_oneHundredTwentyOneDO_88741 : Nat.Prime 88741 := by norm_num

private theorem prime_oneHundredTwentyOneDO_92311 : Nat.Prime 92311 := by norm_num

private theorem prime_oneHundredTwentyOneDO_92641 : Nat.Prime 92641 := by norm_num

private theorem prime_oneHundredTwentyOneDO_102079 : Nat.Prime 102079 := by norm_num

private theorem prime_oneHundredTwentyOneDO_112031 : Nat.Prime 112031 := by norm_num

private theorem prime_oneHundredTwentyOneDO_115309 : Nat.Prime 115309 := by norm_num

private theorem prime_oneHundredTwentyOneDO_123821 : Nat.Prime 123821 := by norm_num

private theorem prime_oneHundredTwentyOneDO_139343 : Nat.Prime 139343 := by norm_num

private theorem prime_oneHundredTwentyOneDO_144593 : Nat.Prime 144593 := by norm_num

private theorem prime_oneHundredTwentyOneDO_145463 : Nat.Prime 145463 := by norm_num

private theorem prime_oneHundredTwentyOneDO_149689 : Nat.Prime 149689 := by norm_num

private theorem prime_oneHundredTwentyOneDO_158657 : Nat.Prime 158657 := by norm_num

private theorem prime_oneHundredTwentyOneDO_171401 : Nat.Prime 171401 := by norm_num

private theorem prime_oneHundredTwentyOneDO_177091 : Nat.Prime 177091 := by norm_num

private theorem prime_oneHundredTwentyOneDO_182123 : Nat.Prime 182123 := by norm_num

private theorem prime_oneHundredTwentyOneDO_201791 : Nat.Prime 201791 := by norm_num

private theorem prime_oneHundredTwentyOneDO_255589 : Nat.Prime 255589 := by norm_num

private theorem prime_oneHundredTwentyOneDO_273083 : Nat.Prime 273083 := by norm_num

private theorem prime_oneHundredTwentyOneDO_276049 : Nat.Prime 276049 := by norm_num

private theorem prime_oneHundredTwentyOneDO_276449 : Nat.Prime 276449 := by norm_num

private theorem prime_oneHundredTwentyOneDO_287383 : Nat.Prime 287383 := by norm_num

private theorem prime_oneHundredTwentyOneDO_289309 : Nat.Prime 289309 := by norm_num

private theorem prime_oneHundredTwentyOneDO_296683 : Nat.Prime 296683 := by norm_num

private theorem prime_oneHundredTwentyOneDO_328379 : Nat.Prime 328379 := by norm_num

private theorem prime_oneHundredTwentyOneDO_329993 : Nat.Prime 329993 := by norm_num

private theorem prime_oneHundredTwentyOneDO_354439 : Nat.Prime 354439 := by norm_num

private theorem prime_oneHundredTwentyOneDO_377137 : Nat.Prime 377137 := by norm_num

private theorem prime_oneHundredTwentyOneDO_399481 : Nat.Prime 399481 := by norm_num

private theorem prime_oneHundredTwentyOneDO_424001 : Nat.Prime 424001 := by norm_num

private theorem prime_oneHundredTwentyOneDO_450301 : Nat.Prime 450301 := by norm_num

private theorem prime_oneHundredTwentyOneDO_452017 : Nat.Prime 452017 := by norm_num

private theorem prime_oneHundredTwentyOneDO_458483 : Nat.Prime 458483 := by norm_num

private theorem prime_oneHundredTwentyOneDO_500333 : Nat.Prime 500333 := by norm_num

private theorem prime_oneHundredTwentyOneDO_506687 : Nat.Prime 506687 := by norm_num

private theorem prime_oneHundredTwentyOneDO_514001 : Nat.Prime 514001 := by norm_num

private theorem prime_oneHundredTwentyOneDO_519611 : Nat.Prime 519611 := by norm_num

private theorem prime_oneHundredTwentyOneDO_526583 : Nat.Prime 526583 := by norm_num

private theorem prime_oneHundredTwentyOneDO_536719 : Nat.Prime 536719 := by norm_num

private theorem prime_oneHundredTwentyOneDO_582773 : Nat.Prime 582773 := by norm_num

private theorem prime_oneHundredTwentyOneDO_600857 : Nat.Prime 600857 := by norm_num

private theorem prime_oneHundredTwentyOneDO_609101 : Nat.Prime 609101 := by norm_num

private theorem prime_oneHundredTwentyOneDO_617693 : Nat.Prime 617693 := by norm_num

private theorem prime_oneHundredTwentyOneDO_623209 : Nat.Prime 623209 := by norm_num

private theorem prime_oneHundredTwentyOneDO_650189 : Nat.Prime 650189 := by norm_num

private theorem prime_oneHundredTwentyOneDO_655489 : Nat.Prime 655489 := by norm_num

private theorem prime_oneHundredTwentyOneDO_687437 : Nat.Prime 687437 := by norm_num

private theorem prime_oneHundredTwentyOneDO_738317 : Nat.Prime 738317 := by norm_num

private theorem prime_oneHundredTwentyOneDO_747827 : Nat.Prime 747827 := by norm_num

private theorem prime_oneHundredTwentyOneDO_795253 : Nat.Prime 795253 := by norm_num

private theorem prime_oneHundredTwentyOneDO_825479 : Nat.Prime 825479 := by norm_num

private theorem prime_oneHundredTwentyOneDO_831619 : Nat.Prime 831619 := by norm_num

private theorem prime_oneHundredTwentyOneDO_854443 : Nat.Prime 854443 := by norm_num

private theorem prime_oneHundredTwentyOneDO_856393 : Nat.Prime 856393 := by norm_num

private theorem prime_oneHundredTwentyOneDO_869119 : Nat.Prime 869119 := by norm_num

private theorem prime_oneHundredTwentyOneDO_890993 : Nat.Prime 890993 := by norm_num

private theorem prime_oneHundredTwentyOneDO_945179 : Nat.Prime 945179 := by norm_num

private theorem prime_oneHundredTwentyOneDO_983993 : Nat.Prime 983993 := by norm_num

private theorem prime_oneHundredTwentyOneDO_1011079 : Nat.Prime 1011079 := by norm_num

private theorem prime_oneHundredTwentyOneDO_1136287 : Nat.Prime 1136287 := by norm_num

private theorem prime_oneHundredTwentyOneDO_1156307 : Nat.Prime 1156307 := by norm_num

private theorem prime_oneHundredTwentyOneDO_1156403 : Nat.Prime 1156403 := by norm_num

private theorem prime_oneHundredTwentyOneDO_1161757 : Nat.Prime 1161757 := by norm_num

private theorem prime_oneHundredTwentyOneDO_1204859 : Nat.Prime 1204859 := by norm_num

private theorem prime_oneHundredTwentyOneDO_1265657 : Nat.Prime 1265657 := by norm_num

private theorem prime_oneHundredTwentyOneDO_1276397 : Nat.Prime 1276397 := by norm_num

private theorem prime_oneHundredTwentyOneDO_1284487 : Nat.Prime 1284487 := by norm_num

private theorem prime_oneHundredTwentyOneDO_1318781 : Nat.Prime 1318781 := by norm_num

private theorem prime_oneHundredTwentyOneDO_1335259 : Nat.Prime 1335259 := by norm_num

private theorem prime_oneHundredTwentyOneDO_1415851 : Nat.Prime 1415851 := by norm_num

private theorem prime_oneHundredTwentyOneDO_1427653 : Nat.Prime 1427653 := by norm_num

private theorem prime_oneHundredTwentyOneDO_1439561 : Nat.Prime 1439561 := by norm_num

private theorem prime_oneHundredTwentyOneDO_1592671 : Nat.Prime 1592671 := by norm_num

private theorem prime_oneHundredTwentyOneDO_1604521 : Nat.Prime 1604521 := by norm_num

private theorem prime_oneHundredTwentyOneDO_1661437 : Nat.Prime 1661437 := by norm_num

private theorem prime_oneHundredTwentyOneDO_2005739 : Nat.Prime 2005739 := by norm_num

private theorem prime_oneHundredTwentyOneDO_2062873 : Nat.Prime 2062873 := by norm_num

private theorem prime_oneHundredTwentyOneDO_2069923 : Nat.Prime 2069923 := by norm_num

private theorem prime_oneHundredTwentyOneDO_2130703 : Nat.Prime 2130703 := by norm_num

private theorem prime_oneHundredTwentyOneDO_2174701 : Nat.Prime 2174701 := by norm_num

private theorem prime_oneHundredTwentyOneDO_2186603 : Nat.Prime 2186603 := by norm_num

private theorem prime_oneHundredTwentyOneDO_2230301 : Nat.Prime 2230301 := by norm_num

private theorem prime_oneHundredTwentyOneDO_2354591 : Nat.Prime 2354591 := by norm_num

private theorem prime_oneHundredTwentyOneDO_2433443 : Nat.Prime 2433443 := by norm_num

private theorem prime_oneHundredTwentyOneDO_2460299 : Nat.Prime 2460299 := by norm_num

private theorem prime_oneHundredTwentyOneDO_2491711 : Nat.Prime 2491711 := by norm_num

private theorem prime_oneHundredTwentyOneDO_2499053 : Nat.Prime 2499053 := by norm_num

private theorem prime_oneHundredTwentyOneDO_2530961 : Nat.Prime 2530961 := by norm_num

private theorem prime_oneHundredTwentyOneDO_2644913 : Nat.Prime 2644913 := by norm_num

private theorem prime_oneHundredTwentyOneDO_2650537 : Nat.Prime 2650537 := by norm_num

private theorem prime_oneHundredTwentyOneDO_3165203 : Nat.Prime 3165203 := by norm_num

private theorem prime_oneHundredTwentyOneDO_3283807 : Nat.Prime 3283807 := by norm_num

private theorem prime_oneHundredTwentyOneDO_3663833 : Nat.Prime 3663833 := by norm_num

private theorem prime_oneHundredTwentyOneDO_3700691 : Nat.Prime 3700691 := by norm_num

private theorem prime_oneHundredTwentyOneDO_3755359 : Nat.Prime 3755359 := by norm_num

private theorem prime_oneHundredTwentyOneDO_3813499 : Nat.Prime 3813499 := by norm_num

private theorem prime_oneHundredTwentyOneDO_4351489 : Nat.Prime 4351489 := by norm_num

private theorem prime_oneHundredTwentyOneDO_4362719 : Nat.Prime 4362719 := by norm_num

private theorem prime_oneHundredTwentyOneDO_4598983 : Nat.Prime 4598983 := by norm_num

private theorem prime_oneHundredTwentyOneDO_4654597 : Nat.Prime 4654597 := by norm_num

private theorem prime_oneHundredTwentyOneDO_4674077 : Nat.Prime 4674077 := by norm_num

private theorem prime_oneHundredTwentyOneDO_4861403 : Nat.Prime 4861403 := by norm_num

private theorem prime_oneHundredTwentyOneDO_5559209 : Nat.Prime 5559209 := by norm_num

private theorem prime_oneHundredTwentyOneDO_5750117 : Nat.Prime 5750117 := by norm_num

private theorem prime_oneHundredTwentyOneDO_6146053 : Nat.Prime 6146053 := by norm_num

private theorem prime_oneHundredTwentyOneDO_6466301 : Nat.Prime 6466301 := by norm_num

private theorem prime_oneHundredTwentyOneDO_7066487 : Nat.Prime 7066487 := by norm_num

private theorem prime_oneHundredTwentyOneDO_7528211 : Nat.Prime 7528211 := by norm_num

private theorem prime_oneHundredTwentyOneDO_7654121 : Nat.Prime 7654121 := by norm_num

private theorem prime_oneHundredTwentyOneDO_7895033 : Nat.Prime 7895033 := by norm_num

private theorem prime_oneHundredTwentyOneDO_8348687 : Nat.Prime 8348687 := by norm_num

private theorem prime_oneHundredTwentyOneDO_8837987 : Nat.Prime 8837987 := by norm_num

private theorem prime_oneHundredTwentyOneDO_8912927 : Nat.Prime 8912927 := by norm_num

private theorem prime_oneHundredTwentyOneDO_9147587 : Nat.Prime 9147587 := by norm_num

private theorem prime_oneHundredTwentyOneDO_9576443 : Nat.Prime 9576443 := by norm_num

private theorem prime_oneHundredTwentyOneDO_9796411 : Nat.Prime 9796411 := by norm_num

private theorem prime_oneHundredTwentyOneDO_10096081 : Nat.Prime 10096081 := by norm_num

private theorem prime_oneHundredTwentyOneDO_10655867 : Nat.Prime 10655867 := by norm_num

private theorem prime_oneHundredTwentyOneDO_10705951 : Nat.Prime 10705951 := by norm_num

private theorem prime_oneHundredTwentyOneDO_10820141 : Nat.Prime 10820141 := by norm_num

private theorem prime_oneHundredTwentyOneDO_10909627 : Nat.Prime 10909627 := by norm_num

private theorem prime_oneHundredTwentyOneDO_11517307 : Nat.Prime 11517307 := by norm_num

private theorem prime_oneHundredTwentyOneDO_11598157 : Nat.Prime 11598157 := by norm_num

private theorem prime_oneHundredTwentyOneDO_12087409 : Nat.Prime 12087409 := by norm_num

private theorem prime_oneHundredTwentyOneDO_12574993 : Nat.Prime 12574993 := by norm_num

private theorem prime_oneHundredTwentyOneDO_12767203 : Nat.Prime 12767203 := by norm_num

private theorem prime_oneHundredTwentyOneDO_13314571 : Nat.Prime 13314571 := by norm_num

private theorem prime_oneHundredTwentyOneDO_13629871 : Nat.Prime 13629871 := by norm_num

private theorem prime_oneHundredTwentyOneDO_13975901 : Nat.Prime 13975901 := by norm_num

private theorem prime_oneHundredTwentyOneDO_15159499 : Nat.Prime 15159499 := by norm_num

private theorem prime_oneHundredTwentyOneDO_15609343 : Nat.Prime 15609343 := by norm_num

private theorem prime_oneHundredTwentyOneDO_15627853 : Nat.Prime 15627853 := by norm_num

private theorem prime_oneHundredTwentyOneDO_16145813 : Nat.Prime 16145813 := by norm_num

private theorem prime_oneHundredTwentyOneDO_16818413 : Nat.Prime 16818413 := by norm_num

private theorem prime_oneHundredTwentyOneDO_19150853 : Nat.Prime 19150853 := by norm_num

private theorem prime_oneHundredTwentyOneDO_19976597 : Nat.Prime 19976597 := by norm_num

private theorem prime_oneHundredTwentyOneDO_20697877 : Nat.Prime 20697877 := by norm_num

private theorem prime_oneHundredTwentyOneDO_21546079 : Nat.Prime 21546079 := by norm_num

private theorem prime_oneHundredTwentyOneDO_22415483 : Nat.Prime 22415483 := by norm_num

private theorem prime_oneHundredTwentyOneDO_23118001 : Nat.Prime 23118001 := by norm_num

private theorem prime_oneHundredTwentyOneDO_23490877 : Nat.Prime 23490877 := by norm_num

private theorem prime_oneHundredTwentyOneDO_24628493 : Nat.Prime 24628493 := by norm_num

private theorem prime_oneHundredTwentyOneDO_25381789 : Nat.Prime 25381789 := by norm_num

private theorem prime_oneHundredTwentyOneDO_27241681 : Nat.Prime 27241681 := by norm_num

private theorem prime_oneHundredTwentyOneDO_27529609 : Nat.Prime 27529609 := by norm_num

private theorem prime_oneHundredTwentyOneDO_27597463 : Nat.Prime 27597463 := by norm_num

private theorem prime_oneHundredTwentyOneDO_28080931 : Nat.Prime 28080931 := by norm_num

private theorem prime_oneHundredTwentyOneDO_30612443 : Nat.Prime 30612443 := by
  apply lucas_primality 30612443 (2 : ZMod 30612443)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (2186603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (2186603, 1)] : List FactorBlock).map factorBlockValue).prod) = 30612443 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_7
      · exact prime_oneHundredTwentyOneDO_2186603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 30612443) ^ 15306221 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 30612443) ^ 4373206 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 30612443) ^ 14 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_31277291 : Nat.Prime 31277291 := by
  apply lucas_primality 31277291 (2 : ZMod 31277291)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 2), (25849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 2), (25849, 1)] : List FactorBlock).map factorBlockValue).prod) = 31277291 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_5
      · exact prime_oneHundredTwentyOneDO_11
      · exact prime_oneHundredTwentyOneDO_25849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 31277291) ^ 15638645 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 31277291) ^ 6255458 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 31277291) ^ 2843390 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 31277291) ^ 1210 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_32291627 : Nat.Prime 32291627 := by
  apply lucas_primality 32291627 (2 : ZMod 32291627)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (16145813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (16145813, 1)] : List FactorBlock).map factorBlockValue).prod) = 32291627 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_16145813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 32291627) ^ 16145813 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 32291627) ^ 2 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_33679313 : Nat.Prime 33679313 := by
  apply lucas_primality 33679313 (3 : ZMod 33679313)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (17, 1), (123821, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (17, 1), (123821, 1)] : List FactorBlock).map factorBlockValue).prod) = 33679313 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_17
      · exact prime_oneHundredTwentyOneDO_123821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 33679313) ^ 16839656 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 33679313) ^ 1981136 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 33679313) ^ 272 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_37392617 : Nat.Prime 37392617 := by
  apply lucas_primality 37392617 (3 : ZMod 37392617)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (4674077, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (4674077, 1)] : List FactorBlock).map factorBlockValue).prod) = 37392617 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_4674077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 37392617) ^ 18696308 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 37392617) ^ 8 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_38633759 : Nat.Prime 38633759 := by
  apply lucas_primality 38633759 (13 : ZMod 38633759)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (1136287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (1136287, 1)] : List FactorBlock).map factorBlockValue).prod) = 38633759 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_17
      · exact prime_oneHundredTwentyOneDO_1136287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 38633759) ^ 19316879 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (13 : ZMod 38633759) ^ 2272574 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (13 : ZMod 38633759) ^ 34 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_38712257 : Nat.Prime 38712257 := by
  apply lucas_primality 38712257 (3 : ZMod 38712257)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (11, 2), (4999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (11, 2), (4999, 1)] : List FactorBlock).map factorBlockValue).prod) = 38712257 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_11
      · exact prime_oneHundredTwentyOneDO_4999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 38712257) ^ 19356128 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 38712257) ^ 3519296 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 38712257) ^ 7744 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_40170791 : Nat.Prime 40170791 := by
  apply lucas_primality 40170791 (11 : ZMod 40170791)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 2), (33199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 2), (33199, 1)] : List FactorBlock).map factorBlockValue).prod) = 40170791 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_5
      · exact prime_oneHundredTwentyOneDO_11
      · exact prime_oneHundredTwentyOneDO_33199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 40170791) ^ 20085395 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (11 : ZMod 40170791) ^ 8034158 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (11 : ZMod 40170791) ^ 3651890 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (11 : ZMod 40170791) ^ 1210 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_43001837 : Nat.Prime 43001837 := by
  apply lucas_primality 43001837 (2 : ZMod 43001837)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (31, 1), (239, 1), (1451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (31, 1), (239, 1), (1451, 1)] : List FactorBlock).map factorBlockValue).prod) = 43001837 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_31
      · exact prime_oneHundredTwentyOneDO_239
      · exact prime_oneHundredTwentyOneDO_1451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 43001837) ^ 21500918 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 43001837) ^ 1387156 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 43001837) ^ 179924 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 43001837) ^ 29636 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_44296561 : Nat.Prime 44296561 := by
  apply lucas_primality 44296561 (37 : ZMod 44296561)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5, 1), (7, 1), (11, 1), (17, 1), (47, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5, 1), (7, 1), (11, 1), (17, 1), (47, 1)] : List FactorBlock).map factorBlockValue).prod) = 44296561 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_5
      · exact prime_oneHundredTwentyOneDO_7
      · exact prime_oneHundredTwentyOneDO_11
      · exact prime_oneHundredTwentyOneDO_17
      · exact prime_oneHundredTwentyOneDO_47
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (37 : ZMod 44296561) ^ 22148280 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (37 : ZMod 44296561) ^ 14765520 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (37 : ZMod 44296561) ^ 8859312 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (37 : ZMod 44296561) ^ 6328080 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (37 : ZMod 44296561) ^ 4026960 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (37 : ZMod 44296561) ^ 2605680 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (37 : ZMod 44296561) ^ 942480 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_47197243 : Nat.Prime 47197243 := by
  apply lucas_primality 47197243 (2 : ZMod 47197243)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (23, 1), (53, 1), (239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (23, 1), (53, 1), (239, 1)] : List FactorBlock).map factorBlockValue).prod) = 47197243 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_23
      · exact prime_oneHundredTwentyOneDO_53
      · exact prime_oneHundredTwentyOneDO_239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 47197243) ^ 23598621 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 47197243) ^ 15732414 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 47197243) ^ 2052054 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 47197243) ^ 890514 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 47197243) ^ 197478 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_48834113 : Nat.Prime 48834113 := by
  apply lucas_primality 48834113 (3 : ZMod 48834113)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (257, 1), (2969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (257, 1), (2969, 1)] : List FactorBlock).map factorBlockValue).prod) = 48834113 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_257
      · exact prime_oneHundredTwentyOneDO_2969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 48834113) ^ 24417056 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 48834113) ^ 190016 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 48834113) ^ 16448 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_49471423 : Nat.Prime 49471423 := by
  apply lucas_primality 49471423 (3 : ZMod 49471423)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (11, 1), (13, 1), (8237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (11, 1), (13, 1), (8237, 1)] : List FactorBlock).map factorBlockValue).prod) = 49471423 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_7
      · exact prime_oneHundredTwentyOneDO_11
      · exact prime_oneHundredTwentyOneDO_13
      · exact prime_oneHundredTwentyOneDO_8237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 49471423) ^ 24735711 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 49471423) ^ 16490474 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 49471423) ^ 7067346 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 49471423) ^ 4497402 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 49471423) ^ 3805494 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 49471423) ^ 6006 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_51068813 : Nat.Prime 51068813 := by
  apply lucas_primality 51068813 (2 : ZMod 51068813)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (12767203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (12767203, 1)] : List FactorBlock).map factorBlockValue).prod) = 51068813 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_12767203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 51068813) ^ 25534406 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 51068813) ^ 4 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_55987651 : Nat.Prime 55987651 := by
  apply lucas_primality 55987651 (2 : ZMod 55987651)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (83, 1), (1499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (83, 1), (1499, 1)] : List FactorBlock).map factorBlockValue).prod) = 55987651 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_5
      · exact prime_oneHundredTwentyOneDO_83
      · exact prime_oneHundredTwentyOneDO_1499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 55987651) ^ 27993825 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 55987651) ^ 18662550 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 55987651) ^ 11197530 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 55987651) ^ 674550 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 55987651) ^ 37350 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_59401873 : Nat.Prime 59401873 := by
  apply lucas_primality 59401873 (7 : ZMod 59401873)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (37, 1), (11149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (37, 1), (11149, 1)] : List FactorBlock).map factorBlockValue).prod) = 59401873 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_37
      · exact prime_oneHundredTwentyOneDO_11149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 59401873) ^ 29700936 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (7 : ZMod 59401873) ^ 19800624 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (7 : ZMod 59401873) ^ 1605456 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (7 : ZMod 59401873) ^ 5328 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_65296087 : Nat.Prime 65296087 := by
  apply lucas_primality 65296087 (3 : ZMod 65296087)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1459, 1), (7459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1459, 1), (7459, 1)] : List FactorBlock).map factorBlockValue).prod) = 65296087 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_1459
      · exact prime_oneHundredTwentyOneDO_7459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 65296087) ^ 32648043 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 65296087) ^ 21765362 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 65296087) ^ 44754 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 65296087) ^ 8754 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_68767739 : Nat.Prime 68767739 := by
  apply lucas_primality 68767739 (2 : ZMod 68767739)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (2644913, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (2644913, 1)] : List FactorBlock).map factorBlockValue).prod) = 68767739 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_13
      · exact prime_oneHundredTwentyOneDO_2644913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 68767739) ^ 34383869 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 68767739) ^ 5289826 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 68767739) ^ 26 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_73180697 : Nat.Prime 73180697 := by
  apply lucas_primality 73180697 (3 : ZMod 73180697)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (9147587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (9147587, 1)] : List FactorBlock).map factorBlockValue).prod) = 73180697 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_9147587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 73180697) ^ 36590348 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 73180697) ^ 8 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_74320801 : Nat.Prime 74320801 := by
  apply lucas_primality 74320801 (19 : ZMod 74320801)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 2), (173, 1), (179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 2), (173, 1), (179, 1)] : List FactorBlock).map factorBlockValue).prod) = 74320801 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_5
      · exact prime_oneHundredTwentyOneDO_173
      · exact prime_oneHundredTwentyOneDO_179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 74320801) ^ 37160400 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (19 : ZMod 74320801) ^ 24773600 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (19 : ZMod 74320801) ^ 14864160 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (19 : ZMod 74320801) ^ 429600 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (19 : ZMod 74320801) ^ 415200 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_77926439 : Nat.Prime 77926439 := by
  apply lucas_primality 77926439 (13 : ZMod 77926439)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (127, 1), (13339, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (127, 1), (13339, 1)] : List FactorBlock).map factorBlockValue).prod) = 77926439 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_23
      · exact prime_oneHundredTwentyOneDO_127
      · exact prime_oneHundredTwentyOneDO_13339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 77926439) ^ 38963219 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (13 : ZMod 77926439) ^ 3388106 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (13 : ZMod 77926439) ^ 613594 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (13 : ZMod 77926439) ^ 5842 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_81603971 : Nat.Prime 81603971 := by
  apply lucas_primality 81603971 (2 : ZMod 81603971)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (29, 1), (61, 1), (659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (29, 1), (61, 1), (659, 1)] : List FactorBlock).map factorBlockValue).prod) = 81603971 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_5
      · exact prime_oneHundredTwentyOneDO_7
      · exact prime_oneHundredTwentyOneDO_29
      · exact prime_oneHundredTwentyOneDO_61
      · exact prime_oneHundredTwentyOneDO_659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 81603971) ^ 40801985 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 81603971) ^ 16320794 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 81603971) ^ 11657710 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 81603971) ^ 2813930 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 81603971) ^ 1337770 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 81603971) ^ 123830 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_91288129 : Nat.Prime 91288129 := by
  apply lucas_primality 91288129 (31 : ZMod 91288129)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (149, 1), (3191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (149, 1), (3191, 1)] : List FactorBlock).map factorBlockValue).prod) = 91288129 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_149
      · exact prime_oneHundredTwentyOneDO_3191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (31 : ZMod 91288129) ^ 45644064 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (31 : ZMod 91288129) ^ 30429376 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (31 : ZMod 91288129) ^ 612672 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (31 : ZMod 91288129) ^ 28608 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_99765313 : Nat.Prime 99765313 := by
  apply lucas_primality 99765313 (5 : ZMod 99765313)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (519611, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (519611, 1)] : List FactorBlock).map factorBlockValue).prod) = 99765313 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_519611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 99765313) ^ 49882656 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 99765313) ^ 33255104 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 99765313) ^ 192 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_104132681 : Nat.Prime 104132681 := by
  apply lucas_primality 104132681 (3 : ZMod 104132681)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (283, 1), (9199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (283, 1), (9199, 1)] : List FactorBlock).map factorBlockValue).prod) = 104132681 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_5
      · exact prime_oneHundredTwentyOneDO_283
      · exact prime_oneHundredTwentyOneDO_9199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 104132681) ^ 52066340 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 104132681) ^ 20826536 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 104132681) ^ 367960 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 104132681) ^ 11320 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_106021481 : Nat.Prime 106021481 := by
  apply lucas_primality 106021481 (6 : ZMod 106021481)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (2650537, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (2650537, 1)] : List FactorBlock).map factorBlockValue).prod) = 106021481 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_5
      · exact prime_oneHundredTwentyOneDO_2650537
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 106021481) ^ 53010740 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (6 : ZMod 106021481) ^ 21204296 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (6 : ZMod 106021481) ^ 40 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_106920559 : Nat.Prime 106920559 := by
  apply lucas_primality 106920559 (3 : ZMod 106920559)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (229, 1), (25939, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (229, 1), (25939, 1)] : List FactorBlock).map factorBlockValue).prod) = 106920559 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_229
      · exact prime_oneHundredTwentyOneDO_25939
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 106920559) ^ 53460279 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 106920559) ^ 35640186 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 106920559) ^ 466902 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 106920559) ^ 4122 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_109022593 : Nat.Prime 109022593 := by
  apply lucas_primality 109022593 (5 : ZMod 109022593)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (7, 1), (40559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (7, 1), (40559, 1)] : List FactorBlock).map factorBlockValue).prod) = 109022593 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_7
      · exact prime_oneHundredTwentyOneDO_40559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 109022593) ^ 54511296 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 109022593) ^ 36340864 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 109022593) ^ 15574656 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 109022593) ^ 2688 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_113902927 : Nat.Prime 113902927 := by
  apply lucas_primality 113902927 (3 : ZMod 113902927)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (271, 1), (70051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (271, 1), (70051, 1)] : List FactorBlock).map factorBlockValue).prod) = 113902927 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_271
      · exact prime_oneHundredTwentyOneDO_70051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 113902927) ^ 56951463 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 113902927) ^ 37967642 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 113902927) ^ 420306 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 113902927) ^ 1626 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_140945263 : Nat.Prime 140945263 := by
  apply lucas_primality 140945263 (3 : ZMod 140945263)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23490877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23490877, 1)] : List FactorBlock).map factorBlockValue).prod) = 140945263 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_23490877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 140945263) ^ 70472631 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 140945263) ^ 46981754 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 140945263) ^ 6 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_161760701 : Nat.Prime 161760701 := by
  apply lucas_primality 161760701 (2 : ZMod 161760701)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (73, 1), (22159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (73, 1), (22159, 1)] : List FactorBlock).map factorBlockValue).prod) = 161760701 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_5
      · exact prime_oneHundredTwentyOneDO_73
      · exact prime_oneHundredTwentyOneDO_22159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 161760701) ^ 80880350 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 161760701) ^ 32352140 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 161760701) ^ 2215900 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 161760701) ^ 7300 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_163207943 : Nat.Prime 163207943 := by
  apply lucas_primality 163207943 (5 : ZMod 163207943)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (81603971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (81603971, 1)] : List FactorBlock).map factorBlockValue).prod) = 163207943 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_81603971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 163207943) ^ 81603971 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 163207943) ^ 2 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_167710813 : Nat.Prime 167710813 := by
  apply lucas_primality 167710813 (2 : ZMod 167710813)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13975901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13975901, 1)] : List FactorBlock).map factorBlockValue).prod) = 167710813 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_13975901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 167710813) ^ 83855406 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 167710813) ^ 55903604 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 167710813) ^ 12 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_179593991 : Nat.Prime 179593991 := by
  apply lucas_primality 179593991 (11 : ZMod 179593991)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (89, 1), (201791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (89, 1), (201791, 1)] : List FactorBlock).map factorBlockValue).prod) = 179593991 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_5
      · exact prime_oneHundredTwentyOneDO_89
      · exact prime_oneHundredTwentyOneDO_201791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 179593991) ^ 89796995 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (11 : ZMod 179593991) ^ 35918798 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (11 : ZMod 179593991) ^ 2017910 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (11 : ZMod 179593991) ^ 890 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_179964529 : Nat.Prime 179964529 := by
  apply lucas_primality 179964529 (7 : ZMod 179964529)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (79, 1), (47459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (79, 1), (47459, 1)] : List FactorBlock).map factorBlockValue).prod) = 179964529 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_79
      · exact prime_oneHundredTwentyOneDO_47459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 179964529) ^ 89982264 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (7 : ZMod 179964529) ^ 59988176 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (7 : ZMod 179964529) ^ 2278032 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (7 : ZMod 179964529) ^ 3792 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_181839001 : Nat.Prime 181839001 := by
  apply lucas_primality 181839001 (13 : ZMod 181839001)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 3), (7, 2), (1237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 3), (7, 2), (1237, 1)] : List FactorBlock).map factorBlockValue).prod) = 181839001 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_5
      · exact prime_oneHundredTwentyOneDO_7
      · exact prime_oneHundredTwentyOneDO_1237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 181839001) ^ 90919500 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (13 : ZMod 181839001) ^ 60613000 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (13 : ZMod 181839001) ^ 36367800 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (13 : ZMod 181839001) ^ 25977000 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (13 : ZMod 181839001) ^ 147000 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_185567273 : Nat.Prime 185567273 := by
  apply lucas_primality 185567273 (3 : ZMod 185567273)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (59, 1), (103, 1), (347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (59, 1), (103, 1), (347, 1)] : List FactorBlock).map factorBlockValue).prod) = 185567273 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_11
      · exact prime_oneHundredTwentyOneDO_59
      · exact prime_oneHundredTwentyOneDO_103
      · exact prime_oneHundredTwentyOneDO_347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 185567273) ^ 92783636 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 185567273) ^ 16869752 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 185567273) ^ 3145208 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 185567273) ^ 1801624 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 185567273) ^ 534776 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_188620591 : Nat.Prime 188620591 := by
  apply lucas_primality 188620591 (6 : ZMod 188620591)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (149, 1), (42197, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (149, 1), (42197, 1)] : List FactorBlock).map factorBlockValue).prod) = 188620591 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_5
      · exact prime_oneHundredTwentyOneDO_149
      · exact prime_oneHundredTwentyOneDO_42197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 188620591) ^ 94310295 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (6 : ZMod 188620591) ^ 62873530 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (6 : ZMod 188620591) ^ 37724118 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (6 : ZMod 188620591) ^ 1265910 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (6 : ZMod 188620591) ^ 4470 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_192542521 : Nat.Prime 192542521 := by
  apply lucas_primality 192542521 (13 : ZMod 192542521)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (1604521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (1604521, 1)] : List FactorBlock).map factorBlockValue).prod) = 192542521 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_5
      · exact prime_oneHundredTwentyOneDO_1604521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 192542521) ^ 96271260 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (13 : ZMod 192542521) ^ 64180840 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (13 : ZMod 192542521) ^ 38508504 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (13 : ZMod 192542521) ^ 120 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_200272519 : Nat.Prime 200272519 := by
  apply lucas_primality 200272519 (15 : ZMod 200272519)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (181, 1), (61471, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (181, 1), (61471, 1)] : List FactorBlock).map factorBlockValue).prod) = 200272519 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_181
      · exact prime_oneHundredTwentyOneDO_61471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (15 : ZMod 200272519) ^ 100136259 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (15 : ZMod 200272519) ^ 66757506 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (15 : ZMod 200272519) ^ 1106478 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (15 : ZMod 200272519) ^ 3258 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_216539023 : Nat.Prime 216539023 := by
  apply lucas_primality 216539023 (12 : ZMod 216539023)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (37, 1), (139343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (37, 1), (139343, 1)] : List FactorBlock).map factorBlockValue).prod) = 216539023 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_7
      · exact prime_oneHundredTwentyOneDO_37
      · exact prime_oneHundredTwentyOneDO_139343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (12 : ZMod 216539023) ^ 108269511 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (12 : ZMod 216539023) ^ 72179674 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (12 : ZMod 216539023) ^ 30934146 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (12 : ZMod 216539023) ^ 5852406 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (12 : ZMod 216539023) ^ 1554 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_256466803 : Nat.Prime 256466803 := by
  apply lucas_primality 256466803 (2 : ZMod 256466803)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (107, 1), (399481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (107, 1), (399481, 1)] : List FactorBlock).map factorBlockValue).prod) = 256466803 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_107
      · exact prime_oneHundredTwentyOneDO_399481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 256466803) ^ 128233401 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 256466803) ^ 85488934 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 256466803) ^ 2396886 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 256466803) ^ 642 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_277412503 : Nat.Prime 277412503 := by
  apply lucas_primality 277412503 (3 : ZMod 277412503)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (2433443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (2433443, 1)] : List FactorBlock).map factorBlockValue).prod) = 277412503 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_19
      · exact prime_oneHundredTwentyOneDO_2433443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 277412503) ^ 138706251 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 277412503) ^ 92470834 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 277412503) ^ 14600658 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 277412503) ^ 114 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_281675497 : Nat.Prime 281675497 := by
  apply lucas_primality 281675497 (5 : ZMod 281675497)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (53, 1), (229, 1), (967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (53, 1), (229, 1), (967, 1)] : List FactorBlock).map factorBlockValue).prod) = 281675497 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_53
      · exact prime_oneHundredTwentyOneDO_229
      · exact prime_oneHundredTwentyOneDO_967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 281675497) ^ 140837748 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 281675497) ^ 93891832 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 281675497) ^ 5314632 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 281675497) ^ 1230024 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 281675497) ^ 291288 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_290442961 : Nat.Prime 290442961 := by
  apply lucas_primality 290442961 (11 : ZMod 290442961)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5, 1), (17, 1), (61, 1), (389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5, 1), (17, 1), (61, 1), (389, 1)] : List FactorBlock).map factorBlockValue).prod) = 290442961 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_5
      · exact prime_oneHundredTwentyOneDO_17
      · exact prime_oneHundredTwentyOneDO_61
      · exact prime_oneHundredTwentyOneDO_389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 290442961) ^ 145221480 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (11 : ZMod 290442961) ^ 96814320 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (11 : ZMod 290442961) ^ 58088592 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (11 : ZMod 290442961) ^ 17084880 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (11 : ZMod 290442961) ^ 4761360 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (11 : ZMod 290442961) ^ 746640 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_304338497 : Nat.Prime 304338497 := by
  apply lucas_primality 304338497 (5 : ZMod 304338497)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (7, 1), (11, 1), (61757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (7, 1), (11, 1), (61757, 1)] : List FactorBlock).map factorBlockValue).prod) = 304338497 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_7
      · exact prime_oneHundredTwentyOneDO_11
      · exact prime_oneHundredTwentyOneDO_61757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 304338497) ^ 152169248 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 304338497) ^ 43476928 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 304338497) ^ 27667136 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 304338497) ^ 4928 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_315417211 : Nat.Prime 315417211 := by
  apply lucas_primality 315417211 (3 : ZMod 315417211)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (1303, 1), (8069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (1303, 1), (8069, 1)] : List FactorBlock).map factorBlockValue).prod) = 315417211 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_5
      · exact prime_oneHundredTwentyOneDO_1303
      · exact prime_oneHundredTwentyOneDO_8069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 315417211) ^ 157708605 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 315417211) ^ 105139070 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 315417211) ^ 63083442 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 315417211) ^ 242070 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 315417211) ^ 39090 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_323977837 : Nat.Prime 323977837 := by
  apply lucas_primality 323977837 (6 : ZMod 323977837)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (13, 1), (296683, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (13, 1), (296683, 1)] : List FactorBlock).map factorBlockValue).prod) = 323977837 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_7
      · exact prime_oneHundredTwentyOneDO_13
      · exact prime_oneHundredTwentyOneDO_296683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 323977837) ^ 161988918 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (6 : ZMod 323977837) ^ 107992612 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (6 : ZMod 323977837) ^ 46282548 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (6 : ZMod 323977837) ^ 24921372 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (6 : ZMod 323977837) ^ 1092 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_332210939 : Nat.Prime 332210939 := by
  apply lucas_primality 332210939 (2 : ZMod 332210939)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (1021, 1), (4397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (1021, 1), (4397, 1)] : List FactorBlock).map factorBlockValue).prod) = 332210939 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_37
      · exact prime_oneHundredTwentyOneDO_1021
      · exact prime_oneHundredTwentyOneDO_4397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 332210939) ^ 166105469 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 332210939) ^ 8978674 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 332210939) ^ 325378 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 332210939) ^ 75554 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_339648767 : Nat.Prime 339648767 := by
  apply lucas_primality 339648767 (5 : ZMod 339648767)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (587, 1), (289309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (587, 1), (289309, 1)] : List FactorBlock).map factorBlockValue).prod) = 339648767 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_587
      · exact prime_oneHundredTwentyOneDO_289309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 339648767) ^ 169824383 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 339648767) ^ 578618 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 339648767) ^ 1174 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_358439597 : Nat.Prime 358439597 := by
  apply lucas_primality 358439597 (2 : ZMod 358439597)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (199, 1), (450301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (199, 1), (450301, 1)] : List FactorBlock).map factorBlockValue).prod) = 358439597 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_199
      · exact prime_oneHundredTwentyOneDO_450301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 358439597) ^ 179219798 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 358439597) ^ 1801204 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 358439597) ^ 796 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_375327493 : Nat.Prime 375327493 := by
  apply lucas_primality 375327493 (5 : ZMod 375327493)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (31277291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (31277291, 1)] : List FactorBlock).map factorBlockValue).prod) = 375327493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_31277291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 375327493) ^ 187663746 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 375327493) ^ 125109164 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 375327493) ^ 12 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_387829423 : Nat.Prime 387829423 := by
  apply lucas_primality 387829423 (3 : ZMod 387829423)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (21546079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (21546079, 1)] : List FactorBlock).map factorBlockValue).prod) = 387829423 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_21546079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 387829423) ^ 193914711 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 387829423) ^ 129276474 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 387829423) ^ 18 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_397661741 : Nat.Prime 397661741 := by
  apply lucas_primality 397661741 (2 : ZMod 397661741)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (503, 1), (5647, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (503, 1), (5647, 1)] : List FactorBlock).map factorBlockValue).prod) = 397661741 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_5
      · exact prime_oneHundredTwentyOneDO_7
      · exact prime_oneHundredTwentyOneDO_503
      · exact prime_oneHundredTwentyOneDO_5647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 397661741) ^ 198830870 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 397661741) ^ 79532348 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 397661741) ^ 56808820 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 397661741) ^ 790580 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 397661741) ^ 70420 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_431003641 : Nat.Prime 431003641 := by
  apply lucas_primality 431003641 (7 : ZMod 431003641)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (467, 1), (7691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (467, 1), (7691, 1)] : List FactorBlock).map factorBlockValue).prod) = 431003641 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_5
      · exact prime_oneHundredTwentyOneDO_467
      · exact prime_oneHundredTwentyOneDO_7691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 431003641) ^ 215501820 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (7 : ZMod 431003641) ^ 143667880 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (7 : ZMod 431003641) ^ 86200728 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (7 : ZMod 431003641) ^ 922920 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (7 : ZMod 431003641) ^ 56040 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_441559409 : Nat.Prime 441559409 := by
  apply lucas_primality 441559409 (3 : ZMod 441559409)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (27597463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (27597463, 1)] : List FactorBlock).map factorBlockValue).prod) = 441559409 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_27597463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 441559409) ^ 220779704 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 441559409) ^ 16 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_467148029 : Nat.Prime 467148029 := by
  apply lucas_primality 467148029 (2 : ZMod 467148029)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (101, 1), (1156307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (101, 1), (1156307, 1)] : List FactorBlock).map factorBlockValue).prod) = 467148029 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_101
      · exact prime_oneHundredTwentyOneDO_1156307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 467148029) ^ 233574014 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 467148029) ^ 4625228 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 467148029) ^ 404 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_482049493 : Nat.Prime 482049493 := by
  apply lucas_primality 482049493 (5 : ZMod 482049493)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (40170791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (40170791, 1)] : List FactorBlock).map factorBlockValue).prod) = 482049493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_40170791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 482049493) ^ 241024746 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 482049493) ^ 160683164 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 482049493) ^ 12 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_526042799 : Nat.Prime 526042799 := by
  apply lucas_primality 526042799 (7 : ZMod 526042799)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (23, 1), (113, 1), (5953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (23, 1), (113, 1), (5953, 1)] : List FactorBlock).map factorBlockValue).prod) = 526042799 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_17
      · exact prime_oneHundredTwentyOneDO_23
      · exact prime_oneHundredTwentyOneDO_113
      · exact prime_oneHundredTwentyOneDO_5953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 526042799) ^ 263021399 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (7 : ZMod 526042799) ^ 30943694 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (7 : ZMod 526042799) ^ 22871426 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (7 : ZMod 526042799) ^ 4655246 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (7 : ZMod 526042799) ^ 88366 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_585445577 : Nat.Prime 585445577 := by
  apply lucas_primality 585445577 (3 : ZMod 585445577)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (73180697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (73180697, 1)] : List FactorBlock).map factorBlockValue).prod) = 585445577 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_73180697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 585445577) ^ 292722788 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 585445577) ^ 8 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_602914999 : Nat.Prime 602914999 := by
  apply lucas_primality 602914999 (3 : ZMod 602914999)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (313, 1), (45863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (313, 1), (45863, 1)] : List FactorBlock).map factorBlockValue).prod) = 602914999 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_7
      · exact prime_oneHundredTwentyOneDO_313
      · exact prime_oneHundredTwentyOneDO_45863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 602914999) ^ 301457499 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 602914999) ^ 200971666 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 602914999) ^ 86130714 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 602914999) ^ 1926246 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 602914999) ^ 13146 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_620764897 : Nat.Prime 620764897 := by
  apply lucas_primality 620764897 (5 : ZMod 620764897)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (6466301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (6466301, 1)] : List FactorBlock).map factorBlockValue).prod) = 620764897 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_6466301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 620764897) ^ 310382448 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 620764897) ^ 206921632 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 620764897) ^ 96 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_654233809 : Nat.Prime 654233809 := by
  apply lucas_primality 654233809 (7 : ZMod 654233809)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (13629871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (13629871, 1)] : List FactorBlock).map factorBlockValue).prod) = 654233809 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_13629871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 654233809) ^ 327116904 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (7 : ZMod 654233809) ^ 218077936 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (7 : ZMod 654233809) ^ 48 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_670843253 : Nat.Prime 670843253 := by
  apply lucas_primality 670843253 (2 : ZMod 670843253)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (167710813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (167710813, 1)] : List FactorBlock).map factorBlockValue).prod) = 670843253 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_167710813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 670843253) ^ 335421626 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 670843253) ^ 4 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_672087701 : Nat.Prime 672087701 := by
  apply lucas_primality 672087701 (3 : ZMod 672087701)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (53, 1), (173, 1), (733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (53, 1), (173, 1), (733, 1)] : List FactorBlock).map factorBlockValue).prod) = 672087701 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_5
      · exact prime_oneHundredTwentyOneDO_53
      · exact prime_oneHundredTwentyOneDO_173
      · exact prime_oneHundredTwentyOneDO_733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 672087701) ^ 336043850 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 672087701) ^ 134417540 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 672087701) ^ 12680900 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 672087701) ^ 3884900 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 672087701) ^ 916900 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_714027719 : Nat.Prime 714027719 := by
  apply lucas_primality 714027719 (11 : ZMod 714027719)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) = 714027719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_17203
      · exact prime_oneHundredTwentyOneDO_20753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 714027719) ^ 357013859 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 41506 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 34406 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_735999331 : Nat.Prime 735999331 := by
  apply lucas_primality 735999331 (2 : ZMod 735999331)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (2230301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (2230301, 1)] : List FactorBlock).map factorBlockValue).prod) = 735999331 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_5
      · exact prime_oneHundredTwentyOneDO_11
      · exact prime_oneHundredTwentyOneDO_2230301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 735999331) ^ 367999665 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 735999331) ^ 245333110 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 735999331) ^ 147199866 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 735999331) ^ 66909030 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 735999331) ^ 330 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_861519343 : Nat.Prime 861519343 := by
  apply lucas_primality 861519343 (3 : ZMod 861519343)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (3049, 1), (47093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (3049, 1), (47093, 1)] : List FactorBlock).map factorBlockValue).prod) = 861519343 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_3049
      · exact prime_oneHundredTwentyOneDO_47093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 861519343) ^ 430759671 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 861519343) ^ 287173114 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 861519343) ^ 282558 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 861519343) ^ 18294 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_922676291 : Nat.Prime 922676291 := by
  apply lucas_primality 922676291 (2 : ZMod 922676291)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (19, 2), (255589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (19, 2), (255589, 1)] : List FactorBlock).map factorBlockValue).prod) = 922676291 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_5
      · exact prime_oneHundredTwentyOneDO_19
      · exact prime_oneHundredTwentyOneDO_255589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 922676291) ^ 461338145 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 922676291) ^ 184535258 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 922676291) ^ 48561910 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 922676291) ^ 3610 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_924758573 : Nat.Prime 924758573 := by
  apply lucas_primality 924758573 (2 : ZMod 924758573)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (199, 1), (1161757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (199, 1), (1161757, 1)] : List FactorBlock).map factorBlockValue).prod) = 924758573 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_199
      · exact prime_oneHundredTwentyOneDO_1161757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 924758573) ^ 462379286 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 924758573) ^ 4647028 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 924758573) ^ 796 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_926226547 : Nat.Prime 926226547 := by
  apply lucas_primality 926226547 (2 : ZMod 926226547)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (1657, 1), (13309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (1657, 1), (13309, 1)] : List FactorBlock).map factorBlockValue).prod) = 926226547 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_7
      · exact prime_oneHundredTwentyOneDO_1657
      · exact prime_oneHundredTwentyOneDO_13309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 926226547) ^ 463113273 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 926226547) ^ 308742182 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 926226547) ^ 132318078 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 926226547) ^ 558978 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 926226547) ^ 69594 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_934296059 : Nat.Prime 934296059 := by
  apply lucas_primality 934296059 (2 : ZMod 934296059)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (467148029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (467148029, 1)] : List FactorBlock).map factorBlockValue).prod) = 934296059 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_467148029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 934296059) ^ 467148029 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 934296059) ^ 2 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_1033899533 : Nat.Prime 1033899533 := by
  apply lucas_primality 1033899533 (2 : ZMod 1033899533)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 1), (8912927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 1), (8912927, 1)] : List FactorBlock).map factorBlockValue).prod) = 1033899533 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_29
      · exact prime_oneHundredTwentyOneDO_8912927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1033899533) ^ 516949766 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1033899533) ^ 35651708 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1033899533) ^ 116 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_1095457549 : Nat.Prime 1095457549 := by
  apply lucas_primality 1095457549 (2 : ZMod 1095457549)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (91288129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (91288129, 1)] : List FactorBlock).map factorBlockValue).prod) = 1095457549 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_91288129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1095457549) ^ 547728774 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1095457549) ^ 365152516 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1095457549) ^ 12 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_1225651513 : Nat.Prime 1225651513 := by
  apply lucas_primality 1225651513 (10 : ZMod 1225651513)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (51068813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (51068813, 1)] : List FactorBlock).map factorBlockValue).prod) = 1225651513 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_51068813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 1225651513) ^ 612825756 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (10 : ZMod 1225651513) ^ 408550504 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (10 : ZMod 1225651513) ^ 24 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_1387974373 : Nat.Prime 1387974373 := by
  apply lucas_primality 1387974373 (2 : ZMod 1387974373)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (419, 1), (276049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (419, 1), (276049, 1)] : List FactorBlock).map factorBlockValue).prod) = 1387974373 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_419
      · exact prime_oneHundredTwentyOneDO_276049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1387974373) ^ 693987186 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1387974373) ^ 462658124 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1387974373) ^ 3312588 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1387974373) ^ 5028 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_1498838717 : Nat.Prime 1498838717 := by
  apply lucas_primality 1498838717 (2 : ZMod 1498838717)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (31, 1), (12087409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (31, 1), (12087409, 1)] : List FactorBlock).map factorBlockValue).prod) = 1498838717 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_31
      · exact prime_oneHundredTwentyOneDO_12087409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1498838717) ^ 749419358 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1498838717) ^ 48349636 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1498838717) ^ 124 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_1502764099 : Nat.Prime 1502764099 := by
  apply lucas_primality 1502764099 (2 : ZMod 1502764099)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 2), (2069923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 2), (2069923, 1)] : List FactorBlock).map factorBlockValue).prod) = 1502764099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_11
      · exact prime_oneHundredTwentyOneDO_2069923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1502764099) ^ 751382049 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1502764099) ^ 500921366 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1502764099) ^ 136614918 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1502764099) ^ 726 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_1635057623 : Nat.Prime 1635057623 := by
  apply lucas_primality 1635057623 (5 : ZMod 1635057623)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (74320801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (74320801, 1)] : List FactorBlock).map factorBlockValue).prod) = 1635057623 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_11
      · exact prime_oneHundredTwentyOneDO_74320801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1635057623) ^ 817528811 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 1635057623) ^ 148641602 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 1635057623) ^ 22 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_1689911551 : Nat.Prime 1689911551 := by
  apply lucas_primality 1689911551 (6 : ZMod 1689911551)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (3755359, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (3755359, 1)] : List FactorBlock).map factorBlockValue).prod) = 1689911551 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_5
      · exact prime_oneHundredTwentyOneDO_3755359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 1689911551) ^ 844955775 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (6 : ZMod 1689911551) ^ 563303850 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (6 : ZMod 1689911551) ^ 337982310 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (6 : ZMod 1689911551) ^ 450 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_1753385299 : Nat.Prime 1753385299 := by
  apply lucas_primality 1753385299 (10 : ZMod 1753385299)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (29, 1), (1439561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (29, 1), (1439561, 1)] : List FactorBlock).map factorBlockValue).prod) = 1753385299 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_7
      · exact prime_oneHundredTwentyOneDO_29
      · exact prime_oneHundredTwentyOneDO_1439561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 1753385299) ^ 876692649 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (10 : ZMod 1753385299) ^ 584461766 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (10 : ZMod 1753385299) ^ 250483614 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (10 : ZMod 1753385299) ^ 60461562 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (10 : ZMod 1753385299) ^ 1218 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_1997185651 : Nat.Prime 1997185651 := by
  apply lucas_primality 1997185651 (3 : ZMod 1997185651)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (13314571, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (13314571, 1)] : List FactorBlock).map factorBlockValue).prod) = 1997185651 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_5
      · exact prime_oneHundredTwentyOneDO_13314571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1997185651) ^ 998592825 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1997185651) ^ 665728550 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1997185651) ^ 399437130 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1997185651) ^ 150 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_2358036103 : Nat.Prime 2358036103 := by
  apply lucas_primality 2358036103 (3 : ZMod 2358036103)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (23118001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (23118001, 1)] : List FactorBlock).map factorBlockValue).prod) = 2358036103 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_17
      · exact prime_oneHundredTwentyOneDO_23118001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2358036103) ^ 1179018051 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 2358036103) ^ 786012034 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 2358036103) ^ 138708006 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 2358036103) ^ 102 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_2378057809 : Nat.Prime 2378057809 := by
  apply lucas_primality 2378057809 (11 : ZMod 2378057809)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (7, 2), (1011079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (7, 2), (1011079, 1)] : List FactorBlock).map factorBlockValue).prod) = 2378057809 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_7
      · exact prime_oneHundredTwentyOneDO_1011079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 2378057809) ^ 1189028904 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (11 : ZMod 2378057809) ^ 792685936 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (11 : ZMod 2378057809) ^ 339722544 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (11 : ZMod 2378057809) ^ 2352 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_2513482381 : Nat.Prime 2513482381 := by
  apply lucas_primality 2513482381 (10 : ZMod 2513482381)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 1), (4654597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 1), (4654597, 1)] : List FactorBlock).map factorBlockValue).prod) = 2513482381 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_5
      · exact prime_oneHundredTwentyOneDO_4654597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 2513482381) ^ 1256741190 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (10 : ZMod 2513482381) ^ 837827460 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (10 : ZMod 2513482381) ^ 502696476 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (10 : ZMod 2513482381) ^ 540 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_2637042103 : Nat.Prime 2637042103 := by
  apply lucas_primality 2637042103 (3 : ZMod 2637042103)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (48834113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (48834113, 1)] : List FactorBlock).map factorBlockValue).prod) = 2637042103 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_48834113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2637042103) ^ 1318521051 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 2637042103) ^ 879014034 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 2637042103) ^ 54 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_2889582079 : Nat.Prime 2889582079 := by
  apply lucas_primality 2889582079 (3 : ZMod 2889582079)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (61, 1), (7895033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (61, 1), (7895033, 1)] : List FactorBlock).map factorBlockValue).prod) = 2889582079 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_61
      · exact prime_oneHundredTwentyOneDO_7895033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2889582079) ^ 1444791039 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 2889582079) ^ 963194026 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 2889582079) ^ 47370198 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 2889582079) ^ 366 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_3994688051 : Nat.Prime 3994688051 := by
  apply lucas_primality 3994688051 (2 : ZMod 3994688051)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (17, 2), (276449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (17, 2), (276449, 1)] : List FactorBlock).map factorBlockValue).prod) = 3994688051 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_5
      · exact prime_oneHundredTwentyOneDO_17
      · exact prime_oneHundredTwentyOneDO_276449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3994688051) ^ 1997344025 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 3994688051) ^ 798937610 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 3994688051) ^ 234981650 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 3994688051) ^ 14450 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_4223612929 : Nat.Prime 4223612929 := by
  apply lucas_primality 4223612929 (11 : ZMod 4223612929)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 11), (3, 1), (687437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 11), (3, 1), (687437, 1)] : List FactorBlock).map factorBlockValue).prod) = 4223612929 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_687437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 4223612929) ^ 2111806464 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (11 : ZMod 4223612929) ^ 1407870976 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (11 : ZMod 4223612929) ^ 6144 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_4235935463 : Nat.Prime 4235935463 := by
  apply lucas_primality 4235935463 (5 : ZMod 4235935463)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (192542521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (192542521, 1)] : List FactorBlock).map factorBlockValue).prod) = 4235935463 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_11
      · exact prime_oneHundredTwentyOneDO_192542521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 4235935463) ^ 2117967731 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 4235935463) ^ 385085042 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 4235935463) ^ 22 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_4914242863 : Nat.Prime 4914242863 := by
  apply lucas_primality 4914242863 (3 : ZMod 4914242863)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (41, 1), (19976597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (41, 1), (19976597, 1)] : List FactorBlock).map factorBlockValue).prod) = 4914242863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_41
      · exact prime_oneHundredTwentyOneDO_19976597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4914242863) ^ 2457121431 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 4914242863) ^ 1638080954 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 4914242863) ^ 119859582 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 4914242863) ^ 246 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_5151077749 : Nat.Prime 5151077749 := by
  apply lucas_primality 5151077749 (2 : ZMod 5151077749)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (2293, 1), (62401, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (2293, 1), (62401, 1)] : List FactorBlock).map factorBlockValue).prod) = 5151077749 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_2293
      · exact prime_oneHundredTwentyOneDO_62401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5151077749) ^ 2575538874 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 5151077749) ^ 1717025916 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 5151077749) ^ 2246436 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 5151077749) ^ 82548 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_5281376549 : Nat.Prime 5281376549 := by
  apply lucas_primality 5281376549 (2 : ZMod 5281376549)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (188620591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (188620591, 1)] : List FactorBlock).map factorBlockValue).prod) = 5281376549 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_7
      · exact prime_oneHundredTwentyOneDO_188620591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 5281376549) ^ 2640688274 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 5281376549) ^ 754482364 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 5281376549) ^ 28 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_5429792839 : Nat.Prime 5429792839 := by
  apply lucas_primality 5429792839 (6 : ZMod 5429792839)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (709, 1), (1276397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (709, 1), (1276397, 1)] : List FactorBlock).map factorBlockValue).prod) = 5429792839 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_709
      · exact prime_oneHundredTwentyOneDO_1276397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 5429792839) ^ 2714896419 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (6 : ZMod 5429792839) ^ 1809930946 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (6 : ZMod 5429792839) ^ 7658382 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (6 : ZMod 5429792839) ^ 4254 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_5825185187 : Nat.Prime 5825185187 := by
  apply lucas_primality 5825185187 (2 : ZMod 5825185187)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (179, 1), (856393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (179, 1), (856393, 1)] : List FactorBlock).map factorBlockValue).prod) = 5825185187 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_19
      · exact prime_oneHundredTwentyOneDO_179
      · exact prime_oneHundredTwentyOneDO_856393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5825185187) ^ 2912592593 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 5825185187) ^ 306588694 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 5825185187) ^ 32542934 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 5825185187) ^ 6802 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_6037638679 : Nat.Prime 6037638679 := by
  apply lucas_primality 6037638679 (3 : ZMod 6037638679)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) = 6037638679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_31
      · exact prime_oneHundredTwentyOneDO_10820141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6037638679) ^ 3018819339 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 2012546226 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 194762538 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 558 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_7989376103 : Nat.Prime 7989376103 := by
  apply lucas_primality 7989376103 (5 : ZMod 7989376103)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3994688051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3994688051, 1)] : List FactorBlock).map factorBlockValue).prod) = 7989376103 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3994688051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 7989376103) ^ 3994688051 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 7989376103) ^ 2 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_11273907287 : Nat.Prime 11273907287 := by
  apply lucas_primality 11273907287 (5 : ZMod 11273907287)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 2), (10655867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 2), (10655867, 1)] : List FactorBlock).map factorBlockValue).prod) = 11273907287 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_23
      · exact prime_oneHundredTwentyOneDO_10655867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 11273907287) ^ 5636953643 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 11273907287) ^ 490169882 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 11273907287) ^ 1058 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_13613253347 : Nat.Prime 13613253347 := by
  apply lucas_primality 13613253347 (2 : ZMod 13613253347)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 2), (97, 1), (82847, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 2), (97, 1), (82847, 1)] : List FactorBlock).map factorBlockValue).prod) = 13613253347 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_7
      · exact prime_oneHundredTwentyOneDO_11
      · exact prime_oneHundredTwentyOneDO_97
      · exact prime_oneHundredTwentyOneDO_82847
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 13613253347) ^ 6806626673 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 13613253347) ^ 1944750478 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 13613253347) ^ 1237568486 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 13613253347) ^ 140342818 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 13613253347) ^ 164318 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_14261813977 : Nat.Prime 14261813977 := by
  apply lucas_primality 14261813977 (5 : ZMod 14261813977)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (251, 1), (991, 1), (2389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (251, 1), (991, 1), (2389, 1)] : List FactorBlock).map factorBlockValue).prod) = 14261813977 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_251
      · exact prime_oneHundredTwentyOneDO_991
      · exact prime_oneHundredTwentyOneDO_2389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 14261813977) ^ 7130906988 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 14261813977) ^ 4753937992 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 14261813977) ^ 56819976 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 14261813977) ^ 14391336 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 14261813977) ^ 5969784 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_15396560497 : Nat.Prime 15396560497 := by
  apply lucas_primality 15396560497 (10 : ZMod 15396560497)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (106920559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (106920559, 1)] : List FactorBlock).map factorBlockValue).prod) = 15396560497 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_106920559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 15396560497) ^ 7698280248 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (10 : ZMod 15396560497) ^ 5132186832 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (10 : ZMod 15396560497) ^ 144 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_18110434427 : Nat.Prime 18110434427 := by
  apply lucas_primality 18110434427 (2 : ZMod 18110434427)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (8893, 1), (145463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (8893, 1), (145463, 1)] : List FactorBlock).map factorBlockValue).prod) = 18110434427 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_7
      · exact prime_oneHundredTwentyOneDO_8893
      · exact prime_oneHundredTwentyOneDO_145463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 18110434427) ^ 9055217213 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 18110434427) ^ 2587204918 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 18110434427) ^ 2036482 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 18110434427) ^ 124502 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_19022995471 : Nat.Prime 19022995471 := by
  apply lucas_primality 19022995471 (6 : ZMod 19022995471)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (1931, 1), (328379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (1931, 1), (328379, 1)] : List FactorBlock).map factorBlockValue).prod) = 19022995471 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_5
      · exact prime_oneHundredTwentyOneDO_1931
      · exact prime_oneHundredTwentyOneDO_328379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 19022995471) ^ 9511497735 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (6 : ZMod 19022995471) ^ 6340998490 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (6 : ZMod 19022995471) ^ 3804599094 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (6 : ZMod 19022995471) ^ 9851370 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (6 : ZMod 19022995471) ^ 57930 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_19953858371 : Nat.Prime 19953858371 := by
  apply lucas_primality 19953858371 (2 : ZMod 19953858371)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1201, 1), (1661437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1201, 1), (1661437, 1)] : List FactorBlock).map factorBlockValue).prod) = 19953858371 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_5
      · exact prime_oneHundredTwentyOneDO_1201
      · exact prime_oneHundredTwentyOneDO_1661437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 19953858371) ^ 9976929185 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 19953858371) ^ 3990771674 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 19953858371) ^ 16614370 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 19953858371) ^ 12010 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_24620995453 : Nat.Prime 24620995453 := by
  apply lucas_primality 24620995453 (2 : ZMod 24620995453)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (53, 1), (38712257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (53, 1), (38712257, 1)] : List FactorBlock).map factorBlockValue).prod) = 24620995453 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_53
      · exact prime_oneHundredTwentyOneDO_38712257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 24620995453) ^ 12310497726 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 24620995453) ^ 8206998484 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 24620995453) ^ 464547084 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 24620995453) ^ 636 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_25641967277 : Nat.Prime 25641967277 := by
  apply lucas_primality 25641967277 (2 : ZMod 25641967277)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (41, 2), (3813499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (41, 2), (3813499, 1)] : List FactorBlock).map factorBlockValue).prod) = 25641967277 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_41
      · exact prime_oneHundredTwentyOneDO_3813499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 25641967277) ^ 12820983638 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 25641967277) ^ 625413836 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 25641967277) ^ 6724 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_27918548017 : Nat.Prime 27918548017 := by
  apply lucas_primality 27918548017 (5 : ZMod 27918548017)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (19, 1), (30612443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (19, 1), (30612443, 1)] : List FactorBlock).map factorBlockValue).prod) = 27918548017 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_19
      · exact prime_oneHundredTwentyOneDO_30612443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 27918548017) ^ 13959274008 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 27918548017) ^ 9306182672 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 27918548017) ^ 1469397264 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 27918548017) ^ 912 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_29485457179 : Nat.Prime 29485457179 := by
  apply lucas_primality 29485457179 (2 : ZMod 29485457179)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (4914242863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (4914242863, 1)] : List FactorBlock).map factorBlockValue).prod) = 29485457179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_4914242863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 29485457179) ^ 14742728589 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 29485457179) ^ 9828485726 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 29485457179) ^ 6 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_32529611633 : Nat.Prime 32529611633 := by
  apply lucas_primality 32529611633 (5 : ZMod 32529611633)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (290442961, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (290442961, 1)] : List FactorBlock).map factorBlockValue).prod) = 32529611633 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_7
      · exact prime_oneHundredTwentyOneDO_290442961
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 32529611633) ^ 16264805816 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 32529611633) ^ 4647087376 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 32529611633) ^ 112 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_38365438219 : Nat.Prime 38365438219 := by
  apply lucas_primality 38365438219 (2 : ZMod 38365438219)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (3001, 1), (2130703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (3001, 1), (2130703, 1)] : List FactorBlock).map factorBlockValue).prod) = 38365438219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_3001
      · exact prime_oneHundredTwentyOneDO_2130703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 38365438219) ^ 19182719109 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 38365438219) ^ 12788479406 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 38365438219) ^ 12784218 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 38365438219) ^ 18006 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_43464529943 : Nat.Prime 43464529943 := by
  apply lucas_primality 43464529943 (5 : ZMod 43464529943)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (673, 1), (32291627, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (673, 1), (32291627, 1)] : List FactorBlock).map factorBlockValue).prod) = 43464529943 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_673
      · exact prime_oneHundredTwentyOneDO_32291627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 43464529943) ^ 21732264971 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 43464529943) ^ 64583254 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 43464529943) ^ 1346 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_43793876429 : Nat.Prime 43793876429 := by
  apply lucas_primality 43793876429 (2 : ZMod 43793876429)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (59, 1), (185567273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (59, 1), (185567273, 1)] : List FactorBlock).map factorBlockValue).prod) = 43793876429 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_59
      · exact prime_oneHundredTwentyOneDO_185567273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 43793876429) ^ 21896938214 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 43793876429) ^ 742269092 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 43793876429) ^ 236 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_48456886771 : Nat.Prime 48456886771 := by
  apply lucas_primality 48456886771 (3 : ZMod 48456886771)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (5, 1), (29, 1), (2062873, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (5, 1), (29, 1), (2062873, 1)] : List FactorBlock).map factorBlockValue).prod) = 48456886771 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_5
      · exact prime_oneHundredTwentyOneDO_29
      · exact prime_oneHundredTwentyOneDO_2062873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 48456886771) ^ 24228443385 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 48456886771) ^ 16152295590 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 48456886771) ^ 9691377354 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 48456886771) ^ 1670927130 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 48456886771) ^ 23490 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_51645051611 : Nat.Prime 51645051611 := by
  apply lucas_primality 51645051611 (2 : ZMod 51645051611)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (929, 1), (5559209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (929, 1), (5559209, 1)] : List FactorBlock).map factorBlockValue).prod) = 51645051611 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_5
      · exact prime_oneHundredTwentyOneDO_929
      · exact prime_oneHundredTwentyOneDO_5559209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 51645051611) ^ 25822525805 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 51645051611) ^ 10329010322 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 51645051611) ^ 55592090 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 51645051611) ^ 9290 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_52504156247 : Nat.Prime 52504156247 := by
  apply lucas_primality 52504156247 (5 : ZMod 52504156247)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (28547, 1), (39983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (28547, 1), (39983, 1)] : List FactorBlock).map factorBlockValue).prod) = 52504156247 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_23
      · exact prime_oneHundredTwentyOneDO_28547
      · exact prime_oneHundredTwentyOneDO_39983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 52504156247) ^ 26252078123 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 52504156247) ^ 2282789402 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 52504156247) ^ 1839218 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 52504156247) ^ 1313162 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_60579977329 : Nat.Prime 60579977329 := by
  apply lucas_primality 60579977329 (19 : ZMod 60579977329)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (13, 1), (337, 1), (32009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (13, 1), (337, 1), (32009, 1)] : List FactorBlock).map factorBlockValue).prod) = 60579977329 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_13
      · exact prime_oneHundredTwentyOneDO_337
      · exact prime_oneHundredTwentyOneDO_32009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 60579977329) ^ 30289988664 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (19 : ZMod 60579977329) ^ 20193325776 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (19 : ZMod 60579977329) ^ 4659998256 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (19 : ZMod 60579977329) ^ 179762544 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (19 : ZMod 60579977329) ^ 1892592 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_61224320167 : Nat.Prime 61224320167 := by
  apply lucas_primality 61224320167 (3 : ZMod 61224320167)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (29, 1), (20697877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (29, 1), (20697877, 1)] : List FactorBlock).map factorBlockValue).prod) = 61224320167 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_17
      · exact prime_oneHundredTwentyOneDO_29
      · exact prime_oneHundredTwentyOneDO_20697877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 61224320167) ^ 30612160083 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 61224320167) ^ 20408106722 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 61224320167) ^ 3601430598 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 61224320167) ^ 2111183454 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 61224320167) ^ 2958 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_61572219791 : Nat.Prime 61572219791 := by
  apply lucas_primality 61572219791 (11 : ZMod 61572219791)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (139, 1), (44296561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (139, 1), (44296561, 1)] : List FactorBlock).map factorBlockValue).prod) = 61572219791 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_5
      · exact prime_oneHundredTwentyOneDO_139
      · exact prime_oneHundredTwentyOneDO_44296561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 61572219791) ^ 30786109895 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (11 : ZMod 61572219791) ^ 12314443958 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (11 : ZMod 61572219791) ^ 442965610 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (11 : ZMod 61572219791) ^ 1390 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_65582676239 : Nat.Prime 65582676239 := by
  apply lucas_primality 65582676239 (11 : ZMod 65582676239)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (23, 1), (67, 1), (317, 1), (3533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (23, 1), (67, 1), (317, 1), (3533, 1)] : List FactorBlock).map factorBlockValue).prod) = 65582676239 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_19
      · exact prime_oneHundredTwentyOneDO_23
      · exact prime_oneHundredTwentyOneDO_67
      · exact prime_oneHundredTwentyOneDO_317
      · exact prime_oneHundredTwentyOneDO_3533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 65582676239) ^ 32791338119 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (11 : ZMod 65582676239) ^ 3451719802 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (11 : ZMod 65582676239) ^ 2851420706 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (11 : ZMod 65582676239) ^ 978845914 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (11 : ZMod 65582676239) ^ 206885414 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (11 : ZMod 65582676239) ^ 18562886 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_76027529471 : Nat.Prime 76027529471 := by
  apply lucas_primality 76027529471 (11 : ZMod 76027529471)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (47, 1), (161760701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (47, 1), (161760701, 1)] : List FactorBlock).map factorBlockValue).prod) = 76027529471 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_5
      · exact prime_oneHundredTwentyOneDO_47
      · exact prime_oneHundredTwentyOneDO_161760701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 76027529471) ^ 38013764735 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (11 : ZMod 76027529471) ^ 15205505894 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (11 : ZMod 76027529471) ^ 1617607010 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (11 : ZMod 76027529471) ^ 470 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_80377964003 : Nat.Prime 80377964003 := by
  apply lucas_primality 80377964003 (2 : ZMod 80377964003)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (19, 1), (563, 1), (536719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (19, 1), (563, 1), (536719, 1)] : List FactorBlock).map factorBlockValue).prod) = 80377964003 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_7
      · exact prime_oneHundredTwentyOneDO_19
      · exact prime_oneHundredTwentyOneDO_563
      · exact prime_oneHundredTwentyOneDO_536719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 80377964003) ^ 40188982001 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 80377964003) ^ 11482566286 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 80377964003) ^ 4230419158 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 80377964003) ^ 142767254 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 80377964003) ^ 149758 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_85026066847 : Nat.Prime 85026066847 := by
  apply lucas_primality 85026066847 (3 : ZMod 85026066847)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (101, 1), (409, 1), (7001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (101, 1), (409, 1), (7001, 1)] : List FactorBlock).map factorBlockValue).prod) = 85026066847 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_7
      · exact prime_oneHundredTwentyOneDO_101
      · exact prime_oneHundredTwentyOneDO_409
      · exact prime_oneHundredTwentyOneDO_7001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 85026066847) ^ 42513033423 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 85026066847) ^ 28342022282 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 85026066847) ^ 12146580978 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 85026066847) ^ 841842246 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 85026066847) ^ 207887694 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 85026066847) ^ 12144846 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_97779597193 : Nat.Prime 97779597193 := by
  apply lucas_primality 97779597193 (7 : ZMod 97779597193)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (29, 1), (37, 1), (1265657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (29, 1), (37, 1), (1265657, 1)] : List FactorBlock).map factorBlockValue).prod) = 97779597193 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_29
      · exact prime_oneHundredTwentyOneDO_37
      · exact prime_oneHundredTwentyOneDO_1265657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 97779597193) ^ 48889798596 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (7 : ZMod 97779597193) ^ 32593199064 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (7 : ZMod 97779597193) ^ 3371710248 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (7 : ZMod 97779597193) ^ 2642691816 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (7 : ZMod 97779597193) ^ 77256 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_124239312709 : Nat.Prime 124239312709 := by
  apply lucas_primality 124239312709 (11 : ZMod 124239312709)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (1279, 1), (1156403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (1279, 1), (1156403, 1)] : List FactorBlock).map factorBlockValue).prod) = 124239312709 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_7
      · exact prime_oneHundredTwentyOneDO_1279
      · exact prime_oneHundredTwentyOneDO_1156403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 124239312709) ^ 62119656354 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (11 : ZMod 124239312709) ^ 41413104236 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (11 : ZMod 124239312709) ^ 17748473244 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (11 : ZMod 124239312709) ^ 97137852 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (11 : ZMod 124239312709) ^ 107436 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_179746708591 : Nat.Prime 179746708591 := by
  apply lucas_primality 179746708591 (3 : ZMod 179746708591)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (1997185651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (1997185651, 1)] : List FactorBlock).map factorBlockValue).prod) = 179746708591 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_5
      · exact prime_oneHundredTwentyOneDO_1997185651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 179746708591) ^ 89873354295 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 179746708591) ^ 59915569530 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 179746708591) ^ 35949341718 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 179746708591) ^ 90 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_209179080359 : Nat.Prime 209179080359 := by
  apply lucas_primality 209179080359 (7 : ZMod 209179080359)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (419, 1), (1201, 1), (10939, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (419, 1), (1201, 1), (10939, 1)] : List FactorBlock).map factorBlockValue).prod) = 209179080359 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_19
      · exact prime_oneHundredTwentyOneDO_419
      · exact prime_oneHundredTwentyOneDO_1201
      · exact prime_oneHundredTwentyOneDO_10939
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 209179080359) ^ 104589540179 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (7 : ZMod 209179080359) ^ 11009425282 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (7 : ZMod 209179080359) ^ 499234082 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (7 : ZMod 209179080359) ^ 174170758 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (7 : ZMod 209179080359) ^ 19122322 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_270363888863 : Nat.Prime 270363888863 := by
  apply lucas_primality 270363888863 (5 : ZMod 270363888863)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1009, 1), (4091, 1), (32749, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1009, 1), (4091, 1), (32749, 1)] : List FactorBlock).map factorBlockValue).prod) = 270363888863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_1009
      · exact prime_oneHundredTwentyOneDO_4091
      · exact prime_oneHundredTwentyOneDO_32749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 270363888863) ^ 135181944431 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 270363888863) ^ 267952318 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 270363888863) ^ 66087482 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 270363888863) ^ 8255638 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_299124270941 : Nat.Prime 299124270941 := by
  apply lucas_primality 299124270941 (2 : ZMod 299124270941)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (11, 1), (127, 1), (10705951, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (11, 1), (127, 1), (10705951, 1)] : List FactorBlock).map factorBlockValue).prod) = 299124270941 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_5
      · exact prime_oneHundredTwentyOneDO_11
      · exact prime_oneHundredTwentyOneDO_127
      · exact prime_oneHundredTwentyOneDO_10705951
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 299124270941) ^ 149562135470 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 299124270941) ^ 59824854188 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 299124270941) ^ 27193115540 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 299124270941) ^ 2355309220 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 299124270941) ^ 27940 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_321161878913 : Nat.Prime 321161878913 := by
  apply lucas_primality 321161878913 (3 : ZMod 321161878913)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (7, 1), (358439597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (7, 1), (358439597, 1)] : List FactorBlock).map factorBlockValue).prod) = 321161878913 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_7
      · exact prime_oneHundredTwentyOneDO_358439597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 321161878913) ^ 160580939456 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 321161878913) ^ 45880268416 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 321161878913) ^ 896 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_358987541879 : Nat.Prime 358987541879 := by
  apply lucas_primality 358987541879 (7 : ZMod 358987541879)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (25641967277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (25641967277, 1)] : List FactorBlock).map factorBlockValue).prod) = 358987541879 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_7
      · exact prime_oneHundredTwentyOneDO_25641967277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 358987541879) ^ 179493770939 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (7 : ZMod 358987541879) ^ 51283934554 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (7 : ZMod 358987541879) ^ 14 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_476907466417 : Nat.Prime 476907466417 := by
  apply lucas_primality 476907466417 (10 : ZMod 476907466417)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (43, 1), (73, 1), (3165203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (43, 1), (73, 1), (3165203, 1)] : List FactorBlock).map factorBlockValue).prod) = 476907466417 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_43
      · exact prime_oneHundredTwentyOneDO_73
      · exact prime_oneHundredTwentyOneDO_3165203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 476907466417) ^ 238453733208 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (10 : ZMod 476907466417) ^ 158969155472 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (10 : ZMod 476907466417) ^ 11090871312 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (10 : ZMod 476907466417) ^ 6532978992 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (10 : ZMod 476907466417) ^ 150672 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_501958596917 : Nat.Prime 501958596917 := by
  apply lucas_primality 501958596917 (2 : ZMod 501958596917)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (35381, 1), (506687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (35381, 1), (506687, 1)] : List FactorBlock).map factorBlockValue).prod) = 501958596917 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_7
      · exact prime_oneHundredTwentyOneDO_35381
      · exact prime_oneHundredTwentyOneDO_506687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 501958596917) ^ 250979298458 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 501958596917) ^ 71708370988 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 501958596917) ^ 14187236 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 501958596917) ^ 990668 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_531307856377 : Nat.Prime 531307856377 := by
  apply lucas_primality 531307856377 (5 : ZMod 531307856377)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (11, 1), (670843253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (11, 1), (670843253, 1)] : List FactorBlock).map factorBlockValue).prod) = 531307856377 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_11
      · exact prime_oneHundredTwentyOneDO_670843253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 531307856377) ^ 265653928188 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 531307856377) ^ 177102618792 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 531307856377) ^ 48300714216 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 531307856377) ^ 792 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_700969938553 : Nat.Prime 700969938553 := by
  apply lucas_primality 700969938553 (5 : ZMod 700969938553)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (13, 1), (103, 1), (311, 1), (7793, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (13, 1), (103, 1), (311, 1), (7793, 1)] : List FactorBlock).map factorBlockValue).prod) = 700969938553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_13
      · exact prime_oneHundredTwentyOneDO_103
      · exact prime_oneHundredTwentyOneDO_311
      · exact prime_oneHundredTwentyOneDO_7793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 700969938553) ^ 350484969276 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 700969938553) ^ 233656646184 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 700969938553) ^ 53920764504 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 700969938553) ^ 6805533384 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 700969938553) ^ 2253922632 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 700969938553) ^ 89948664 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_767404309363 : Nat.Prime 767404309363 := by
  apply lucas_primality 767404309363 (2 : ZMod 767404309363)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (149689, 1), (854443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (149689, 1), (854443, 1)] : List FactorBlock).map factorBlockValue).prod) = 767404309363 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_149689
      · exact prime_oneHundredTwentyOneDO_854443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 767404309363) ^ 383702154681 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 767404309363) ^ 255801436454 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 767404309363) ^ 5126658 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 767404309363) ^ 898134 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_872897331191 : Nat.Prime 872897331191 := by
  apply lucas_primality 872897331191 (14 : ZMod 872897331191)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (257, 1), (339648767, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (257, 1), (339648767, 1)] : List FactorBlock).map factorBlockValue).prod) = 872897331191 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_5
      · exact prime_oneHundredTwentyOneDO_257
      · exact prime_oneHundredTwentyOneDO_339648767
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 872897331191) ^ 436448665595 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (14 : ZMod 872897331191) ^ 174579466238 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (14 : ZMod 872897331191) ^ 3396487670 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (14 : ZMod 872897331191) ^ 2570 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_910994932907 : Nat.Prime 910994932907 := by
  apply lucas_primality 910994932907 (2 : ZMod 910994932907)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (30047, 1), (15159499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (30047, 1), (15159499, 1)] : List FactorBlock).map factorBlockValue).prod) = 910994932907 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_30047
      · exact prime_oneHundredTwentyOneDO_15159499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 910994932907) ^ 455497466453 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 910994932907) ^ 30318998 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 910994932907) ^ 60094 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_930049555199 : Nat.Prime 930049555199 := by
  apply lucas_primality 930049555199 (7 : ZMod 930049555199)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (809, 1), (3623, 1), (158657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (809, 1), (3623, 1), (158657, 1)] : List FactorBlock).map factorBlockValue).prod) = 930049555199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_809
      · exact prime_oneHundredTwentyOneDO_3623
      · exact prime_oneHundredTwentyOneDO_158657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 930049555199) ^ 465024777599 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (7 : ZMod 930049555199) ^ 1149628622 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (7 : ZMod 930049555199) ^ 256707026 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (7 : ZMod 930049555199) ^ 5862014 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_978388996843 : Nat.Prime 978388996843 := by
  apply lucas_primality 978388996843 (2 : ZMod 978388996843)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (1753385299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (1753385299, 1)] : List FactorBlock).map factorBlockValue).prod) = 978388996843 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_31
      · exact prime_oneHundredTwentyOneDO_1753385299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 978388996843) ^ 489194498421 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 978388996843) ^ 326129665614 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 978388996843) ^ 31560935382 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 978388996843) ^ 558 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_1013186584247 : Nat.Prime 1013186584247 := by
  apply lucas_primality 1013186584247 (5 : ZMod 1013186584247)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (97, 1), (1069, 1), (287383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (97, 1), (1069, 1), (287383, 1)] : List FactorBlock).map factorBlockValue).prod) = 1013186584247 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_17
      · exact prime_oneHundredTwentyOneDO_97
      · exact prime_oneHundredTwentyOneDO_1069
      · exact prime_oneHundredTwentyOneDO_287383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1013186584247) ^ 506593292123 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 1013186584247) ^ 59599210838 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 1013186584247) ^ 10445222518 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 1013186584247) ^ 947789134 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 1013186584247) ^ 3525562 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_1146482427703 : Nat.Prime 1146482427703 := by
  apply lucas_primality 1146482427703 (5 : ZMod 1146482427703)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (23, 1), (5507, 1), (88741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (23, 1), (5507, 1), (88741, 1)] : List FactorBlock).map factorBlockValue).prod) = 1146482427703 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_17
      · exact prime_oneHundredTwentyOneDO_23
      · exact prime_oneHundredTwentyOneDO_5507
      · exact prime_oneHundredTwentyOneDO_88741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1146482427703) ^ 573241213851 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 1146482427703) ^ 382160809234 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 1146482427703) ^ 67440142806 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 1146482427703) ^ 49847062074 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 1146482427703) ^ 208186386 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 1146482427703) ^ 12919422 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_1163488269001 : Nat.Prime 1163488269001 := by
  apply lucas_primality 1163488269001 (13 : ZMod 1163488269001)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 3), (387829423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 3), (387829423, 1)] : List FactorBlock).map factorBlockValue).prod) = 1163488269001 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_5
      · exact prime_oneHundredTwentyOneDO_387829423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 1163488269001) ^ 581744134500 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (13 : ZMod 1163488269001) ^ 387829423000 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (13 : ZMod 1163488269001) ^ 232697653800 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (13 : ZMod 1163488269001) ^ 3000 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_1295508299753 : Nat.Prime 1295508299753 := by
  apply lucas_primality 1295508299753 (3 : ZMod 1295508299753)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (43759, 1), (3700691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (43759, 1), (3700691, 1)] : List FactorBlock).map factorBlockValue).prod) = 1295508299753 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_43759
      · exact prime_oneHundredTwentyOneDO_3700691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1295508299753) ^ 647754149876 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1295508299753) ^ 29605528 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1295508299753) ^ 350072 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_1424973002779 : Nat.Prime 1424973002779 := by
  apply lucas_primality 1424973002779 (2 : ZMod 1424973002779)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (137, 1), (251, 1), (177091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (137, 1), (251, 1), (177091, 1)] : List FactorBlock).map factorBlockValue).prod) = 1424973002779 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_13
      · exact prime_oneHundredTwentyOneDO_137
      · exact prime_oneHundredTwentyOneDO_251
      · exact prime_oneHundredTwentyOneDO_177091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1424973002779) ^ 712486501389 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1424973002779) ^ 474991000926 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1424973002779) ^ 109613307906 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1424973002779) ^ 10401262794 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1424973002779) ^ 5677183278 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1424973002779) ^ 8046558 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_1527879479293 : Nat.Prime 1527879479293 := by
  apply lucas_primality 1527879479293 (2 : ZMod 1527879479293)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (131, 1), (323977837, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (131, 1), (323977837, 1)] : List FactorBlock).map factorBlockValue).prod) = 1527879479293 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_131
      · exact prime_oneHundredTwentyOneDO_323977837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1527879479293) ^ 763939739646 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1527879479293) ^ 509293159764 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1527879479293) ^ 11663202132 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1527879479293) ^ 4716 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_1854949997179 : Nat.Prime 1854949997179 := by
  apply lucas_primality 1854949997179 (2 : ZMod 1854949997179)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (41, 1), (2513482381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (41, 1), (2513482381, 1)] : List FactorBlock).map factorBlockValue).prod) = 1854949997179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_41
      · exact prime_oneHundredTwentyOneDO_2513482381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1854949997179) ^ 927474998589 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1854949997179) ^ 618316665726 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1854949997179) ^ 45242682858 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1854949997179) ^ 738 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_1876252971787 : Nat.Prime 1876252971787 := by
  apply lucas_primality 1876252971787 (2 : ZMod 1876252971787)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (37, 1), (307, 1), (27529609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (37, 1), (307, 1), (27529609, 1)] : List FactorBlock).map factorBlockValue).prod) = 1876252971787 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_37
      · exact prime_oneHundredTwentyOneDO_307
      · exact prime_oneHundredTwentyOneDO_27529609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1876252971787) ^ 938126485893 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1876252971787) ^ 625417657262 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1876252971787) ^ 50709539778 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1876252971787) ^ 6111573198 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1876252971787) ^ 68154 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_1932639824057 : Nat.Prime 1932639824057 := by
  apply lucas_primality 1932639824057 (3 : ZMod 1932639824057)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (52529, 1), (4598983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (52529, 1), (4598983, 1)] : List FactorBlock).map factorBlockValue).prod) = 1932639824057 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_52529
      · exact prime_oneHundredTwentyOneDO_4598983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1932639824057) ^ 966319912028 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1932639824057) ^ 36791864 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1932639824057) ^ 420232 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_1949380506329 : Nat.Prime 1949380506329 := by
  apply lucas_primality 1949380506329 (6 : ZMod 1949380506329)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (41, 1), (967, 1), (6146053, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (41, 1), (967, 1), (6146053, 1)] : List FactorBlock).map factorBlockValue).prod) = 1949380506329 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_41
      · exact prime_oneHundredTwentyOneDO_967
      · exact prime_oneHundredTwentyOneDO_6146053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 1949380506329) ^ 974690253164 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (6 : ZMod 1949380506329) ^ 47545866008 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (6 : ZMod 1949380506329) ^ 2015905384 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (6 : ZMod 1949380506329) ^ 317176 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_2559125698709 : Nat.Prime 2559125698709 := by
  apply lucas_primality 2559125698709 (2 : ZMod 2559125698709)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (650189, 1), (983993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (650189, 1), (983993, 1)] : List FactorBlock).map factorBlockValue).prod) = 2559125698709 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_650189
      · exact prime_oneHundredTwentyOneDO_983993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2559125698709) ^ 1279562849354 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2559125698709) ^ 3935972 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2559125698709) ^ 2600756 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_2853185964991 : Nat.Prime 2853185964991 := by
  apply lucas_primality 2853185964991 (6 : ZMod 2853185964991)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (101, 1), (433, 1), (2174701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (101, 1), (433, 1), (2174701, 1)] : List FactorBlock).map factorBlockValue).prod) = 2853185964991 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_5
      · exact prime_oneHundredTwentyOneDO_101
      · exact prime_oneHundredTwentyOneDO_433
      · exact prime_oneHundredTwentyOneDO_2174701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 2853185964991) ^ 1426592982495 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (6 : ZMod 2853185964991) ^ 951061988330 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (6 : ZMod 2853185964991) ^ 570637192998 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (6 : ZMod 2853185964991) ^ 28249365990 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (6 : ZMod 2853185964991) ^ 6589344030 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (6 : ZMod 2853185964991) ^ 1311990 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_3404722137977 : Nat.Prime 3404722137977 := by
  apply lucas_primality 3404722137977 (3 : ZMod 3404722137977)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (61, 1), (67, 1), (104132681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (61, 1), (67, 1), (104132681, 1)] : List FactorBlock).map factorBlockValue).prod) = 3404722137977 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_61
      · exact prime_oneHundredTwentyOneDO_67
      · exact prime_oneHundredTwentyOneDO_104132681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3404722137977) ^ 1702361068988 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 3404722137977) ^ 55815117016 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 3404722137977) ^ 50816748328 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 3404722137977) ^ 32696 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_3420337309747 : Nat.Prime 3420337309747 := by
  apply lucas_primality 3420337309747 (3 : ZMod 3420337309747)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (17, 1), (71, 1), (4289, 1), (15731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (17, 1), (71, 1), (4289, 1), (15731, 1)] : List FactorBlock).map factorBlockValue).prod) = 3420337309747 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_7
      · exact prime_oneHundredTwentyOneDO_17
      · exact prime_oneHundredTwentyOneDO_71
      · exact prime_oneHundredTwentyOneDO_4289
      · exact prime_oneHundredTwentyOneDO_15731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3420337309747) ^ 1710168654873 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 3420337309747) ^ 1140112436582 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 3420337309747) ^ 488619615678 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 3420337309747) ^ 201196312338 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 3420337309747) ^ 48173764926 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 3420337309747) ^ 797467314 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 3420337309747) ^ 217426566 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_3446492502899 : Nat.Prime 3446492502899 := by
  apply lucas_primality 3446492502899 (2 : ZMod 3446492502899)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (751, 1), (99765313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (751, 1), (99765313, 1)] : List FactorBlock).map factorBlockValue).prod) = 3446492502899 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_23
      · exact prime_oneHundredTwentyOneDO_751
      · exact prime_oneHundredTwentyOneDO_99765313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3446492502899) ^ 1723246251449 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 3446492502899) ^ 149847500126 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 3446492502899) ^ 4589204398 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 3446492502899) ^ 34546 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_3519865880381 : Nat.Prime 3519865880381 := by
  apply lucas_primality 3519865880381 (2 : ZMod 3519865880381)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (17, 1), (71, 1), (4513, 1), (32309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (17, 1), (71, 1), (4513, 1), (32309, 1)] : List FactorBlock).map factorBlockValue).prod) = 3519865880381 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_5
      · exact prime_oneHundredTwentyOneDO_17
      · exact prime_oneHundredTwentyOneDO_71
      · exact prime_oneHundredTwentyOneDO_4513
      · exact prime_oneHundredTwentyOneDO_32309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3519865880381) ^ 1759932940190 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 3519865880381) ^ 703973176076 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 3519865880381) ^ 207050934140 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 3519865880381) ^ 49575575780 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 3519865880381) ^ 779939260 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 3519865880381) ^ 108943820 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_4205819631319 : Nat.Prime 4205819631319 := by
  apply lucas_primality 4205819631319 (3 : ZMod 4205819631319)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (700969938553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (700969938553, 1)] : List FactorBlock).map factorBlockValue).prod) = 4205819631319 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_700969938553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 4205819631319) ^ 2102909815659 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 4205819631319) ^ 1401939877106 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 4205819631319) ^ 6 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_5649569214607 : Nat.Prime 5649569214607 := by
  apply lucas_primality 5649569214607 (3 : ZMod 5649569214607)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (467, 1), (672087701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (467, 1), (672087701, 1)] : List FactorBlock).map factorBlockValue).prod) = 5649569214607 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_467
      · exact prime_oneHundredTwentyOneDO_672087701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 5649569214607) ^ 2824784607303 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 5649569214607) ^ 1883189738202 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 5649569214607) ^ 12097578618 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 5649569214607) ^ 8406 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_6488733332713 : Nat.Prime 6488733332713 := by
  apply lucas_primality 6488733332713 (5 : ZMod 6488733332713)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (270363888863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (270363888863, 1)] : List FactorBlock).map factorBlockValue).prod) = 6488733332713 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_270363888863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 6488733332713) ^ 3244366666356 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 6488733332713) ^ 2162911110904 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 6488733332713) ^ 24 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_7438682290051 : Nat.Prime 7438682290051 := by
  apply lucas_primality 7438682290051 (10 : ZMod 7438682290051)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (11, 1), (1502764099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (11, 1), (1502764099, 1)] : List FactorBlock).map factorBlockValue).prod) = 7438682290051 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_5
      · exact prime_oneHundredTwentyOneDO_11
      · exact prime_oneHundredTwentyOneDO_1502764099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 7438682290051) ^ 3719341145025 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (10 : ZMod 7438682290051) ^ 2479560763350 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (10 : ZMod 7438682290051) ^ 1487736458010 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (10 : ZMod 7438682290051) ^ 676243844550 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (10 : ZMod 7438682290051) ^ 4950 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_8089150399273 : Nat.Prime 8089150399273 := by
  apply lucas_primality 8089150399273 (7 : ZMod 8089150399273)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 4), (68543, 1), (182123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 4), (68543, 1), (182123, 1)] : List FactorBlock).map factorBlockValue).prod) = 8089150399273 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_68543
      · exact prime_oneHundredTwentyOneDO_182123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 8089150399273) ^ 4044575199636 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (7 : ZMod 8089150399273) ^ 2696383466424 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (7 : ZMod 8089150399273) ^ 118015704 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (7 : ZMod 8089150399273) ^ 44415864 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_8448956183047 : Nat.Prime 8448956183047 := by
  apply lucas_primality 8448956183047 (5 : ZMod 8448956183047)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (61224320167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (61224320167, 1)] : List FactorBlock).map factorBlockValue).prod) = 8448956183047 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_23
      · exact prime_oneHundredTwentyOneDO_61224320167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 8448956183047) ^ 4224478091523 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 8448956183047) ^ 2816318727682 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 8448956183047) ^ 367345921002 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 8448956183047) ^ 138 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_8627842012369 : Nat.Prime 8627842012369 := by
  apply lucas_primality 8627842012369 (7 : ZMod 8627842012369)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (179746708591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (179746708591, 1)] : List FactorBlock).map factorBlockValue).prod) = 8627842012369 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_179746708591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 8627842012369) ^ 4313921006184 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (7 : ZMod 8627842012369) ^ 2875947337456 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (7 : ZMod 8627842012369) ^ 48 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_10412125837669 : Nat.Prime 10412125837669 := by
  apply lucas_primality 10412125837669 (6 : ZMod 10412125837669)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 9), (8377, 1), (15787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 9), (8377, 1), (15787, 1)] : List FactorBlock).map factorBlockValue).prod) = 10412125837669 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_8377
      · exact prime_oneHundredTwentyOneDO_15787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 10412125837669) ^ 5206062918834 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (6 : ZMod 10412125837669) ^ 3470708612556 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (6 : ZMod 10412125837669) ^ 1242942084 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (6 : ZMod 10412125837669) ^ 659537964 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_10949790224383 : Nat.Prime 10949790224383 := by
  apply lucas_primality 10949790224383 (3 : ZMod 10949790224383)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (4133, 1), (441559409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (4133, 1), (441559409, 1)] : List FactorBlock).map factorBlockValue).prod) = 10949790224383 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_4133
      · exact prime_oneHundredTwentyOneDO_441559409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 10949790224383) ^ 5474895112191 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 10949790224383) ^ 3649930074794 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 10949790224383) ^ 2649356454 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 10949790224383) ^ 24798 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_11160594662389 : Nat.Prime 11160594662389 := by
  apply lucas_primality 11160594662389 (2 : ZMod 11160594662389)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (930049555199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (930049555199, 1)] : List FactorBlock).map factorBlockValue).prod) = 11160594662389 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_930049555199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 11160594662389) ^ 5580297331194 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 11160594662389) ^ 3720198220796 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 11160594662389) ^ 12 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_12295227120257 : Nat.Prime 12295227120257 := by
  apply lucas_primality 12295227120257 (3 : ZMod 12295227120257)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (19759, 1), (4861403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (19759, 1), (4861403, 1)] : List FactorBlock).map factorBlockValue).prod) = 12295227120257 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_19759
      · exact prime_oneHundredTwentyOneDO_4861403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 12295227120257) ^ 6147613560128 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 12295227120257) ^ 622259584 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 12295227120257) ^ 2529152 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_12668277994741 : Nat.Prime 12668277994741 := by
  apply lucas_primality 12668277994741 (7 : ZMod 12668277994741)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (17, 1), (1069, 1), (1861, 1), (2081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (17, 1), (1069, 1), (1861, 1), (2081, 1)] : List FactorBlock).map factorBlockValue).prod) = 12668277994741 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_5
      · exact prime_oneHundredTwentyOneDO_17
      · exact prime_oneHundredTwentyOneDO_1069
      · exact prime_oneHundredTwentyOneDO_1861
      · exact prime_oneHundredTwentyOneDO_2081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 12668277994741) ^ 6334138997370 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (7 : ZMod 12668277994741) ^ 4222759331580 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (7 : ZMod 12668277994741) ^ 2533655598948 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (7 : ZMod 12668277994741) ^ 745192823220 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (7 : ZMod 12668277994741) ^ 11850587460 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (7 : ZMod 12668277994741) ^ 6807242340 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (7 : ZMod 12668277994741) ^ 6087591540 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_17320005349313 : Nat.Prime 17320005349313 := by
  apply lucas_primality 17320005349313 (3 : ZMod 17320005349313)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (16091, 1), (16818413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (16091, 1), (16818413, 1)] : List FactorBlock).map factorBlockValue).prod) = 17320005349313 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_16091
      · exact prime_oneHundredTwentyOneDO_16818413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 17320005349313) ^ 8660002674656 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 17320005349313) ^ 1076378432 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 17320005349313) ^ 1029824 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_25582988003357 : Nat.Prime 25582988003357 := by
  apply lucas_primality 25582988003357 (2 : ZMod 25582988003357)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (173, 1), (5281376549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (173, 1), (5281376549, 1)] : List FactorBlock).map factorBlockValue).prod) = 25582988003357 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_7
      · exact prime_oneHundredTwentyOneDO_173
      · exact prime_oneHundredTwentyOneDO_5281376549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 25582988003357) ^ 12791494001678 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 25582988003357) ^ 3654712571908 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 25582988003357) ^ 147878543372 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 25582988003357) ^ 4844 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_47407327182587 : Nat.Prime 47407327182587 := by
  apply lucas_primality 47407327182587 (2 : ZMod 47407327182587)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (17, 1), (19, 1), (41, 1), (3767, 1), (9697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (17, 1), (19, 1), (41, 1), (3767, 1), (9697, 1)] : List FactorBlock).map factorBlockValue).prod) = 47407327182587 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_7
      · exact prime_oneHundredTwentyOneDO_17
      · exact prime_oneHundredTwentyOneDO_19
      · exact prime_oneHundredTwentyOneDO_41
      · exact prime_oneHundredTwentyOneDO_3767
      · exact prime_oneHundredTwentyOneDO_9697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 47407327182587) ^ 23703663591293 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 47407327182587) ^ 6772475311798 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 47407327182587) ^ 2788666304858 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 47407327182587) ^ 2495122483294 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 47407327182587) ^ 1156276272746 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 47407327182587) ^ 12584902358 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 47407327182587) ^ 4888865338 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_57706308742757 : Nat.Prime 57706308742757 := by
  apply lucas_primality 57706308742757 (2 : ZMod 57706308742757)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (937, 1), (15396560497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (937, 1), (15396560497, 1)] : List FactorBlock).map factorBlockValue).prod) = 57706308742757 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_937
      · exact prime_oneHundredTwentyOneDO_15396560497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 57706308742757) ^ 28853154371378 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 57706308742757) ^ 61586241988 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 57706308742757) ^ 3748 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_66139999399751 : Nat.Prime 66139999399751 := by
  apply lucas_primality 66139999399751 (7 : ZMod 66139999399751)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 3), (1321, 1), (200272519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 3), (1321, 1), (200272519, 1)] : List FactorBlock).map factorBlockValue).prod) = 66139999399751 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_5
      · exact prime_oneHundredTwentyOneDO_1321
      · exact prime_oneHundredTwentyOneDO_200272519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 66139999399751) ^ 33069999699875 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (7 : ZMod 66139999399751) ^ 13227999879950 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (7 : ZMod 66139999399751) ^ 50068129750 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (7 : ZMod 66139999399751) ^ 330250 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_67607421575051 : Nat.Prime 67607421575051 := by
  apply lucas_primality 67607421575051 (2 : ZMod 67607421575051)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (7, 3), (7879, 1), (500333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (7, 3), (7879, 1), (500333, 1)] : List FactorBlock).map factorBlockValue).prod) = 67607421575051 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_5
      · exact prime_oneHundredTwentyOneDO_7
      · exact prime_oneHundredTwentyOneDO_7879
      · exact prime_oneHundredTwentyOneDO_500333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 67607421575051) ^ 33803710787525 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 67607421575051) ^ 13521484315010 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 67607421575051) ^ 9658203082150 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 67607421575051) ^ 8580710950 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 67607421575051) ^ 135124850 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_77182241507551 : Nat.Prime 77182241507551 := by
  apply lucas_primality 77182241507551 (3 : ZMod 77182241507551)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (31, 1), (71, 1), (77926439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (31, 1), (71, 1), (77926439, 1)] : List FactorBlock).map factorBlockValue).prod) = 77182241507551 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_5
      · exact prime_oneHundredTwentyOneDO_31
      · exact prime_oneHundredTwentyOneDO_71
      · exact prime_oneHundredTwentyOneDO_77926439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 77182241507551) ^ 38591120753775 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 77182241507551) ^ 25727413835850 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 77182241507551) ^ 15436448301510 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 77182241507551) ^ 2489749726050 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 77182241507551) ^ 1087073824050 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 77182241507551) ^ 990450 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_110517724970203 : Nat.Prime 110517724970203 := by
  apply lucas_primality 110517724970203 (11 : ZMod 110517724970203)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (17, 1), (2087, 1), (47197243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (17, 1), (2087, 1), (47197243, 1)] : List FactorBlock).map factorBlockValue).prod) = 110517724970203 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_11
      · exact prime_oneHundredTwentyOneDO_17
      · exact prime_oneHundredTwentyOneDO_2087
      · exact prime_oneHundredTwentyOneDO_47197243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 110517724970203) ^ 55258862485101 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (11 : ZMod 110517724970203) ^ 36839241656734 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (11 : ZMod 110517724970203) ^ 10047065906382 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (11 : ZMod 110517724970203) ^ 6501042645306 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (11 : ZMod 110517724970203) ^ 52955306646 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (11 : ZMod 110517724970203) ^ 2341614 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_120760683377107 : Nat.Prime 120760683377107 := by
  apply lucas_primality 120760683377107 (5 : ZMod 120760683377107)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (102079, 1), (11598157, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (102079, 1), (11598157, 1)] : List FactorBlock).map factorBlockValue).prod) = 120760683377107 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_17
      · exact prime_oneHundredTwentyOneDO_102079
      · exact prime_oneHundredTwentyOneDO_11598157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 120760683377107) ^ 60380341688553 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 120760683377107) ^ 40253561125702 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 120760683377107) ^ 7103569610418 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 120760683377107) ^ 1183012014 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 120760683377107) ^ 10412058 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_127247943062269 : Nat.Prime 127247943062269 := by
  apply lucas_primality 127247943062269 (2 : ZMod 127247943062269)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 5), (7, 1), (19, 1), (10663, 1), (92311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 5), (7, 1), (19, 1), (10663, 1), (92311, 1)] : List FactorBlock).map factorBlockValue).prod) = 127247943062269 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_7
      · exact prime_oneHundredTwentyOneDO_19
      · exact prime_oneHundredTwentyOneDO_10663
      · exact prime_oneHundredTwentyOneDO_92311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 127247943062269) ^ 63623971531134 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 127247943062269) ^ 42415981020756 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 127247943062269) ^ 18178277580324 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 127247943062269) ^ 6697260161172 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 127247943062269) ^ 11933596836 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 127247943062269) ^ 1378469988 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_135043290227249 : Nat.Prime 135043290227249 := by
  apply lucas_primality 135043290227249 (3 : ZMod 135043290227249)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (13, 1), (17, 1), (89, 1), (15227, 1), (28181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (13, 1), (17, 1), (89, 1), (15227, 1), (28181, 1)] : List FactorBlock).map factorBlockValue).prod) = 135043290227249 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_13
      · exact prime_oneHundredTwentyOneDO_17
      · exact prime_oneHundredTwentyOneDO_89
      · exact prime_oneHundredTwentyOneDO_15227
      · exact prime_oneHundredTwentyOneDO_28181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 135043290227249) ^ 67521645113624 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 135043290227249) ^ 10387945402096 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 135043290227249) ^ 7943722954544 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 135043290227249) ^ 1517340339632 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 135043290227249) ^ 8868673424 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 135043290227249) ^ 4791997808 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_152081211294847 : Nat.Prime 152081211294847 := by
  apply lucas_primality 152081211294847 (3 : ZMod 152081211294847)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (8448956183047, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (8448956183047, 1)] : List FactorBlock).map factorBlockValue).prod) = 152081211294847 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_8448956183047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 152081211294847) ^ 76040605647423 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 152081211294847) ^ 50693737098282 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 152081211294847) ^ 18 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_181155642691489 : Nat.Prime 181155642691489 := by
  apply lucas_primality 181155642691489 (23 : ZMod 181155642691489)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (1259, 1), (1498838717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (1259, 1), (1498838717, 1)] : List FactorBlock).map factorBlockValue).prod) = 181155642691489 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_1259
      · exact prime_oneHundredTwentyOneDO_1498838717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (23 : ZMod 181155642691489) ^ 90577821345744 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (23 : ZMod 181155642691489) ^ 60385214230496 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (23 : ZMod 181155642691489) ^ 143888516832 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (23 : ZMod 181155642691489) ^ 120864 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_270086580454499 : Nat.Prime 270086580454499 := by
  apply lucas_primality 270086580454499 (2 : ZMod 270086580454499)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (135043290227249, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (135043290227249, 1)] : List FactorBlock).map factorBlockValue).prod) = 270086580454499 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_135043290227249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 270086580454499) ^ 135043290227249 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 270086580454499) ^ 2 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_308312035685249 : Nat.Prime 308312035685249 := by
  apply lucas_primality 308312035685249 (3 : ZMod 308312035685249)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (7, 1), (19, 1), (18110434427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (7, 1), (19, 1), (18110434427, 1)] : List FactorBlock).map factorBlockValue).prod) = 308312035685249 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_7
      · exact prime_oneHundredTwentyOneDO_19
      · exact prime_oneHundredTwentyOneDO_18110434427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 308312035685249) ^ 154156017842624 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 308312035685249) ^ 44044576526464 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 308312035685249) ^ 16226949246592 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 308312035685249) ^ 17024 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_308765963399027 : Nat.Prime 308765963399027 := by
  apply lucas_primality 308765963399027 (2 : ZMod 308765963399027)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (47, 1), (199, 1), (2358036103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (47, 1), (199, 1), (2358036103, 1)] : List FactorBlock).map factorBlockValue).prod) = 308765963399027 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_7
      · exact prime_oneHundredTwentyOneDO_47
      · exact prime_oneHundredTwentyOneDO_199
      · exact prime_oneHundredTwentyOneDO_2358036103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 308765963399027) ^ 154382981699513 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 308765963399027) ^ 44109423342718 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 308765963399027) ^ 6569488582958 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 308765963399027) ^ 1551587755774 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 308765963399027) ^ 130942 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_526587885894017 : Nat.Prime 526587885894017 := by
  apply lucas_primality 526587885894017 (3 : ZMod 526587885894017)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (43, 1), (26113, 1), (3663833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (43, 1), (26113, 1), (3663833, 1)] : List FactorBlock).map factorBlockValue).prod) = 526587885894017 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_43
      · exact prime_oneHundredTwentyOneDO_26113
      · exact prime_oneHundredTwentyOneDO_3663833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 526587885894017) ^ 263293942947008 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 526587885894017) ^ 12246229904512 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 526587885894017) ^ 20165736832 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 526587885894017) ^ 143725952 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_540173160908999 : Nat.Prime 540173160908999 := by
  apply lucas_primality 540173160908999 (7 : ZMod 540173160908999)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (270086580454499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (270086580454499, 1)] : List FactorBlock).map factorBlockValue).prod) = 540173160908999 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_270086580454499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (7 : ZMod 540173160908999) ^ 270086580454499 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (7 : ZMod 540173160908999) ^ 2 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_651357393302093 : Nat.Prime 651357393302093 := by
  apply lucas_primality 651357393302093 (2 : ZMod 651357393302093)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (1741, 1), (5821, 1), (945179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (1741, 1), (5821, 1), (945179, 1)] : List FactorBlock).map factorBlockValue).prod) = 651357393302093 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_17
      · exact prime_oneHundredTwentyOneDO_1741
      · exact prime_oneHundredTwentyOneDO_5821
      · exact prime_oneHundredTwentyOneDO_945179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 651357393302093) ^ 325678696651046 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 651357393302093) ^ 38315140782476 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 651357393302093) ^ 374128313212 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 651357393302093) ^ 111897851452 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 651357393302093) ^ 689136548 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_850556908919339 : Nat.Prime 850556908919339 := by
  apply lucas_primality 850556908919339 (2 : ZMod 850556908919339)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (751, 1), (24620995453, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (751, 1), (24620995453, 1)] : List FactorBlock).map factorBlockValue).prod) = 850556908919339 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_23
      · exact prime_oneHundredTwentyOneDO_751
      · exact prime_oneHundredTwentyOneDO_24620995453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 850556908919339) ^ 425278454459669 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 850556908919339) ^ 36980735170406 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 850556908919339) ^ 1132565790838 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 850556908919339) ^ 34546 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_969174263781499 : Nat.Prime 969174263781499 := by
  apply lucas_primality 969174263781499 (3 : ZMod 969174263781499)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 1), (79, 1), (619, 1), (113902927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 1), (79, 1), (619, 1), (113902927, 1)] : List FactorBlock).map factorBlockValue).prod) = 969174263781499 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_29
      · exact prime_oneHundredTwentyOneDO_79
      · exact prime_oneHundredTwentyOneDO_619
      · exact prime_oneHundredTwentyOneDO_113902927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 969174263781499) ^ 484587131890749 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 969174263781499) ^ 323058087927166 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 969174263781499) ^ 33419802199362 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 969174263781499) ^ 12268028655462 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 969174263781499) ^ 1565709634542 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 969174263781499) ^ 8508774 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_1032799078101589 : Nat.Prime 1032799078101589 := by
  apply lucas_primality 1032799078101589 (2 : ZMod 1032799078101589)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (12295227120257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (12295227120257, 1)] : List FactorBlock).map factorBlockValue).prod) = 1032799078101589 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_7
      · exact prime_oneHundredTwentyOneDO_12295227120257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1032799078101589) ^ 516399539050794 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1032799078101589) ^ 344266359367196 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1032799078101589) ^ 147542725443084 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1032799078101589) ^ 84 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_1244510803984297 : Nat.Prime 1244510803984297 := by
  apply lucas_primality 1244510803984297 (13 : ZMod 1244510803984297)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (53, 1), (978388996843, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (53, 1), (978388996843, 1)] : List FactorBlock).map factorBlockValue).prod) = 1244510803984297 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_53
      · exact prime_oneHundredTwentyOneDO_978388996843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 1244510803984297) ^ 622255401992148 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (13 : ZMod 1244510803984297) ^ 414836934661432 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (13 : ZMod 1244510803984297) ^ 23481335924232 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (13 : ZMod 1244510803984297) ^ 1272 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_3683950272483409 : Nat.Prime 3683950272483409 := by
  apply lucas_primality 3683950272483409 (7 : ZMod 3683950272483409)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (25582988003357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (25582988003357, 1)] : List FactorBlock).map factorBlockValue).prod) = 3683950272483409 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_25582988003357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 3683950272483409) ^ 1841975136241704 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (7 : ZMod 3683950272483409) ^ 1227983424161136 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (7 : ZMod 3683950272483409) ^ 144 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_4230662710903529 : Nat.Prime 4230662710903529 := by
  apply lucas_primality 4230662710903529 (3 : ZMod 4230662710903529)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (127, 1), (4513, 1), (922676291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (127, 1), (4513, 1), (922676291, 1)] : List FactorBlock).map factorBlockValue).prod) = 4230662710903529 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_127
      · exact prime_oneHundredTwentyOneDO_4513
      · exact prime_oneHundredTwentyOneDO_922676291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4230662710903529) ^ 2115331355451764 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 4230662710903529) ^ 33312304810264 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 4230662710903529) ^ 937439111656 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 4230662710903529) ^ 4585208 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_4991573785810037 : Nat.Prime 4991573785810037 := by
  apply lucas_primality 4991573785810037 (3 : ZMod 4991573785810037)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (59, 1), (458483, 1), (2005739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (59, 1), (458483, 1), (2005739, 1)] : List FactorBlock).map factorBlockValue).prod) = 4991573785810037 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_23
      · exact prime_oneHundredTwentyOneDO_59
      · exact prime_oneHundredTwentyOneDO_458483
      · exact prime_oneHundredTwentyOneDO_2005739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4991573785810037) ^ 2495786892905018 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 4991573785810037) ^ 217024947209132 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 4991573785810037) ^ 84602945522204 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 4991573785810037) ^ 10887151292 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 4991573785810037) ^ 2488645724 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_6465794100565351 : Nat.Prime 6465794100565351 := by
  apply lucas_primality 6465794100565351 (3 : ZMod 6465794100565351)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (191, 1), (277, 1), (1319, 1), (617693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (191, 1), (277, 1), (1319, 1), (617693, 1)] : List FactorBlock).map factorBlockValue).prod) = 6465794100565351 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_5
      · exact prime_oneHundredTwentyOneDO_191
      · exact prime_oneHundredTwentyOneDO_277
      · exact prime_oneHundredTwentyOneDO_1319
      · exact prime_oneHundredTwentyOneDO_617693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 6465794100565351) ^ 3232897050282675 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 6465794100565351) ^ 2155264700188450 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 6465794100565351) ^ 1293158820113070 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 6465794100565351) ^ 33852325133850 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 6465794100565351) ^ 23342216969550 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 6465794100565351) ^ 4902042532650 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 6465794100565351) ^ 10467649950 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_6982819718723939 : Nat.Prime 6982819718723939 := by
  apply lucas_primality 6982819718723939 (2 : ZMod 6982819718723939)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (79, 1), (1583, 1), (27918548017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (79, 1), (1583, 1), (27918548017, 1)] : List FactorBlock).map factorBlockValue).prod) = 6982819718723939 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_79
      · exact prime_oneHundredTwentyOneDO_1583
      · exact prime_oneHundredTwentyOneDO_27918548017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 6982819718723939) ^ 3491409859361969 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 6982819718723939) ^ 88390123021822 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 6982819718723939) ^ 4411130586686 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 6982819718723939) ^ 250114 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_7657277528107127 : Nat.Prime 7657277528107127 := by
  apply lucas_primality 7657277528107127 (5 : ZMod 7657277528107127)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (1217, 1), (85026066847, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (1217, 1), (85026066847, 1)] : List FactorBlock).map factorBlockValue).prod) = 7657277528107127 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_37
      · exact prime_oneHundredTwentyOneDO_1217
      · exact prime_oneHundredTwentyOneDO_85026066847
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 7657277528107127) ^ 3828638764053563 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 7657277528107127) ^ 206953446705598 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 7657277528107127) ^ 6291928946678 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 7657277528107127) ^ 90058 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_10656541624904779 : Nat.Prime 10656541624904779 := by
  apply lucas_primality 10656541624904779 (2 : ZMod 10656541624904779)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (36653, 1), (48456886771, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (36653, 1), (48456886771, 1)] : List FactorBlock).map factorBlockValue).prod) = 10656541624904779 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_36653
      · exact prime_oneHundredTwentyOneDO_48456886771
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 10656541624904779) ^ 5328270812452389 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 10656541624904779) ^ 3552180541634926 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 10656541624904779) ^ 290741320626 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 10656541624904779) ^ 219918 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_11075154693333529 : Nat.Prime 11075154693333529 := by
  apply lucas_primality 11075154693333529 (19 : ZMod 11075154693333529)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 2), (8597, 1), (1095457549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 2), (8597, 1), (1095457549, 1)] : List FactorBlock).map factorBlockValue).prod) = 11075154693333529 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_7
      · exact prime_oneHundredTwentyOneDO_8597
      · exact prime_oneHundredTwentyOneDO_1095457549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 11075154693333529) ^ 5537577346666764 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (19 : ZMod 11075154693333529) ^ 3691718231111176 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (19 : ZMod 11075154693333529) ^ 1582164956190504 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (19 : ZMod 11075154693333529) ^ 1288258077624 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (19 : ZMod 11075154693333529) ^ 10110072 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_16305776300704313 : Nat.Prime 16305776300704313 := by
  apply lucas_primality 16305776300704313 (3 : ZMod 16305776300704313)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17, 1), (19, 1), (83, 1), (76027529471, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17, 1), (19, 1), (83, 1), (76027529471, 1)] : List FactorBlock).map factorBlockValue).prod) = 16305776300704313 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_17
      · exact prime_oneHundredTwentyOneDO_19
      · exact prime_oneHundredTwentyOneDO_83
      · exact prime_oneHundredTwentyOneDO_76027529471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 16305776300704313) ^ 8152888150352156 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 16305776300704313) ^ 959163311806136 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 16305776300704313) ^ 858198752668648 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 16305776300704313) ^ 196455136153064 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 16305776300704313) ^ 214472 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_21567286335162311 : Nat.Prime 21567286335162311 := by
  apply lucas_primality 21567286335162311 (7 : ZMod 21567286335162311)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (4051, 1), (21617, 1), (24628493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (4051, 1), (21617, 1), (24628493, 1)] : List FactorBlock).map factorBlockValue).prod) = 21567286335162311 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_5
      · exact prime_oneHundredTwentyOneDO_4051
      · exact prime_oneHundredTwentyOneDO_21617
      · exact prime_oneHundredTwentyOneDO_24628493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 21567286335162311) ^ 10783643167581155 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (7 : ZMod 21567286335162311) ^ 4313457267032462 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (7 : ZMod 21567286335162311) ^ 5323941331810 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (7 : ZMod 21567286335162311) ^ 997700251430 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (7 : ZMod 21567286335162311) ^ 875704670 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_26201610349460101 : Nat.Prime 26201610349460101 := by
  apply lucas_primality 26201610349460101 (6 : ZMod 26201610349460101)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 2), (23753, 1), (1225651513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 2), (23753, 1), (1225651513, 1)] : List FactorBlock).map factorBlockValue).prod) = 26201610349460101 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_5
      · exact prime_oneHundredTwentyOneDO_23753
      · exact prime_oneHundredTwentyOneDO_1225651513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 26201610349460101) ^ 13100805174730050 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (6 : ZMod 26201610349460101) ^ 8733870116486700 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (6 : ZMod 26201610349460101) ^ 5240322069892020 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (6 : ZMod 26201610349460101) ^ 1103086361700 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (6 : ZMod 26201610349460101) ^ 21377700 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_36149342127088153 : Nat.Prime 36149342127088153 := by
  apply lucas_primality 36149342127088153 (7 : ZMod 36149342127088153)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (47, 1), (34301, 1), (934296059, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (47, 1), (34301, 1), (934296059, 1)] : List FactorBlock).map factorBlockValue).prod) = 36149342127088153 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_47
      · exact prime_oneHundredTwentyOneDO_34301
      · exact prime_oneHundredTwentyOneDO_934296059
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 36149342127088153) ^ 18074671063544076 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (7 : ZMod 36149342127088153) ^ 12049780709029384 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (7 : ZMod 36149342127088153) ^ 769134938874216 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (7 : ZMod 36149342127088153) ^ 1053885954552 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (7 : ZMod 36149342127088153) ^ 38691528 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_42626166499619117 : Nat.Prime 42626166499619117 := by
  apply lucas_primality 42626166499619117 (2 : ZMod 42626166499619117)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (10656541624904779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (10656541624904779, 1)] : List FactorBlock).map factorBlockValue).prod) = 42626166499619117 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_10656541624904779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 42626166499619117) ^ 21313083249809558 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 42626166499619117) ^ 4 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_64955883383770747 : Nat.Prime 64955883383770747 := by
  apply lucas_primality 64955883383770747 (2 : ZMod 64955883383770747)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (795253, 1), (13613253347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (795253, 1), (13613253347, 1)] : List FactorBlock).map factorBlockValue).prod) = 64955883383770747 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_795253
      · exact prime_oneHundredTwentyOneDO_13613253347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 64955883383770747) ^ 32477941691885373 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 64955883383770747) ^ 21651961127923582 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 64955883383770747) ^ 81679520082 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 64955883383770747) ^ 4771518 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_71274230068136971 : Nat.Prime 71274230068136971 := by
  apply lucas_primality 71274230068136971 (2 : ZMod 71274230068136971)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 2), (67, 1), (2239, 1), (2803, 1), (115309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 2), (67, 1), (2239, 1), (2803, 1), (115309, 1)] : List FactorBlock).map factorBlockValue).prod) = 71274230068136971 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_5
      · exact prime_oneHundredTwentyOneDO_7
      · exact prime_oneHundredTwentyOneDO_67
      · exact prime_oneHundredTwentyOneDO_2239
      · exact prime_oneHundredTwentyOneDO_2803
      · exact prime_oneHundredTwentyOneDO_115309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 71274230068136971) ^ 35637115034068485 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 71274230068136971) ^ 23758076689378990 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 71274230068136971) ^ 14254846013627394 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 71274230068136971) ^ 10182032866876710 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 71274230068136971) ^ 1063794478628910 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 71274230068136971) ^ 31833063898230 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 71274230068136971) ^ 25427838054990 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 71274230068136971) ^ 618115065330 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_78511797954027271 : Nat.Prime 78511797954027271 := by
  apply lucas_primality 78511797954027271 (3 : ZMod 78511797954027271)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 1), (3457, 1), (8263, 1), (4362719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 1), (3457, 1), (8263, 1), (4362719, 1)] : List FactorBlock).map factorBlockValue).prod) = 78511797954027271 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_5
      · exact prime_oneHundredTwentyOneDO_7
      · exact prime_oneHundredTwentyOneDO_3457
      · exact prime_oneHundredTwentyOneDO_8263
      · exact prime_oneHundredTwentyOneDO_4362719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 78511797954027271) ^ 39255898977013635 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 78511797954027271) ^ 26170599318009090 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 78511797954027271) ^ 15702359590805454 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 78511797954027271) ^ 11215971136289610 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 78511797954027271) ^ 22710962671110 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 78511797954027271) ^ 9501609337290 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 78511797954027271) ^ 17996070330 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_80294781734595371 : Nat.Prime 80294781734595371 := by
  apply lucas_primality 80294781734595371 (2 : ZMod 80294781734595371)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (10909627, 1), (735999331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (10909627, 1), (735999331, 1)] : List FactorBlock).map factorBlockValue).prod) = 80294781734595371 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_5
      · exact prime_oneHundredTwentyOneDO_10909627
      · exact prime_oneHundredTwentyOneDO_735999331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 80294781734595371) ^ 40147390867297685 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 80294781734595371) ^ 16058956346919074 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 80294781734595371) ^ 7359993310 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 80294781734595371) ^ 109096270 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_95954142887642339 : Nat.Prime 95954142887642339 := by
  apply lucas_primality 95954142887642339 (2 : ZMod 95954142887642339)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 2), (83, 1), (3420337309747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 2), (83, 1), (3420337309747, 1)] : List FactorBlock).map factorBlockValue).prod) = 95954142887642339 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_13
      · exact prime_oneHundredTwentyOneDO_83
      · exact prime_oneHundredTwentyOneDO_3420337309747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 95954142887642339) ^ 47977071443821169 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 95954142887642339) ^ 7381087914434026 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 95954142887642339) ^ 1156074010694486 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 95954142887642339) ^ 28054 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_118989061972089761 : Nat.Prime 118989061972089761 := by
  apply lucas_primality 118989061972089761 (3 : ZMod 118989061972089761)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (11, 1), (67607421575051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (11, 1), (67607421575051, 1)] : List FactorBlock).map factorBlockValue).prod) = 118989061972089761 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_5
      · exact prime_oneHundredTwentyOneDO_11
      · exact prime_oneHundredTwentyOneDO_67607421575051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 118989061972089761) ^ 59494530986044880 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 118989061972089761) ^ 23797812394417952 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 118989061972089761) ^ 10817187452008160 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 118989061972089761) ^ 1760 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_127937937640211957 : Nat.Prime 127937937640211957 := by
  apply lucas_primality 127937937640211957 (2 : ZMod 127937937640211957)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17047, 1), (1876252971787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17047, 1), (1876252971787, 1)] : List FactorBlock).map factorBlockValue).prod) = 127937937640211957 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_17047
      · exact prime_oneHundredTwentyOneDO_1876252971787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 127937937640211957) ^ 63968968820105978 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 127937937640211957) ^ 7505011887148 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 127937937640211957) ^ 68188 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_165635447035832771 : Nat.Prime 165635447035832771 := by
  apply lucas_primality 165635447035832771 (2 : ZMod 165635447035832771)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (23, 1), (47, 1), (9067, 1), (1689911551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (23, 1), (47, 1), (9067, 1), (1689911551, 1)] : List FactorBlock).map factorBlockValue).prod) = 165635447035832771 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_5
      · exact prime_oneHundredTwentyOneDO_23
      · exact prime_oneHundredTwentyOneDO_47
      · exact prime_oneHundredTwentyOneDO_9067
      · exact prime_oneHundredTwentyOneDO_1689911551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 165635447035832771) ^ 82817723517916385 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 165635447035832771) ^ 33127089407166554 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 165635447035832771) ^ 7201541175470990 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 165635447035832771) ^ 3524158447570910 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 165635447035832771) ^ 18267943866310 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 165635447035832771) ^ 98014270 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_259823533535082989 : Nat.Prime 259823533535082989 := by
  apply lucas_primality 259823533535082989 (2 : ZMod 259823533535082989)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (64955883383770747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (64955883383770747, 1)] : List FactorBlock).map factorBlockValue).prod) = 259823533535082989 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_64955883383770747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 259823533535082989) ^ 129911766767541494 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 259823533535082989) ^ 4 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_335714946508128767 : Nat.Prime 335714946508128767 := by
  apply lucas_primality 335714946508128767 (5 : ZMod 335714946508128767)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (83, 1), (6761, 1), (299124270941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (83, 1), (6761, 1), (299124270941, 1)] : List FactorBlock).map factorBlockValue).prod) = 335714946508128767 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_83
      · exact prime_oneHundredTwentyOneDO_6761
      · exact prime_oneHundredTwentyOneDO_299124270941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 335714946508128767) ^ 167857473254064383 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 335714946508128767) ^ 4044758391664202 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 335714946508128767) ^ 49654628976206 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 335714946508128767) ^ 1122326 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_373341079970251621 : Nat.Prime 373341079970251621 := by
  apply lucas_primality 373341079970251621 (6 : ZMod 373341079970251621)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (29, 1), (10753, 1), (19953858371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (29, 1), (10753, 1), (19953858371, 1)] : List FactorBlock).map factorBlockValue).prod) = 373341079970251621 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_5
      · exact prime_oneHundredTwentyOneDO_29
      · exact prime_oneHundredTwentyOneDO_10753
      · exact prime_oneHundredTwentyOneDO_19953858371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 373341079970251621) ^ 186670539985125810 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (6 : ZMod 373341079970251621) ^ 124447026656750540 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (6 : ZMod 373341079970251621) ^ 74668215994050324 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (6 : ZMod 373341079970251621) ^ 12873830343801780 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (6 : ZMod 373341079970251621) ^ 34719713565540 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (6 : ZMod 373341079970251621) ^ 18710220 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_394161934691576669 : Nat.Prime 394161934691576669 := by
  apply lucas_primality 394161934691576669 (2 : ZMod 394161934691576669)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (34537, 1), (2853185964991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (34537, 1), (2853185964991, 1)] : List FactorBlock).map factorBlockValue).prod) = 394161934691576669 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_34537
      · exact prime_oneHundredTwentyOneDO_2853185964991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 394161934691576669) ^ 197080967345788334 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 394161934691576669) ^ 11412743859964 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 394161934691576669) ^ 138148 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_411202968274753859 : Nat.Prime 411202968274753859 := by
  apply lucas_primality 411202968274753859 (2 : ZMod 411202968274753859)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (163207943, 1), (179964529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (163207943, 1), (179964529, 1)] : List FactorBlock).map factorBlockValue).prod) = 411202968274753859 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_7
      · exact prime_oneHundredTwentyOneDO_163207943
      · exact prime_oneHundredTwentyOneDO_179964529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 411202968274753859) ^ 205601484137376929 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 411202968274753859) ^ 58743281182107694 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 411202968274753859) ^ 2519503406 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 411202968274753859) ^ 2284911202 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_949510675980847217 : Nat.Prime 949510675980847217 := by
  apply lucas_primality 949510675980847217 (3 : ZMod 949510675980847217)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (738317, 1), (80377964003, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (738317, 1), (80377964003, 1)] : List FactorBlock).map factorBlockValue).prod) = 949510675980847217 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_738317
      · exact prime_oneHundredTwentyOneDO_80377964003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 949510675980847217) ^ 474755337990423608 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 949510675980847217) ^ 1286047424048 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 949510675980847217) ^ 11813072 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_1032309899567240527 : Nat.Prime 1032309899567240527 := by
  apply lucas_primality 1032309899567240527 (3 : ZMod 1032309899567240527)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (109022593, 1), (526042799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (109022593, 1), (526042799, 1)] : List FactorBlock).map factorBlockValue).prod) = 1032309899567240527 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_109022593
      · exact prime_oneHundredTwentyOneDO_526042799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1032309899567240527) ^ 516154949783620263 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1032309899567240527) ^ 344103299855746842 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1032309899567240527) ^ 9468770382 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1032309899567240527) ^ 1962406674 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_1109188763774599357 : Nat.Prime 1109188763774599357 := by
  apply lucas_primality 1109188763774599357 (5 : ZMod 1109188763774599357)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (59, 1), (89, 1), (199, 1), (29485457179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (59, 1), (89, 1), (199, 1), (29485457179, 1)] : List FactorBlock).map factorBlockValue).prod) = 1109188763774599357 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_59
      · exact prime_oneHundredTwentyOneDO_89
      · exact prime_oneHundredTwentyOneDO_199
      · exact prime_oneHundredTwentyOneDO_29485457179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1109188763774599357) ^ 554594381887299678 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 1109188763774599357) ^ 369729587924866452 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 1109188763774599357) ^ 18799809555501684 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 1109188763774599357) ^ 12462795098591004 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 1109188763774599357) ^ 5573812883289444 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 1109188763774599357) ^ 37618164 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_3289623746198030873 : Nat.Prime 3289623746198030873 := by
  apply lucas_primality 3289623746198030873 (3 : ZMod 3289623746198030873)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (411202968274753859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (411202968274753859, 1)] : List FactorBlock).map factorBlockValue).prod) = 3289623746198030873 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_411202968274753859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 3289623746198030873) ^ 1644811873099015436 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 3289623746198030873) ^ 8 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_3291288164488260637 : Nat.Prime 3291288164488260637 := by
  apply lucas_primality 3291288164488260637 (5 : ZMod 3291288164488260637)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (89, 1), (647, 1), (273083, 1), (2491711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (89, 1), (647, 1), (273083, 1), (2491711, 1)] : List FactorBlock).map factorBlockValue).prod) = 3291288164488260637 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_7
      · exact prime_oneHundredTwentyOneDO_89
      · exact prime_oneHundredTwentyOneDO_647
      · exact prime_oneHundredTwentyOneDO_273083
      · exact prime_oneHundredTwentyOneDO_2491711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 3291288164488260637) ^ 1645644082244130318 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 3291288164488260637) ^ 1097096054829420212 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 3291288164488260637) ^ 470184023498322948 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 3291288164488260637) ^ 36980765893126524 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 3291288164488260637) ^ 5086998708637188 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 3291288164488260637) ^ 12052336339092 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 3291288164488260637) ^ 1320894824676 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_5846096868441986491 : Nat.Prime 5846096868441986491 := by
  apply lucas_primality 5846096868441986491 (11 : ZMod 5846096868441986491)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (19, 1), (13183, 1), (28559, 1), (27241681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (19, 1), (13183, 1), (28559, 1), (27241681, 1)] : List FactorBlock).map factorBlockValue).prod) = 5846096868441986491 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_5
      · exact prime_oneHundredTwentyOneDO_19
      · exact prime_oneHundredTwentyOneDO_13183
      · exact prime_oneHundredTwentyOneDO_28559
      · exact prime_oneHundredTwentyOneDO_27241681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 5846096868441986491) ^ 2923048434220993245 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (11 : ZMod 5846096868441986491) ^ 1948698956147328830 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (11 : ZMod 5846096868441986491) ^ 1169219373688397298 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (11 : ZMod 5846096868441986491) ^ 307689308865367710 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (11 : ZMod 5846096868441986491) ^ 443457245577030 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (11 : ZMod 5846096868441986491) ^ 204702435955110 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (11 : ZMod 5846096868441986491) ^ 214601179290 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_6118625208737008441 : Nat.Prime 6118625208737008441 := by
  apply lucas_primality 6118625208737008441 (7 : ZMod 6118625208737008441)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (11, 1), (787, 1), (6451, 1), (304338497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (11, 1), (787, 1), (6451, 1), (304338497, 1)] : List FactorBlock).map factorBlockValue).prod) = 6118625208737008441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_5
      · exact prime_oneHundredTwentyOneDO_11
      · exact prime_oneHundredTwentyOneDO_787
      · exact prime_oneHundredTwentyOneDO_6451
      · exact prime_oneHundredTwentyOneDO_304338497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 6118625208737008441) ^ 3059312604368504220 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (7 : ZMod 6118625208737008441) ^ 2039541736245669480 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (7 : ZMod 6118625208737008441) ^ 1223725041747401688 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (7 : ZMod 6118625208737008441) ^ 556238655339728040 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (7 : ZMod 6118625208737008441) ^ 7774619070822120 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (7 : ZMod 6118625208737008441) ^ 948477012670440 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (7 : ZMod 6118625208737008441) ^ 20104670520 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_10301656832607448111 : Nat.Prime 10301656832607448111 := by
  apply lucas_primality 10301656832607448111 (3 : ZMod 10301656832607448111)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (23, 1), (103, 1), (239, 1), (307, 1), (179593991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (23, 1), (103, 1), (239, 1), (307, 1), (179593991, 1)] : List FactorBlock).map factorBlockValue).prod) = 10301656832607448111 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_5
      · exact prime_oneHundredTwentyOneDO_11
      · exact prime_oneHundredTwentyOneDO_23
      · exact prime_oneHundredTwentyOneDO_103
      · exact prime_oneHundredTwentyOneDO_239
      · exact prime_oneHundredTwentyOneDO_307
      · exact prime_oneHundredTwentyOneDO_179593991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 10301656832607448111) ^ 5150828416303724055 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 10301656832607448111) ^ 3433885610869149370 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 10301656832607448111) ^ 2060331366521489622 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 10301656832607448111) ^ 936514257509768010 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 10301656832607448111) ^ 447898123156845570 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 10301656832607448111) ^ 100016085753470370 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 10301656832607448111) ^ 43103166663629490 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 10301656832607448111) ^ 33555885448232730 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 10301656832607448111) ^ 57360810210 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_24372352293461154107 : Nat.Prime 24372352293461154107 := by
  apply lucas_primality 24372352293461154107 (2 : ZMod 24372352293461154107)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (127, 1), (95954142887642339, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (127, 1), (95954142887642339, 1)] : List FactorBlock).map factorBlockValue).prod) = 24372352293461154107 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_127
      · exact prime_oneHundredTwentyOneDO_95954142887642339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 24372352293461154107) ^ 12186176146730577053 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 24372352293461154107) ^ 191908285775284678 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 24372352293461154107) ^ 254 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_92466215604885683747 : Nat.Prime 92466215604885683747 := by
  apply lucas_primality 92466215604885683747 (5 : ZMod 92466215604885683747)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (140945263, 1), (14261813977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (140945263, 1), (14261813977, 1)] : List FactorBlock).map factorBlockValue).prod) = 92466215604885683747 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_23
      · exact prime_oneHundredTwentyOneDO_140945263
      · exact prime_oneHundredTwentyOneDO_14261813977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 92466215604885683747) ^ 46233107802442841873 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 92466215604885683747) ^ 4020270243690681902 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 92466215604885683747) ^ 656043442942 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 92466215604885683747) ^ 6483482098 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_263025112294685047009 : Nat.Prime 263025112294685047009 := by
  apply lucas_primality 263025112294685047009 (7 : ZMod 263025112294685047009)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (13, 1), (1907, 1), (110517724970203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (13, 1), (1907, 1), (110517724970203, 1)] : List FactorBlock).map factorBlockValue).prod) = 263025112294685047009 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_13
      · exact prime_oneHundredTwentyOneDO_1907
      · exact prime_oneHundredTwentyOneDO_110517724970203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 263025112294685047009) ^ 131512556147342523504 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (7 : ZMod 263025112294685047009) ^ 87675037431561682336 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (7 : ZMod 263025112294685047009) ^ 20232700945745003616 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (7 : ZMod 263025112294685047009) ^ 137926120762813344 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (7 : ZMod 263025112294685047009) ^ 2379936 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_266796789051514876837 : Nat.Prime 266796789051514876837 := by
  apply lucas_primality 266796789051514876837 (5 : ZMod 266796789051514876837)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (19, 1), (103, 1), (1032799078101589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (19, 1), (103, 1), (1032799078101589, 1)] : List FactorBlock).map factorBlockValue).prod) = 266796789051514876837 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_11
      · exact prime_oneHundredTwentyOneDO_19
      · exact prime_oneHundredTwentyOneDO_103
      · exact prime_oneHundredTwentyOneDO_1032799078101589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 266796789051514876837) ^ 133398394525757438418 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 266796789051514876837) ^ 88932263017171625612 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 266796789051514876837) ^ 24254253550137716076 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 266796789051514876837) ^ 14041936265869204044 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 266796789051514876837) ^ 2590260087878785212 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 266796789051514876837) ^ 258324 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_1101612939162985290631 : Nat.Prime 1101612939162985290631 := by
  apply lucas_primality 1101612939162985290631 (7 : ZMod 1101612939162985290631)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (67979, 1), (540173160908999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (67979, 1), (540173160908999, 1)] : List FactorBlock).map factorBlockValue).prod) = 1101612939162985290631 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_5
      · exact prime_oneHundredTwentyOneDO_67979
      · exact prime_oneHundredTwentyOneDO_540173160908999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1101612939162985290631) ^ 550806469581492645315 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (7 : ZMod 1101612939162985290631) ^ 367204313054328430210 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (7 : ZMod 1101612939162985290631) ^ 220322587832597058126 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (7 : ZMod 1101612939162985290631) ^ 16205194827269970 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (7 : ZMod 1101612939162985290631) ^ 2039370 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_1118460645412107453821 : Nat.Prime 1118460645412107453821 := by
  apply lucas_primality 1118460645412107453821 (3 : ZMod 1118460645412107453821)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (13, 1), (17, 1), (36149342127088153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (13, 1), (17, 1), (36149342127088153, 1)] : List FactorBlock).map factorBlockValue).prod) = 1118460645412107453821 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_5
      · exact prime_oneHundredTwentyOneDO_7
      · exact prime_oneHundredTwentyOneDO_13
      · exact prime_oneHundredTwentyOneDO_17
      · exact prime_oneHundredTwentyOneDO_36149342127088153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1118460645412107453821) ^ 559230322706053726910 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1118460645412107453821) ^ 223692129082421490764 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1118460645412107453821) ^ 159780092201729636260 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1118460645412107453821) ^ 86035434262469804140 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1118460645412107453821) ^ 65791802671300438460 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1118460645412107453821) ^ 30940 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_1550411355806685423811 : Nat.Prime 1550411355806685423811 := by
  apply lucas_primality 1550411355806685423811 (2 : ZMod 1550411355806685423811)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (11, 1), (3283807, 1), (476907466417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (11, 1), (3283807, 1), (476907466417, 1)] : List FactorBlock).map factorBlockValue).prod) = 1550411355806685423811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_5
      · exact prime_oneHundredTwentyOneDO_11
      · exact prime_oneHundredTwentyOneDO_3283807
      · exact prime_oneHundredTwentyOneDO_476907466417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1550411355806685423811) ^ 775205677903342711905 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1550411355806685423811) ^ 516803785268895141270 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1550411355806685423811) ^ 310082271161337084762 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1550411355806685423811) ^ 140946486891516856710 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1550411355806685423811) ^ 472138391752830 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1550411355806685423811) ^ 3250968930 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_2303086321197366638341 : Nat.Prime 2303086321197366638341 := by
  apply lucas_primality 2303086321197366638341 (2 : ZMod 2303086321197366638341)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (11, 2), (23, 1), (424001, 1), (32529611633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (11, 2), (23, 1), (424001, 1), (32529611633, 1)] : List FactorBlock).map factorBlockValue).prod) = 2303086321197366638341 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_5
      · exact prime_oneHundredTwentyOneDO_11
      · exact prime_oneHundredTwentyOneDO_23
      · exact prime_oneHundredTwentyOneDO_424001
      · exact prime_oneHundredTwentyOneDO_32529611633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2303086321197366638341) ^ 1151543160598683319170 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2303086321197366638341) ^ 767695440399122212780 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2303086321197366638341) ^ 460617264239473327668 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2303086321197366638341) ^ 209371483745215148940 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2303086321197366638341) ^ 100134187878146375580 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2303086321197366638341) ^ 5431794550478340 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2303086321197366638341) ^ 70799686980 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_5987115218080416188861 : Nat.Prime 5987115218080416188861 := by
  apply lucas_primality 5987115218080416188861 (2 : ZMod 5987115218080416188861)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (13, 1), (3289623746198030873, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (13, 1), (3289623746198030873, 1)] : List FactorBlock).map factorBlockValue).prod) = 5987115218080416188861 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_5
      · exact prime_oneHundredTwentyOneDO_7
      · exact prime_oneHundredTwentyOneDO_13
      · exact prime_oneHundredTwentyOneDO_3289623746198030873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5987115218080416188861) ^ 2993557609040208094430 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 5987115218080416188861) ^ 1197423043616083237772 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 5987115218080416188861) ^ 855302174011488026980 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 5987115218080416188861) ^ 460547324467724322220 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 5987115218080416188861) ^ 1820 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_6154578097571874053399 : Nat.Prime 6154578097571874053399 := by
  apply lucas_primality 6154578097571874053399 (7 : ZMod 6154578097571874053399)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (25381789, 1), (17320005349313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (25381789, 1), (17320005349313, 1)] : List FactorBlock).map factorBlockValue).prod) = 6154578097571874053399 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_7
      · exact prime_oneHundredTwentyOneDO_25381789
      · exact prime_oneHundredTwentyOneDO_17320005349313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 6154578097571874053399) ^ 3077289048785937026699 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (7 : ZMod 6154578097571874053399) ^ 879225442510267721914 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (7 : ZMod 6154578097571874053399) ^ 242480074890382 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (7 : ZMod 6154578097571874053399) ^ 355345046 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_7035874109018077877971 : Nat.Prime 7035874109018077877971 := by
  apply lucas_primality 7035874109018077877971 (3 : ZMod 7035874109018077877971)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (13, 1), (19, 1), (949510675980847217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (13, 1), (19, 1), (949510675980847217, 1)] : List FactorBlock).map factorBlockValue).prod) = 7035874109018077877971 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_5
      · exact prime_oneHundredTwentyOneDO_13
      · exact prime_oneHundredTwentyOneDO_19
      · exact prime_oneHundredTwentyOneDO_949510675980847217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 7035874109018077877971) ^ 3517937054509038938985 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 7035874109018077877971) ^ 2345291369672692625990 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 7035874109018077877971) ^ 1407174821803615575594 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 7035874109018077877971) ^ 541221085309082913690 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 7035874109018077877971) ^ 370309163632530414630 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 7035874109018077877971) ^ 7410 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_25342560366176432379269 : Nat.Prime 25342560366176432379269 := by
  apply lucas_primality 25342560366176432379269 (2 : ZMod 25342560366176432379269)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (379, 1), (19150853, 1), (872897331191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (379, 1), (19150853, 1), (872897331191, 1)] : List FactorBlock).map factorBlockValue).prod) = 25342560366176432379269 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_379
      · exact prime_oneHundredTwentyOneDO_19150853
      · exact prime_oneHundredTwentyOneDO_872897331191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 25342560366176432379269) ^ 12671280183088216189634 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 25342560366176432379269) ^ 66866913894924623692 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 25342560366176432379269) ^ 1323312354085556 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 25342560366176432379269) ^ 29032693148 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_33023467536964516184101 : Nat.Prime 33023467536964516184101 := by
  apply lucas_primality 33023467536964516184101 (10 : ZMod 33023467536964516184101)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (11, 2), (17, 1), (43, 1), (1244510803984297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (11, 2), (17, 1), (43, 1), (1244510803984297, 1)] : List FactorBlock).map factorBlockValue).prod) = 33023467536964516184101 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_5
      · exact prime_oneHundredTwentyOneDO_11
      · exact prime_oneHundredTwentyOneDO_17
      · exact prime_oneHundredTwentyOneDO_43
      · exact prime_oneHundredTwentyOneDO_1244510803984297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 33023467536964516184101) ^ 16511733768482258092050 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (10 : ZMod 33023467536964516184101) ^ 11007822512321505394700 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (10 : ZMod 33023467536964516184101) ^ 6604693507392903236820 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (10 : ZMod 33023467536964516184101) ^ 3002133412451319653100 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (10 : ZMod 33023467536964516184101) ^ 1942556913939089187300 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (10 : ZMod 33023467536964516184101) ^ 767987617138709678700 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (10 : ZMod 33023467536964516184101) ^ 26535300 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_35853529750253765128927 : Nat.Prime 35853529750253765128927 := by
  apply lucas_primality 35853529750253765128927 (3 : ZMod 35853529750253765128927)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (17, 1), (71, 1), (8317, 1), (66139999399751, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (17, 1), (71, 1), (8317, 1), (66139999399751, 1)] : List FactorBlock).map factorBlockValue).prod) = 35853529750253765128927 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_17
      · exact prime_oneHundredTwentyOneDO_71
      · exact prime_oneHundredTwentyOneDO_8317
      · exact prime_oneHundredTwentyOneDO_66139999399751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 35853529750253765128927) ^ 17926764875126882564463 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 35853529750253765128927) ^ 11951176583417921709642 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 35853529750253765128927) ^ 2109031161779633242878 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 35853529750253765128927) ^ 504979292257095283506 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 35853529750253765128927) ^ 4310872880876970678 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 35853529750253765128927) ^ 542085426 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_165357363442891885455317 : Nat.Prime 165357363442891885455317 := by
  apply lucas_primality 165357363442891885455317 (2 : ZMod 165357363442891885455317)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (5151077749, 1), (1146482427703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (5151077749, 1), (1146482427703, 1)] : List FactorBlock).map factorBlockValue).prod) = 165357363442891885455317 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_7
      · exact prime_oneHundredTwentyOneDO_5151077749
      · exact prime_oneHundredTwentyOneDO_1146482427703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 165357363442891885455317) ^ 82678681721445942727658 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 165357363442891885455317) ^ 23622480491841697922188 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 165357363442891885455317) ^ 32101507975684 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 165357363442891885455317) ^ 144230176972 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_192382775737826003680613 : Nat.Prime 192382775737826003680613 := by
  apply lucas_primality 192382775737826003680613 (2 : ZMod 192382775737826003680613)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (139, 1), (1021, 1), (13901, 1), (26321, 1), (926226547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (139, 1), (1021, 1), (13901, 1), (26321, 1), (926226547, 1)] : List FactorBlock).map factorBlockValue).prod) = 192382775737826003680613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_139
      · exact prime_oneHundredTwentyOneDO_1021
      · exact prime_oneHundredTwentyOneDO_13901
      · exact prime_oneHundredTwentyOneDO_26321
      · exact prime_oneHundredTwentyOneDO_926226547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 192382775737826003680613) ^ 96191387868913001840306 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 192382775737826003680613) ^ 1384048746315294990508 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 192382775737826003680613) ^ 188425833239790405172 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 192382775737826003680613) ^ 13839491816259693812 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 192382775737826003680613) ^ 7309098276578625572 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 192382775737826003680613) ^ 207705961744396 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_215121178501522590773563 : Nat.Prime 215121178501522590773563 := by
  apply lucas_primality 215121178501522590773563 (2 : ZMod 215121178501522590773563)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (35853529750253765128927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (35853529750253765128927, 1)] : List FactorBlock).map factorBlockValue).prod) = 215121178501522590773563 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_35853529750253765128927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 215121178501522590773563) ^ 107560589250761295386781 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 215121178501522590773563) ^ 71707059500507530257854 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 215121178501522590773563) ^ 6 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_384765551475652007361227 : Nat.Prime 384765551475652007361227 := by
  apply lucas_primality 384765551475652007361227 (2 : ZMod 384765551475652007361227)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (192382775737826003680613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (192382775737826003680613, 1)] : List FactorBlock).map factorBlockValue).prod) = 384765551475652007361227 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_192382775737826003680613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 384765551475652007361227) ^ 192382775737826003680613 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 384765551475652007361227) ^ 2 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_634984078053165342711883 : Nat.Prime 634984078053165342711883 := by
  apply lucas_primality 634984078053165342711883 (2 : ZMod 634984078053165342711883)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (23, 1), (514001, 1), (526587885894017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (23, 1), (514001, 1), (526587885894017, 1)] : List FactorBlock).map factorBlockValue).prod) = 634984078053165342711883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_17
      · exact prime_oneHundredTwentyOneDO_23
      · exact prime_oneHundredTwentyOneDO_514001
      · exact prime_oneHundredTwentyOneDO_526587885894017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 634984078053165342711883) ^ 317492039026582671355941 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 634984078053165342711883) ^ 211661359351055114237294 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 634984078053165342711883) ^ 37352004591362667218346 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 634984078053165342711883) ^ 27608003393615884465734 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 634984078053165342711883) ^ 1235375180307363882 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 634984078053165342711883) ^ 1205846346 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_2304688066511599840970417 : Nat.Prime 2304688066511599840970417 := by
  apply lucas_primality 2304688066511599840970417 (3 : ZMod 2304688066511599840970417)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (349, 2), (1399, 1), (120760683377107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (349, 2), (1399, 1), (120760683377107, 1)] : List FactorBlock).map factorBlockValue).prod) = 2304688066511599840970417 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_7
      · exact prime_oneHundredTwentyOneDO_349
      · exact prime_oneHundredTwentyOneDO_1399
      · exact prime_oneHundredTwentyOneDO_120760683377107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2304688066511599840970417) ^ 1152344033255799920485208 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 2304688066511599840970417) ^ 329241152358799977281488 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 2304688066511599840970417) ^ 6603690734990257423984 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 2304688066511599840970417) ^ 1647382463553681087184 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 2304688066511599840970417) ^ 19084755088 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_2539936312212661370847533 : Nat.Prime 2539936312212661370847533 := by
  apply lucas_primality 2539936312212661370847533 (2 : ZMod 2539936312212661370847533)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (634984078053165342711883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (634984078053165342711883, 1)] : List FactorBlock).map factorBlockValue).prod) = 2539936312212661370847533 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_634984078053165342711883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 2539936312212661370847533) ^ 1269968156106330685423766 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2539936312212661370847533) ^ 4 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_4515317624406335260680347 : Nat.Prime 4515317624406335260680347 := by
  apply lucas_primality 4515317624406335260680347 (2 : ZMod 4515317624406335260680347)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 1), (83, 1), (107, 1), (1069, 1), (3881, 1), (1424973002779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 1), (83, 1), (107, 1), (1069, 1), (3881, 1), (1424973002779, 1)] : List FactorBlock).map factorBlockValue).prod) = 4515317624406335260680347 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_43
      · exact prime_oneHundredTwentyOneDO_83
      · exact prime_oneHundredTwentyOneDO_107
      · exact prime_oneHundredTwentyOneDO_1069
      · exact prime_oneHundredTwentyOneDO_3881
      · exact prime_oneHundredTwentyOneDO_1424973002779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4515317624406335260680347) ^ 2257658812203167630340173 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 4515317624406335260680347) ^ 105007386614100820015822 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 4515317624406335260680347) ^ 54401417161522111574462 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 4515317624406335260680347) ^ 42199230134638647296078 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 4515317624406335260680347) ^ 4223870556039602676034 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 4515317624406335260680347) ^ 1163441799640900608266 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 4515317624406335260680347) ^ 3168703979374 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_7344780663163809299629037 : Nat.Prime 7344780663163809299629037 := by
  apply lucas_primality 7344780663163809299629037 (2 : ZMod 7344780663163809299629037)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (67, 1), (4223612929, 1), (6488733332713, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (67, 1), (4223612929, 1), (6488733332713, 1)] : List FactorBlock).map factorBlockValue).prod) = 7344780663163809299629037 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_67
      · exact prime_oneHundredTwentyOneDO_4223612929
      · exact prime_oneHundredTwentyOneDO_6488733332713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7344780663163809299629037) ^ 3672390331581904649814518 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 7344780663163809299629037) ^ 109623591987519541785508 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 7344780663163809299629037) ^ 1738980533167084 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 7344780663163809299629037) ^ 1131928264972 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_21977921796964435970022239 : Nat.Prime 21977921796964435970022239 := by
  apply lucas_primality 21977921796964435970022239 (22 : ZMod 21977921796964435970022239)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (144593, 1), (5846096868441986491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (144593, 1), (5846096868441986491, 1)] : List FactorBlock).map factorBlockValue).prod) = 21977921796964435970022239 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_13
      · exact prime_oneHundredTwentyOneDO_144593
      · exact prime_oneHundredTwentyOneDO_5846096868441986491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (22 : ZMod 21977921796964435970022239) ^ 10988960898482217985011119 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (22 : ZMod 21977921796964435970022239) ^ 1690609368997264305386326 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (22 : ZMod 21977921796964435970022239) ^ 151998518579491648766 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (22 : ZMod 21977921796964435970022239) ^ 3759418 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_49329066543600521975474053 : Nat.Prime 49329066543600521975474053 := by
  apply lucas_primality 49329066543600521975474053 (2 : ZMod 49329066543600521975474053)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (2089, 1), (9203, 1), (71274230068136971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (2089, 1), (9203, 1), (71274230068136971, 1)] : List FactorBlock).map factorBlockValue).prod) = 49329066543600521975474053 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_2089
      · exact prime_oneHundredTwentyOneDO_9203
      · exact prime_oneHundredTwentyOneDO_71274230068136971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 49329066543600521975474053) ^ 24664533271800260987737026 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 49329066543600521975474053) ^ 16443022181200173991824684 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 49329066543600521975474053) ^ 23613722615414323588068 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 49329066543600521975474053) ^ 5360107198044172767084 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 49329066543600521975474053) ^ 692102412 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_49619942066056716520594781 : Nat.Prime 49619942066056716520594781 := by
  apply lucas_primality 49619942066056716520594781 (3 : ZMod 49619942066056716520594781)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (11, 1), (197, 1), (7528211, 1), (152081211294847, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (11, 1), (197, 1), (7528211, 1), (152081211294847, 1)] : List FactorBlock).map factorBlockValue).prod) = 49619942066056716520594781 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_5
      · exact prime_oneHundredTwentyOneDO_11
      · exact prime_oneHundredTwentyOneDO_197
      · exact prime_oneHundredTwentyOneDO_7528211
      · exact prime_oneHundredTwentyOneDO_152081211294847
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 49619942066056716520594781) ^ 24809971033028358260297390 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 49619942066056716520594781) ^ 9923988413211343304118956 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 49619942066056716520594781) ^ 4510903824186974229144980 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 49619942066056716520594781) ^ 251877878507902114317740 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 49619942066056716520594781) ^ 6591199697518668980 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 49619942066056716520594781) ^ 326272664740 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_62008796262003256926256937 : Nat.Prime 62008796262003256926256937 := by
  apply lucas_primality 62008796262003256926256937 (3 : ZMod 62008796262003256926256937)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (181839001, 1), (42626166499619117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (181839001, 1), (42626166499619117, 1)] : List FactorBlock).map factorBlockValue).prod) = 62008796262003256926256937 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_181839001
      · exact prime_oneHundredTwentyOneDO_42626166499619117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 62008796262003256926256937) ^ 31004398131001628463128468 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 62008796262003256926256937) ^ 341009331996952936 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 62008796262003256926256937) ^ 1454712008 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_71100543228847670839400971 : Nat.Prime 71100543228847670839400971 := by
  apply lucas_primality 71100543228847670839400971 (3 : ZMod 71100543228847670839400971)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (13, 1), (163, 1), (1118460645412107453821, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (13, 1), (163, 1), (1118460645412107453821, 1)] : List FactorBlock).map factorBlockValue).prod) = 71100543228847670839400971 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_5
      · exact prime_oneHundredTwentyOneDO_13
      · exact prime_oneHundredTwentyOneDO_163
      · exact prime_oneHundredTwentyOneDO_1118460645412107453821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 71100543228847670839400971) ^ 35550271614423835419700485 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 71100543228847670839400971) ^ 23700181076282556946466990 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 71100543228847670839400971) ^ 14220108645769534167880194 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 71100543228847670839400971) ^ 5469272556065205449184690 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 71100543228847670839400971) ^ 436199651710721906990190 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 71100543228847670839400971) ^ 63570 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_106044694571120469776778913 : Nat.Prime 106044694571120469776778913 := by
  apply lucas_primality 106044694571120469776778913 (5 : ZMod 106044694571120469776778913)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (157, 1), (7035874109018077877971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (157, 1), (7035874109018077877971, 1)] : List FactorBlock).map factorBlockValue).prod) = 106044694571120469776778913 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_157
      · exact prime_oneHundredTwentyOneDO_7035874109018077877971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 106044694571120469776778913) ^ 53022347285560234888389456 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 106044694571120469776778913) ^ 35348231523706823258926304 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 106044694571120469776778913) ^ 675443914465735476285216 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 106044694571120469776778913) ^ 15072 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_1265967194481783307335174811 : Nat.Prime 1265967194481783307335174811 := by
  apply lucas_primality 1265967194481783307335174811 (3 : ZMod 1265967194481783307335174811)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (31, 1), (623209, 1), (4351489, 1), (501958596917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (31, 1), (623209, 1), (4351489, 1), (501958596917, 1)] : List FactorBlock).map factorBlockValue).prod) = 1265967194481783307335174811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_5
      · exact prime_oneHundredTwentyOneDO_31
      · exact prime_oneHundredTwentyOneDO_623209
      · exact prime_oneHundredTwentyOneDO_4351489
      · exact prime_oneHundredTwentyOneDO_501958596917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1265967194481783307335174811) ^ 632983597240891653667587405 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1265967194481783307335174811) ^ 421989064827261102445058270 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1265967194481783307335174811) ^ 253193438896356661467034962 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1265967194481783307335174811) ^ 40837651434896235720489510 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1265967194481783307335174811) ^ 2031368601033976254090 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1265967194481783307335174811) ^ 290927357160223387290 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1265967194481783307335174811) ^ 2522055010626930 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_1625616965641380837828122201 : Nat.Prime 1625616965641380837828122201 := by
  apply lucas_primality 1625616965641380837828122201 (3 : ZMod 1625616965641380837828122201)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (11, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (11, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 1625616965641380837828122201 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_5
      · exact prime_oneHundredTwentyOneDO_11
      · exact prime_oneHundredTwentyOneDO_171401
      · exact prime_oneHundredTwentyOneDO_714027719
      · exact prime_oneHundredTwentyOneDO_6037638679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1625616965641380837828122201) ^ 812808482820690418914061100 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1625616965641380837828122201) ^ 325123393128276167565624440 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1625616965641380837828122201) ^ 147783360512852803438920200 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1625616965641380837828122201) ^ 9484291023047595042200 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1625616965641380837828122201) ^ 2276686075882413800 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1625616965641380837828122201) ^ 269247143141501800 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_6502467862565523351312488803 : Nat.Prime 6502467862565523351312488803 := by
  apply lucas_primality 6502467862565523351312488803 (2 : ZMod 6502467862565523351312488803)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (107, 1), (43001837, 1), (78511797954027271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (107, 1), (43001837, 1), (78511797954027271, 1)] : List FactorBlock).map factorBlockValue).prod) = 6502467862565523351312488803 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_107
      · exact prime_oneHundredTwentyOneDO_43001837
      · exact prime_oneHundredTwentyOneDO_78511797954027271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6502467862565523351312488803) ^ 3251233931282761675656244401 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 6502467862565523351312488803) ^ 2167489287521841117104162934 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 6502467862565523351312488803) ^ 60770727687528255619742886 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 6502467862565523351312488803) ^ 151213722859456523946 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 6502467862565523351312488803) ^ 82821538062 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_6812109189354357796613083507 : Nat.Prime 6812109189354357796613083507 := by
  apply lucas_primality 6812109189354357796613083507 (3 : ZMod 6812109189354357796613083507)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (149, 1), (2539936312212661370847533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (149, 1), (2539936312212661370847533, 1)] : List FactorBlock).map factorBlockValue).prod) = 6812109189354357796613083507 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_149
      · exact prime_oneHundredTwentyOneDO_2539936312212661370847533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6812109189354357796613083507) ^ 3406054594677178898306541753 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 6812109189354357796613083507) ^ 2270703063118119265537694502 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 6812109189354357796613083507) ^ 45718853619827904675255594 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 6812109189354357796613083507) ^ 2682 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_7947460720913417429381930759 : Nat.Prime 7947460720913417429381930759 := by
  apply lucas_primality 7947460720913417429381930759 (7 : ZMod 7947460720913417429381930759)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (107, 1), (43001837, 1), (78511797954027271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (107, 1), (43001837, 1), (78511797954027271, 1)] : List FactorBlock).map factorBlockValue).prod) = 7947460720913417429381930759 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_11
      · exact prime_oneHundredTwentyOneDO_107
      · exact prime_oneHundredTwentyOneDO_43001837
      · exact prime_oneHundredTwentyOneDO_78511797954027271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 7947460720913417429381930759) ^ 3973730360456708714690965379 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (7 : ZMod 7947460720913417429381930759) ^ 722496429173947039034720978 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (7 : ZMod 7947460720913417429381930759) ^ 74275333840312312424130194 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (7 : ZMod 7947460720913417429381930759) ^ 184816772383780195934 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (7 : ZMod 7947460720913417429381930759) ^ 101226324298 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_20436327568063073389839250523 : Nat.Prime 20436327568063073389839250523 := by
  apply lucas_primality 20436327568063073389839250523 (2 : ZMod 20436327568063073389839250523)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (73, 1), (4515317624406335260680347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (73, 1), (4515317624406335260680347, 1)] : List FactorBlock).map factorBlockValue).prod) = 20436327568063073389839250523 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_31
      · exact prime_oneHundredTwentyOneDO_73
      · exact prime_oneHundredTwentyOneDO_4515317624406335260680347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 20436327568063073389839250523) ^ 10218163784031536694919625261 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 20436327568063073389839250523) ^ 659236373163324948059330662 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 20436327568063073389839250523) ^ 279949692713192786162181514 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 20436327568063073389839250523) ^ 4526 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_23842382162740252288145792281 : Nat.Prime 23842382162740252288145792281 := by
  apply lucas_primality 23842382162740252288145792281 (11 : ZMod 23842382162740252288145792281)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (2029, 1), (33679313, 1), (969174263781499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (2029, 1), (33679313, 1), (969174263781499, 1)] : List FactorBlock).map factorBlockValue).prod) = 23842382162740252288145792281 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_5
      · exact prime_oneHundredTwentyOneDO_2029
      · exact prime_oneHundredTwentyOneDO_33679313
      · exact prime_oneHundredTwentyOneDO_969174263781499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 23842382162740252288145792281) ^ 11921191081370126144072896140 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (11 : ZMod 23842382162740252288145792281) ^ 7947460720913417429381930760 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (11 : ZMod 23842382162740252288145792281) ^ 4768476432548050457629158456 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (11 : ZMod 23842382162740252288145792281) ^ 11750804417319000634867320 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (11 : ZMod 23842382162740252288145792281) ^ 707923649236558129560 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (11 : ZMod 23842382162740252288145792281) ^ 24600717387720 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_28610858595288302745774950729 : Nat.Prime 28610858595288302745774950729 := by
  apply lucas_primality 28610858595288302745774950729 (3 : ZMod 28610858595288302745774950729)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (139, 1), (19753, 1), (354439, 1), (8837987, 1), (59401873, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (139, 1), (19753, 1), (354439, 1), (8837987, 1), (59401873, 1)] : List FactorBlock).map factorBlockValue).prod) = 28610858595288302745774950729 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_7
      · exact prime_oneHundredTwentyOneDO_139
      · exact prime_oneHundredTwentyOneDO_19753
      · exact prime_oneHundredTwentyOneDO_354439
      · exact prime_oneHundredTwentyOneDO_8837987
      · exact prime_oneHundredTwentyOneDO_59401873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 28610858595288302745774950729) ^ 14305429297644151372887475364 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 28610858595288302745774950729) ^ 4087265513612614677967850104 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 28610858595288302745774950729) ^ 205833515074016566516366552 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 28610858595288302745774950729) ^ 1448431053272328392941576 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 28610858595288302745774950729) ^ 80721530630907723884152 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 28610858595288302745774950729) ^ 3237259637889069393944 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (3 : ZMod 28610858595288302745774950729) ^ 481649098763069352136 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_35763573244110378432218688409 : Nat.Prime 35763573244110378432218688409 := by
  apply lucas_primality 35763573244110378432218688409 (7 : ZMod 35763573244110378432218688409)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (41, 1), (761, 1), (375327493, 1), (127247943062269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (41, 1), (761, 1), (375327493, 1), (127247943062269, 1)] : List FactorBlock).map factorBlockValue).prod) = 35763573244110378432218688409 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_41
      · exact prime_oneHundredTwentyOneDO_761
      · exact prime_oneHundredTwentyOneDO_375327493
      · exact prime_oneHundredTwentyOneDO_127247943062269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 35763573244110378432218688409) ^ 17881786622055189216109344204 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (7 : ZMod 35763573244110378432218688409) ^ 11921191081370126144072896136 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (7 : ZMod 35763573244110378432218688409) ^ 872282274246594595907772888 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (7 : ZMod 35763573244110378432218688409) ^ 46995497035624675995031128 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (7 : ZMod 35763573244110378432218688409) ^ 95286313715660521656 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (7 : ZMod 35763573244110378432218688409) ^ 281054234618232 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_71527146488220756864437376817 : Nat.Prime 71527146488220756864437376817 := by
  apply lucas_primality 71527146488220756864437376817 (15 : ZMod 71527146488220756864437376817)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (41, 1), (761, 1), (375327493, 1), (127247943062269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (41, 1), (761, 1), (375327493, 1), (127247943062269, 1)] : List FactorBlock).map factorBlockValue).prod) = 71527146488220756864437376817 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_41
      · exact prime_oneHundredTwentyOneDO_761
      · exact prime_oneHundredTwentyOneDO_375327493
      · exact prime_oneHundredTwentyOneDO_127247943062269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 71527146488220756864437376817) ^ 35763573244110378432218688408 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (15 : ZMod 71527146488220756864437376817) ^ 23842382162740252288145792272 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (15 : ZMod 71527146488220756864437376817) ^ 1744564548493189191815545776 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (15 : ZMod 71527146488220756864437376817) ^ 93990994071249351990062256 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (15 : ZMod 71527146488220756864437376817) ^ 190572627431321043312 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (15 : ZMod 71527146488220756864437376817) ^ 562108469236464 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_143054292976441513728874753609 : Nat.Prime 143054292976441513728874753609 := by
  apply lucas_primality 143054292976441513728874753609 (13 : ZMod 143054292976441513728874753609)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (15609343, 1), (65296087, 1), (1949380506329, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (15609343, 1), (65296087, 1), (1949380506329, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753609 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_15609343
      · exact prime_oneHundredTwentyOneDO_65296087
      · exact prime_oneHundredTwentyOneDO_1949380506329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 143054292976441513728874753609) ^ 71527146488220756864437376804 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (13 : ZMod 143054292976441513728874753609) ^ 47684764325480504576291584536 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (13 : ZMod 143054292976441513728874753609) ^ 9164658177890095292856 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (13 : ZMod 143054292976441513728874753609) ^ 2190855525177818292984 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (13 : ZMod 143054292976441513728874753609) ^ 73384489334940552 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_143054292976441513728874753667 : Nat.Prime 143054292976441513728874753667 := by
  apply lucas_primality 143054292976441513728874753667 (2 : ZMod 143054292976441513728874753667)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (6502467862565523351312488803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (6502467862565523351312488803, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753667 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_11
      · exact prime_oneHundredTwentyOneDO_6502467862565523351312488803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 143054292976441513728874753667) ^ 71527146488220756864437376833 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 143054292976441513728874753667) ^ 13004935725131046702624977606 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (2 : ZMod 143054292976441513728874753667) ^ 22 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyOneDO_143054292976441513728874753687 : Nat.Prime 143054292976441513728874753687 := by
  apply lucas_primality 143054292976441513728874753687 (5 : ZMod 143054292976441513728874753687)
  · rw [← oneHundredTwentyOneDOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23842382162740252288145792281, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23842382162740252288145792281, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753687 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyOneDO_2
      · exact prime_oneHundredTwentyOneDO_3
      · exact prime_oneHundredTwentyOneDO_23842382162740252288145792281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 143054292976441513728874753687) ^ 71527146488220756864437376843 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 143054292976441513728874753687) ^ 47684764325480504576291584562 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide
    · change (5 : ZMod 143054292976441513728874753687) ^ 6 ≠ 1
      rw [← oneHundredTwentyOneDOFastPow_eq_pow]
      decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753600 : Nat.totient 143054292976441513728874753600 = 52019439321742061608074240000 := by
  rw [← show ((([(2, 6), (5, 2), (11, 2), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753600 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_2, prime_oneHundredTwentyOneDO_5, prime_oneHundredTwentyOneDO_11, prime_oneHundredTwentyOneDO_171401, prime_oneHundredTwentyOneDO_714027719, prime_oneHundredTwentyOneDO_6037638679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753601 : Nat.totient 143054292976441513728874753601 = 142831119350095538493551247360 := by
  rw [← show ((([(641, 1), (60579977329, 1), (3683950272483409, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753601 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_641, prime_oneHundredTwentyOneDO_60579977329, prime_oneHundredTwentyOneDO_3683950272483409]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753602 : Nat.totient 143054292976441513728874753602 = 46943822326761434504745912960 := by
  rw [← show ((([(2, 1), (3, 1), (67, 1), (1609, 1), (1335259, 1), (165635447035832771, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753602 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_2, prime_oneHundredTwentyOneDO_3, prime_oneHundredTwentyOneDO_67, prime_oneHundredTwentyOneDO_1609, prime_oneHundredTwentyOneDO_1335259, prime_oneHundredTwentyOneDO_165635447035832771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753603 : Nat.totient 143054292976441513728874753603 = 132033953644944787579501670400 := by
  rw [← show ((([(13, 1), (8221, 1), (1318781, 1), (620764897, 1), (1635057623, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753603 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_13, prime_oneHundredTwentyOneDO_8221, prime_oneHundredTwentyOneDO_1318781, prime_oneHundredTwentyOneDO_620764897, prime_oneHundredTwentyOneDO_1635057623]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753604 : Nat.totient 143054292976441513728874753604 = 65295280637550826520091033600 := by
  rw [← show ((([(2, 2), (17, 1), (53, 1), (89, 1), (7477, 1), (19597, 1), (7654121, 1), (397661741, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753604 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_2, prime_oneHundredTwentyOneDO_17, prime_oneHundredTwentyOneDO_53, prime_oneHundredTwentyOneDO_89, prime_oneHundredTwentyOneDO_7477, prime_oneHundredTwentyOneDO_19597, prime_oneHundredTwentyOneDO_7654121, prime_oneHundredTwentyOneDO_397661741]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753605 : Nat.totient 143054292976441513728874753605 = 62552922199347792005883682560 := by
  rw [← show ((([(3, 1), (5, 1), (7, 1), (23, 1), (5750117, 1), (10301656832607448111, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753605 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_3, prime_oneHundredTwentyOneDO_5, prime_oneHundredTwentyOneDO_7, prime_oneHundredTwentyOneDO_23, prime_oneHundredTwentyOneDO_5750117, prime_oneHundredTwentyOneDO_10301656832607448111]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753606 : Nat.totient 143054292976441513728874753606 = 71521972119847358183134811520 := by
  rw [← show ((([(2, 1), (14057, 1), (831619, 1), (6118625208737008441, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753606 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_2, prime_oneHundredTwentyOneDO_14057, prime_oneHundredTwentyOneDO_831619, prime_oneHundredTwentyOneDO_6118625208737008441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753607 : Nat.totient 143054292976441513728874753607 = 143051988288375002129033721120 := by
  rw [← show ((([(62071, 1), (2304688066511599840970417, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753607 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_62071, prime_oneHundredTwentyOneDO_2304688066511599840970417]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753608 : Nat.totient 143054292976441513728874753608 = 47684760540284855510949291264 := by
  rw [← show ((([(2, 3), (3, 2), (15609343, 1), (65296087, 1), (1949380506329, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753608 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_2, prime_oneHundredTwentyOneDO_3, prime_oneHundredTwentyOneDO_15609343, prime_oneHundredTwentyOneDO_65296087, prime_oneHundredTwentyOneDO_1949380506329]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753609 : Nat.totient 143054292976441513728874753609 = 143054292976441513728874753608 := by
  rw [← show ((([(143054292976441513728874753609, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753609 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_143054292976441513728874753609]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753610 : Nat.totient 143054292976441513728874753610 = 57191613788437816380459611200 := by
  rw [← show ((([(2, 1), (5, 1), (1901, 1), (22415483, 1), (335714946508128767, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753610 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_2, prime_oneHundredTwentyOneDO_5, prime_oneHundredTwentyOneDO_1901, prime_oneHundredTwentyOneDO_22415483, prime_oneHundredTwentyOneDO_335714946508128767]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753611 : Nat.totient 143054292976441513728874753611 = 86690874520800625827825561600 := by
  rw [← show ((([(3, 1), (11, 1), (18541, 1), (21617, 1), (8348687, 1), (1295508299753, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753611 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_3, prime_oneHundredTwentyOneDO_11, prime_oneHundredTwentyOneDO_18541, prime_oneHundredTwentyOneDO_21617, prime_oneHundredTwentyOneDO_8348687, prime_oneHundredTwentyOneDO_1295508299753]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753612 : Nat.totient 143054292976441513728874753612 = 61249632285252481637859320832 := by
  rw [← show ((([(2, 2), (7, 1), (1033, 1), (1932639824057, 1), (2559125698709, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753612 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_2, prime_oneHundredTwentyOneDO_7, prime_oneHundredTwentyOneDO_1033, prime_oneHundredTwentyOneDO_1932639824057, prime_oneHundredTwentyOneDO_2559125698709]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753613 : Nat.totient 143054292976441513728874753613 = 138116115968348085255668835456 := by
  rw [← show ((([(29, 1), (26267, 1), (11517307, 1), (16305776300704313, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753613 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_29, prime_oneHundredTwentyOneDO_26267, prime_oneHundredTwentyOneDO_11517307, prime_oneHundredTwentyOneDO_16305776300704313]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753614 : Nat.totient 143054292976441513728874753614 = 47684744022086851493313786720 := by
  rw [← show ((([(2, 1), (3, 1), (2354591, 1), (924758573, 1), (10949790224383, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753614 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_2, prime_oneHundredTwentyOneDO_3, prime_oneHundredTwentyOneDO_2354591, prime_oneHundredTwentyOneDO_924758573, prime_oneHundredTwentyOneDO_10949790224383]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753615 : Nat.totient 143054292976441513728874753615 = 112740932421645813567250531200 := by
  rw [← show ((([(5, 1), (101, 1), (199, 1), (767404309363, 1), (1854949997179, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753615 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_5, prime_oneHundredTwentyOneDO_101, prime_oneHundredTwentyOneDO_199, prime_oneHundredTwentyOneDO_767404309363, prime_oneHundredTwentyOneDO_1854949997179]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753616 : Nat.totient 143054292976441513728874753616 = 66022034873782002679077027840 := by
  rw [← show ((([(2, 4), (13, 1), (28573, 1), (92641, 1), (259823533535082989, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753616 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_2, prime_oneHundredTwentyOneDO_13, prime_oneHundredTwentyOneDO_28573, prime_oneHundredTwentyOneDO_92641, prime_oneHundredTwentyOneDO_259823533535082989]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753617 : Nat.totient 143054292976441513728874753617 = 95369528650193380781306021088 := by
  rw [← show ((([(3, 2), (124239312709, 1), (127937937640211957, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753617 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_3, prime_oneHundredTwentyOneDO_124239312709, prime_oneHundredTwentyOneDO_127937937640211957]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753618 : Nat.totient 143054292976441513728874753618 = 67757778650212987493140494336 := by
  rw [← show ((([(2, 1), (19, 1), (14173, 1), (861519343, 1), (308312035685249, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753618 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_2, prime_oneHundredTwentyOneDO_19, prime_oneHundredTwentyOneDO_14173, prime_oneHundredTwentyOneDO_861519343, prime_oneHundredTwentyOneDO_308312035685249]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753619 : Nat.totient 143054292976441513728874753619 = 122422369064124160155553228800 := by
  rw [← show ((([(7, 1), (661, 1), (12433, 1), (526583, 1), (9796411, 1), (482049493, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753619 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_7, prime_oneHundredTwentyOneDO_661, prime_oneHundredTwentyOneDO_12433, prime_oneHundredTwentyOneDO_526583, prime_oneHundredTwentyOneDO_9796411, prime_oneHundredTwentyOneDO_482049493]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753620 : Nat.totient 143054292976441513728874753620 = 36952377600989309189208145920 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (43, 1), (127, 1), (2593, 1), (59207, 1), (10096081, 1), (281675497, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753620 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_2, prime_oneHundredTwentyOneDO_3, prime_oneHundredTwentyOneDO_5, prime_oneHundredTwentyOneDO_43, prime_oneHundredTwentyOneDO_127, prime_oneHundredTwentyOneDO_2593, prime_oneHundredTwentyOneDO_59207, prime_oneHundredTwentyOneDO_10096081, prime_oneHundredTwentyOneDO_281675497]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753621 : Nat.totient 143054292976441513728874753621 = 134639334565643370252406579200 := by
  rw [← show ((([(17, 1), (321161878913, 1), (26201610349460101, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753621 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_17, prime_oneHundredTwentyOneDO_321161878913, prime_oneHundredTwentyOneDO_26201610349460101]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753622 : Nat.totient 143054292976441513728874753622 = 64278208136254950123140325600 := by
  rw [← show ((([(2, 1), (11, 1), (167, 1), (181, 1), (215121178501522590773563, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753622 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_2, prime_oneHundredTwentyOneDO_11, prime_oneHundredTwentyOneDO_167, prime_oneHundredTwentyOneDO_181, prime_oneHundredTwentyOneDO_215121178501522590773563]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753623 : Nat.totient 143054292976441513728874753623 = 92293092242865492728306290800 := by
  rw [← show ((([(3, 1), (31, 2), (49619942066056716520594781, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753623 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_3, prime_oneHundredTwentyOneDO_31, prime_oneHundredTwentyOneDO_49619942066056716520594781]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753624 : Nat.totient 143054292976441513728874753624 = 71509347326142505779545835520 := by
  rw [← show ((([(2, 3), (4019, 1), (37392617, 1), (118989061972089761, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753624 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_2, prime_oneHundredTwentyOneDO_4019, prime_oneHundredTwentyOneDO_37392617, prime_oneHundredTwentyOneDO_118989061972089761]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753625 : Nat.totient 143054292976441513728874753625 = 113850463218332077693169049600 := by
  rw [← show ((([(5, 3), (193, 1), (531307856377, 1), (11160594662389, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753625 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_5, prime_oneHundredTwentyOneDO_193, prime_oneHundredTwentyOneDO_531307856377, prime_oneHundredTwentyOneDO_11160594662389]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753626 : Nat.totient 143054292976441513728874753626 = 40598342014407179351626951488 := by
  rw [← show ((([(2, 1), (3, 3), (7, 1), (149, 1), (2539936312212661370847533, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753626 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_2, prime_oneHundredTwentyOneDO_3, prime_oneHundredTwentyOneDO_7, prime_oneHundredTwentyOneDO_149, prime_oneHundredTwentyOneDO_2539936312212661370847533]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753627 : Nat.totient 143054292976441513728874753627 = 142577601106348189416469266432 := by
  rw [← show ((([(353, 1), (2003, 1), (655489, 1), (38633759, 1), (7989376103, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753627 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_353, prime_oneHundredTwentyOneDO_2003, prime_oneHundredTwentyOneDO_655489, prime_oneHundredTwentyOneDO_38633759, prime_oneHundredTwentyOneDO_7989376103]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753628 : Nat.totient 143054292976441513728874753628 = 66568155133552522541736955200 := by
  rw [← show ((([(2, 2), (23, 1), (37, 1), (5649569214607, 1), (7438682290051, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753628 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_2, prime_oneHundredTwentyOneDO_23, prime_oneHundredTwentyOneDO_37, prime_oneHundredTwentyOneDO_5649569214607, prime_oneHundredTwentyOneDO_7438682290051]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753629 : Nat.totient 143054292976441513728874753629 = 88033355788353838173239227200 := by
  rw [← show ((([(3, 1), (13, 1), (1592671, 1), (2303086321197366638341, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753629 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_3, prime_oneHundredTwentyOneDO_13, prime_oneHundredTwentyOneDO_1592671, prime_oneHundredTwentyOneDO_2303086321197366638341]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753630 : Nat.totient 143054292976441513728874753630 = 57221647868095836958387287840 := by
  rw [← show ((([(2, 1), (5, 1), (825479, 1), (19022995471, 1), (910994932907, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753630 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_2, prime_oneHundredTwentyOneDO_5, prime_oneHundredTwentyOneDO_825479, prime_oneHundredTwentyOneDO_19022995471, prime_oneHundredTwentyOneDO_910994932907]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753631 : Nat.totient 143054292976441513728874753631 = 143054192771741381610882991392 := by
  rw [← show ((([(1427653, 1), (65582676239, 1), (1527879479293, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753631 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_1427653, prime_oneHundredTwentyOneDO_65582676239, prime_oneHundredTwentyOneDO_1527879479293]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753632 : Nat.totient 143054292976441513728874753632 = 46460588815497068398861516800 := by
  rw [← show ((([(2, 5), (3, 1), (41, 1), (761, 1), (375327493, 1), (127247943062269, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753632 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_2, prime_oneHundredTwentyOneDO_3, prime_oneHundredTwentyOneDO_41, prime_oneHundredTwentyOneDO_761, prime_oneHundredTwentyOneDO_375327493, prime_oneHundredTwentyOneDO_127247943062269]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753633 : Nat.totient 143054292976441513728874753633 = 111470877623450894371574769360 := by
  rw [← show ((([(7, 3), (11, 1), (5429792839, 1), (6982819718723939, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753633 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_7, prime_oneHundredTwentyOneDO_11, prime_oneHundredTwentyOneDO_5429792839, prime_oneHundredTwentyOneDO_6982819718723939]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753634 : Nat.totient 143054292976441513728874753634 = 71527146488220756864437376816 := by
  rw [← show ((([(2, 1), (71527146488220756864437376817, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753634 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_2, prime_oneHundredTwentyOneDO_71527146488220756864437376817]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753635 : Nat.totient 143054292976441513728874753635 = 76295622620364562432495687680 := by
  rw [← show ((([(3, 2), (5, 1), (431003641, 1), (654233809, 1), (11273907287, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753635 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_3, prime_oneHundredTwentyOneDO_5, prime_oneHundredTwentyOneDO_431003641, prime_oneHundredTwentyOneDO_654233809, prime_oneHundredTwentyOneDO_11273907287]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753636 : Nat.totient 143054292976441513728874753636 = 71527146488220756864437376816 := by
  rw [← show ((([(2, 2), (35763573244110378432218688409, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753636 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_2, prime_oneHundredTwentyOneDO_35763573244110378432218688409]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753637 : Nat.totient 143054292976441513728874753637 = 133616315159611791918741429120 := by
  rw [← show ((([(19, 1), (71, 1), (106044694571120469776778913, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753637 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_19, prime_oneHundredTwentyOneDO_71, prime_oneHundredTwentyOneDO_106044694571120469776778913]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753638 : Nat.totient 143054292976441513728874753638 = 44856382016950323123133155840 := by
  rw [← show ((([(2, 1), (3, 1), (17, 1), (3271, 1), (4637, 1), (92466215604885683747, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753638 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_2, prime_oneHundredTwentyOneDO_3, prime_oneHundredTwentyOneDO_17, prime_oneHundredTwentyOneDO_3271, prime_oneHundredTwentyOneDO_4637, prime_oneHundredTwentyOneDO_92466215604885683747]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753639 : Nat.totient 143054292976441513728874753639 = 140629422625042885779063168000 := by
  rw [← show ((([(59, 1), (1284487, 1), (1415851, 1), (12574993, 1), (106021481, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753639 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_59, prime_oneHundredTwentyOneDO_1284487, prime_oneHundredTwentyOneDO_1415851, prime_oneHundredTwentyOneDO_12574993, prime_oneHundredTwentyOneDO_106021481]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753640 : Nat.totient 143054292976441513728874753640 = 48691719841420532006798524416 := by
  rw [← show ((([(2, 3), (5, 1), (7, 1), (139, 1), (19753, 1), (354439, 1), (8837987, 1), (59401873, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753640 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_2, prime_oneHundredTwentyOneDO_5, prime_oneHundredTwentyOneDO_7, prime_oneHundredTwentyOneDO_139, prime_oneHundredTwentyOneDO_19753, prime_oneHundredTwentyOneDO_354439, prime_oneHundredTwentyOneDO_8837987, prime_oneHundredTwentyOneDO_59401873]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753641 : Nat.totient 143054292976441513728874753641 = 92391242192910973510955827200 := by
  rw [← show ((([(3, 1), (61, 1), (131, 1), (173, 1), (577, 1), (329993, 1), (181155642691489, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753641 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_3, prime_oneHundredTwentyOneDO_61, prime_oneHundredTwentyOneDO_131, prime_oneHundredTwentyOneDO_173, prime_oneHundredTwentyOneDO_577, prime_oneHundredTwentyOneDO_329993, prime_oneHundredTwentyOneDO_181155642691489]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753642 : Nat.totient 143054292976441513728874753642 = 63688361939670241904441338944 := by
  rw [← show ((([(2, 1), (13, 1), (29, 2), (1063, 1), (6154578097571874053399, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753642 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_2, prime_oneHundredTwentyOneDO_13, prime_oneHundredTwentyOneDO_29, prime_oneHundredTwentyOneDO_1063, prime_oneHundredTwentyOneDO_6154578097571874053399]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753643 : Nat.totient 143054292976441513728874753643 = 141788325781959730421539578720 := by
  rw [← show ((([(113, 1), (1265967194481783307335174811, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753643 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_113, prime_oneHundredTwentyOneDO_1265967194481783307335174811]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753644 : Nat.totient 143054292976441513728874753644 = 42944646567183230115741398400 := by
  rw [← show ((([(2, 2), (3, 2), (11, 1), (107, 1), (43001837, 1), (78511797954027271, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753644 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_2, prime_oneHundredTwentyOneDO_3, prime_oneHundredTwentyOneDO_11, prime_oneHundredTwentyOneDO_107, prime_oneHundredTwentyOneDO_43001837, prime_oneHundredTwentyOneDO_78511797954027271]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753645 : Nat.totient 143054292976441513728874753645 = 114443434381153210983099802912 := by
  rw [← show ((([(5, 1), (28610858595288302745774950729, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753645 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_5, prime_oneHundredTwentyOneDO_28610858595288302745774950729]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753646 : Nat.totient 143054292976441513728874753646 = 69780194904625355601808920000 := by
  rw [← show ((([(2, 1), (47, 1), (311, 1), (1163488269001, 1), (4205819631319, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753646 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_2, prime_oneHundredTwentyOneDO_47, prime_oneHundredTwentyOneDO_311, prime_oneHundredTwentyOneDO_1163488269001, prime_oneHundredTwentyOneDO_4205819631319]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753647 : Nat.totient 143054292976441513728874753647 = 81745310272252293559357002072 := by
  rw [← show ((([(3, 1), (7, 1), (6812109189354357796613083507, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753647 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_3, prime_oneHundredTwentyOneDO_7, prime_oneHundredTwentyOneDO_6812109189354357796613083507]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753648 : Nat.totient 143054292976441513728874753648 = 71506030690078719211475201280 := by
  rw [← show ((([(2, 4), (3389, 1), (7066487, 1), (373341079970251621, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753648 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_2, prime_oneHundredTwentyOneDO_3389, prime_oneHundredTwentyOneDO_7066487, prime_oneHundredTwentyOneDO_373341079970251621]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753649 : Nat.totient 143054292976441513728874753649 = 143046948195778349919575105136 := by
  rw [← show ((([(19477, 1), (7344780663163809299629037, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753649 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_19477, prime_oneHundredTwentyOneDO_7344780663163809299629037]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753650 : Nat.totient 143054292976441513728874753650 = 38147807339259902191713046080 := by
  rw [← show ((([(2, 1), (3, 1), (5, 2), (9576443, 1), (277412503, 1), (358987541879, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753650 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_2, prime_oneHundredTwentyOneDO_3, prime_oneHundredTwentyOneDO_5, prime_oneHundredTwentyOneDO_9576443, prime_oneHundredTwentyOneDO_277412503, prime_oneHundredTwentyOneDO_358987541879]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753651 : Nat.totient 143054292976441513728874753651 = 136351026828367360758017964552 := by
  rw [← show ((([(23, 1), (283, 1), (21977921796964435970022239, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753651 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_23, prime_oneHundredTwentyOneDO_283, prime_oneHundredTwentyOneDO_21977921796964435970022239]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753652 : Nat.totient 143054292976441513728874753652 = 71384945401763061522758573880 := by
  rw [← show ((([(2, 2), (503, 1), (71100543228847670839400971, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753652 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_2, prime_oneHundredTwentyOneDO_503, prime_oneHundredTwentyOneDO_71100543228847670839400971]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753653 : Nat.totient 143054292976441513728874753653 = 95064833670271595491552528896 := by
  rw [← show ((([(3, 4), (313, 1), (97779597193, 1), (57706308742757, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753653 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_3, prime_oneHundredTwentyOneDO_313, prime_oneHundredTwentyOneDO_97779597193, prime_oneHundredTwentyOneDO_57706308742757]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753654 : Nat.totient 143054292976441513728874753654 = 58518516412306104978417284160 := by
  rw [← show ((([(2, 1), (7, 1), (31, 1), (73, 1), (4515317624406335260680347, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753654 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_2, prime_oneHundredTwentyOneDO_7, prime_oneHundredTwentyOneDO_31, prime_oneHundredTwentyOneDO_73, prime_oneHundredTwentyOneDO_4515317624406335260680347]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753655 : Nat.totient 143054292976441513728874753655 = 90375338423598661376393472000 := by
  rw [← show ((([(5, 1), (11, 1), (13, 1), (17, 1), (7591, 1), (1550411355806685423811, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753655 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_5, prime_oneHundredTwentyOneDO_11, prime_oneHundredTwentyOneDO_13, prime_oneHundredTwentyOneDO_17, prime_oneHundredTwentyOneDO_7591, prime_oneHundredTwentyOneDO_1550411355806685423811]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753656 : Nat.totient 143054292976441513728874753656 = 45171390558604590718643419776 := by
  rw [← show ((([(2, 3), (3, 1), (19, 1), (12379, 1), (25342560366176432379269, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753656 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_2, prime_oneHundredTwentyOneDO_3, prime_oneHundredTwentyOneDO_19, prime_oneHundredTwentyOneDO_12379, prime_oneHundredTwentyOneDO_25342560366176432379269]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753657 : Nat.totient 143054292976441513728874753657 = 140337180073732015357612484544 := by
  rw [← show ((([(53, 1), (7879, 1), (869119, 1), (394161934691576669, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753657 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_53, prime_oneHundredTwentyOneDO_7879, prime_oneHundredTwentyOneDO_869119, prime_oneHundredTwentyOneDO_394161934691576669]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753658 : Nat.totient 143054292976441513728874753658 = 70816661443053015262743096000 := by
  rw [← show ((([(2, 1), (251, 1), (349, 1), (379, 1), (2087, 1), (1032309899567240527, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753658 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_2, prime_oneHundredTwentyOneDO_251, prime_oneHundredTwentyOneDO_349, prime_oneHundredTwentyOneDO_379, prime_oneHundredTwentyOneDO_2087, prime_oneHundredTwentyOneDO_1032309899567240527]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753659 : Nat.totient 143054292976441513728874753659 = 95245511058437002638730653696 := by
  rw [← show ((([(3, 1), (769, 1), (62008796262003256926256937, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753659 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_3, prime_oneHundredTwentyOneDO_769, prime_oneHundredTwentyOneDO_62008796262003256926256937]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753660 : Nat.totient 143054292976441513728874753660 = 57136692309603382202898511872 := by
  rw [← show ((([(2, 2), (5, 1), (673, 1), (1387974373, 1), (7657277528107127, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753660 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_2, prime_oneHundredTwentyOneDO_5, prime_oneHundredTwentyOneDO_673, prime_oneHundredTwentyOneDO_1387974373, prime_oneHundredTwentyOneDO_7657277528107127]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753661 : Nat.totient 143054292976441513728874753661 = 122617965408378440339035503132 := by
  rw [← show ((([(7, 1), (20436327568063073389839250523, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753661 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_7, prime_oneHundredTwentyOneDO_20436327568063073389839250523]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753662 : Nat.totient 143054292976441513728874753662 = 47684764325480504576291584548 := by
  rw [← show ((([(2, 1), (3, 2), (7947460720913417429381930759, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753662 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_2, prime_oneHundredTwentyOneDO_3, prime_oneHundredTwentyOneDO_7947460720913417429381930759]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753663 : Nat.totient 143054292976441513728874753663 = 139727388065689732773722836320 := by
  rw [← show ((([(43, 1), (2499053, 1), (28080931, 1), (47407327182587, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753663 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_43, prime_oneHundredTwentyOneDO_2499053, prime_oneHundredTwentyOneDO_28080931, prime_oneHundredTwentyOneDO_47407327182587]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753664 : Nat.totient 143054292976441513728874753664 = 70782984915557377040846069760 := by
  rw [← show ((([(2, 7), (97, 1), (10459, 1), (1101612939162985290631, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753664 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_2, prime_oneHundredTwentyOneDO_97, prime_oneHundredTwentyOneDO_10459, prime_oneHundredTwentyOneDO_1101612939162985290631]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753665 : Nat.totient 143054292976441513728874753665 = 73449789935561435609321472000 := by
  rw [← show ((([(3, 1), (5, 1), (37, 1), (103, 1), (2549, 1), (2687, 1), (10861, 1), (600857, 1), (55987651, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753665 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_3, prime_oneHundredTwentyOneDO_5, prime_oneHundredTwentyOneDO_37, prime_oneHundredTwentyOneDO_103, prime_oneHundredTwentyOneDO_2549, prime_oneHundredTwentyOneDO_2687, prime_oneHundredTwentyOneDO_10861, prime_oneHundredTwentyOneDO_600857, prime_oneHundredTwentyOneDO_55987651]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753666 : Nat.totient 143054292976441513728874753666 = 65024678625655233513124888020 := by
  rw [← show ((([(2, 1), (11, 1), (6502467862565523351312488803, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753666 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_2, prime_oneHundredTwentyOneDO_11, prime_oneHundredTwentyOneDO_6502467862565523351312488803]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753667 : Nat.totient 143054292976441513728874753667 = 143054292976441513728874753666 := by
  rw [← show ((([(143054292976441513728874753667, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753667 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_143054292976441513728874753667]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753668 : Nat.totient 143054292976441513728874753668 = 37728267858132204634321881600 := by
  rw [← show ((([(2, 2), (3, 1), (7, 1), (13, 1), (112031, 1), (332210939, 1), (3519865880381, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753668 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_2, prime_oneHundredTwentyOneDO_3, prime_oneHundredTwentyOneDO_7, prime_oneHundredTwentyOneDO_13, prime_oneHundredTwentyOneDO_112031, prime_oneHundredTwentyOneDO_332210939, prime_oneHundredTwentyOneDO_3519865880381]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753669 : Nat.totient 143054292976441513728874753669 = 140668914813714555206109709824 := by
  rw [← show ((([(67, 1), (587, 1), (13829, 1), (263025112294685047009, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753669 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_67, prime_oneHundredTwentyOneDO_587, prime_oneHundredTwentyOneDO_13829, prime_oneHundredTwentyOneDO_263025112294685047009]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753670 : Nat.totient 143054292976441513728874753670 = 57153514883813175440329826400 := by
  rw [← show ((([(2, 1), (5, 1), (839, 1), (2637042103, 1), (6465794100565351, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753670 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_2, prime_oneHundredTwentyOneDO_5, prime_oneHundredTwentyOneDO_839, prime_oneHundredTwentyOneDO_2637042103, prime_oneHundredTwentyOneDO_6465794100565351]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753671 : Nat.totient 143054292976441513728874753671 = 91964209956095768680249749504 := by
  rw [← show ((([(3, 2), (29, 1), (1129, 1), (2617, 1), (4235935463, 1), (43793876429, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753671 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_3, prime_oneHundredTwentyOneDO_29, prime_oneHundredTwentyOneDO_1129, prime_oneHundredTwentyOneDO_2617, prime_oneHundredTwentyOneDO_4235935463, prime_oneHundredTwentyOneDO_43793876429]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753672 : Nat.totient 143054292976441513728874753672 = 66828181441733152059849441280 := by
  rw [← show ((([(2, 3), (17, 1), (137, 1), (890993, 1), (2530961, 1), (3404722137977, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753672 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_2, prime_oneHundredTwentyOneDO_17, prime_oneHundredTwentyOneDO_137, prime_oneHundredTwentyOneDO_890993, prime_oneHundredTwentyOneDO_2530961, prime_oneHundredTwentyOneDO_3404722137977]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753673 : Nat.totient 143054292976441513728874753673 = 139564924394846412128572796800 := by
  rw [← show ((([(41, 1), (582773, 1), (5987115218080416188861, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753673 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_41, prime_oneHundredTwentyOneDO_582773, prime_oneHundredTwentyOneDO_5987115218080416188861]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753674 : Nat.totient 143054292976441513728874753674 = 45604237978642038873492510272 := by
  rw [← show ((([(2, 1), (3, 1), (23, 1), (6269, 1), (165357363442891885455317, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753674 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_2, prime_oneHundredTwentyOneDO_3, prime_oneHundredTwentyOneDO_23, prime_oneHundredTwentyOneDO_6269, prime_oneHundredTwentyOneDO_165357363442891885455317]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753675 : Nat.totient 143054292976441513728874753675 = 92888145462042450334925228160 := by
  rw [← show ((([(5, 2), (7, 1), (19, 1), (2143, 1), (5825185187, 1), (3446492502899, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753675 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_5, prime_oneHundredTwentyOneDO_7, prime_oneHundredTwentyOneDO_19, prime_oneHundredTwentyOneDO_2143, prime_oneHundredTwentyOneDO_5825185187, prime_oneHundredTwentyOneDO_3446492502899]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753676 : Nat.totient 143054292976441513728874753676 = 71348657382840989549529600000 := by
  rw [← show ((([(2, 2), (401, 1), (609101, 1), (2378057809, 1), (61572219791, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753676 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_2, prime_oneHundredTwentyOneDO_401, prime_oneHundredTwentyOneDO_609101, prime_oneHundredTwentyOneDO_2378057809, prime_oneHundredTwentyOneDO_61572219791]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753677 : Nat.totient 143054292976441513728874753677 = 85602106840148367489702601920 := by
  rw [← show ((([(3, 1), (11, 1), (79, 1), (49471423, 1), (1109188763774599357, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753677 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_3, prime_oneHundredTwentyOneDO_11, prime_oneHundredTwentyOneDO_79, prime_oneHundredTwentyOneDO_49471423, prime_oneHundredTwentyOneDO_1109188763774599357]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753678 : Nat.totient 143054292976441513728874753678 = 70665373638895256347155030136 := by
  rw [← show ((([(2, 1), (83, 1), (1013186584247, 1), (850556908919339, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753678 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_2, prime_oneHundredTwentyOneDO_83, prime_oneHundredTwentyOneDO_1013186584247, prime_oneHundredTwentyOneDO_850556908919339]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753679 : Nat.totient 143054292976441513728874753679 = 143047808831771635062511287936 := by
  rw [← show ((([(22063, 1), (585445577, 1), (11075154693333529, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753679 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_22063, prime_oneHundredTwentyOneDO_585445577, prime_oneHundredTwentyOneDO_11075154693333529]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753680 : Nat.totient 143054292976441513728874753680 = 38129009041197059515715248128 := by
  rw [← show ((([(2, 4), (3, 3), (5, 1), (2029, 1), (33679313, 1), (969174263781499, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753680 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_2, prime_oneHundredTwentyOneDO_3, prime_oneHundredTwentyOneDO_5, prime_oneHundredTwentyOneDO_2029, prime_oneHundredTwentyOneDO_33679313, prime_oneHundredTwentyOneDO_969174263781499]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753681 : Nat.totient 143054292976441513728874753681 = 132049824039697052072219616000 := by
  rw [← show ((([(13, 1), (452017, 1), (315417211, 1), (77182241507551, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753681 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_13, prime_oneHundredTwentyOneDO_452017, prime_oneHundredTwentyOneDO_315417211, prime_oneHundredTwentyOneDO_77182241507551]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753682 : Nat.totient 143054292976441513728874753682 = 61308956893323610564839817344 := by
  rw [← show ((([(2, 1), (7, 2), (2460299, 1), (68767739, 1), (8627842012369, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753682 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_2, prime_oneHundredTwentyOneDO_7, prime_oneHundredTwentyOneDO_2460299, prime_oneHundredTwentyOneDO_68767739, prime_oneHundredTwentyOneDO_8627842012369]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753683 : Nat.totient 143054292976441513728874753683 = 94970365970957366199545063136 := by
  rw [← show ((([(3, 1), (239, 1), (747827, 1), (266796789051514876837, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753683 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_3, prime_oneHundredTwentyOneDO_239, prime_oneHundredTwentyOneDO_747827, prime_oneHundredTwentyOneDO_266796789051514876837]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753684 : Nat.totient 143054292976441513728874753684 = 71526310957647235803017039040 := by
  rw [← show ((([(2, 2), (85607, 1), (51645051611, 1), (8089150399273, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753684 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_2, prime_oneHundredTwentyOneDO_85607, prime_oneHundredTwentyOneDO_51645051611, prime_oneHundredTwentyOneDO_8089150399273]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753685 : Nat.totient 143054292976441513728874753685 = 110226820960695824187992179200 := by
  rw [← show ((([(5, 1), (31, 1), (211, 1), (1033899533, 1), (4230662710903529, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753685 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_5, prime_oneHundredTwentyOneDO_31, prime_oneHundredTwentyOneDO_211, prime_oneHundredTwentyOneDO_1033899533, prime_oneHundredTwentyOneDO_4230662710903529]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753686 : Nat.totient 143054292976441513728874753686 = 47684764325480504576291584560 := by
  rw [← show ((([(2, 1), (3, 1), (23842382162740252288145792281, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753686 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_2, prime_oneHundredTwentyOneDO_3, prime_oneHundredTwentyOneDO_23842382162740252288145792281]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753687 : Nat.totient 143054292976441513728874753687 = 143054292976441513728874753686 := by
  rw [← show ((([(143054292976441513728874753687, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753687 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_143054292976441513728874753687]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753688 : Nat.totient 143054292976441513728874753688 = 65024678625655233513124888000 := by
  rw [← show ((([(2, 3), (11, 1), (1625616965641380837828122201, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753688 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_2, prime_oneHundredTwentyOneDO_11, prime_oneHundredTwentyOneDO_1625616965641380837828122201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753689 : Nat.totient 143054292976441513728874753689 = 76936698725140066247265848832 := by
  rw [← show ((([(3, 2), (7, 1), (17, 1), (1204859, 1), (2889582079, 1), (38365438219, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753689 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_3, prime_oneHundredTwentyOneDO_7, prime_oneHundredTwentyOneDO_17, prime_oneHundredTwentyOneDO_1204859, prime_oneHundredTwentyOneDO_2889582079, prime_oneHundredTwentyOneDO_38365438219]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753690 : Nat.totient 143054292976441513728874753690 = 57220365327619716989295716160 := by
  rw [← show ((([(2, 1), (5, 1), (42443, 1), (15627853, 1), (21567286335162311, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753690 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_2, prime_oneHundredTwentyOneDO_5, prime_oneHundredTwentyOneDO_42443, prime_oneHundredTwentyOneDO_15627853, prime_oneHundredTwentyOneDO_21567286335162311]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753691 : Nat.totient 143054292976441513728874753691 = 143054292973150225520921963112 := by
  rw [← show ((([(43464529943, 1), (3291288164488260637, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753691 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_43464529943, prime_oneHundredTwentyOneDO_3291288164488260637]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753692 : Nat.totient 143054292976441513728874753692 = 47683225263274601968262015728 := by
  rw [← show ((([(2, 2), (3, 1), (30983, 1), (384765551475652007361227, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753692 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_2, prime_oneHundredTwentyOneDO_3, prime_oneHundredTwentyOneDO_30983, prime_oneHundredTwentyOneDO_384765551475652007361227]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753693 : Nat.totient 143054292976441513728874753693 = 138437431976477423974506526336 := by
  rw [← show ((([(47, 1), (89, 1), (52504156247, 1), (651357393302093, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753693 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_47, prime_oneHundredTwentyOneDO_89, prime_oneHundredTwentyOneDO_52504156247, prime_oneHundredTwentyOneDO_651357393302093]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753694 : Nat.totient 143054292976441513728874753694 = 62507292279146686620145393920 := by
  rw [← show ((([(2, 1), (13, 1), (19, 1), (1913, 1), (6211, 1), (24372352293461154107, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753694 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_2, prime_oneHundredTwentyOneDO_13, prime_oneHundredTwentyOneDO_19, prime_oneHundredTwentyOneDO_1913, prime_oneHundredTwentyOneDO_6211, prime_oneHundredTwentyOneDO_24372352293461154107]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753695 : Nat.totient 143054292976441513728874753695 = 75908335368872838325875319680 := by
  rw [← show ((([(3, 1), (5, 1), (197, 1), (602914999, 1), (80294781734595371, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753695 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_3, prime_oneHundredTwentyOneDO_5, prime_oneHundredTwentyOneDO_197, prime_oneHundredTwentyOneDO_602914999, prime_oneHundredTwentyOneDO_80294781734595371]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753696 : Nat.totient 143054292976441513728874753696 = 61054588584788003972741836800 := by
  rw [← show ((([(2, 5), (7, 1), (241, 1), (209179080359, 1), (12668277994741, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753696 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_2, prime_oneHundredTwentyOneDO_7, prime_oneHundredTwentyOneDO_241, prime_oneHundredTwentyOneDO_209179080359, prime_oneHundredTwentyOneDO_12668277994741]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753697 : Nat.totient 143054292976441513728874753697 = 136619699059566239207834499840 := by
  rw [← show ((([(23, 1), (821, 1), (2837, 1), (256466803, 1), (10412125837669, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753697 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_23, prime_oneHundredTwentyOneDO_821, prime_oneHundredTwentyOneDO_2837, prime_oneHundredTwentyOneDO_256466803, prime_oneHundredTwentyOneDO_10412125837669]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753698 : Nat.totient 143054292976441513728874753698 = 46865055814277971355568410400 := by
  rw [← show ((([(2, 1), (3, 2), (59, 1), (4079, 1), (33023467536964516184101, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753698 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_2, prime_oneHundredTwentyOneDO_3, prime_oneHundredTwentyOneDO_59, prime_oneHundredTwentyOneDO_4079, prime_oneHundredTwentyOneDO_33023467536964516184101]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753699 : Nat.totient 143054292976441513728874753699 = 129964813259090974055484042240 := by
  rw [← show ((([(11, 1), (1579, 1), (70729, 1), (377137, 1), (308765963399027, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753699 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_11, prime_oneHundredTwentyOneDO_1579, prime_oneHundredTwentyOneDO_70729, prime_oneHundredTwentyOneDO_377137, prime_oneHundredTwentyOneDO_308765963399027]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753700 : Nat.totient 143054292976441513728874753700 = 55248554528832584612530938240 := by
  rw [← show ((([(2, 2), (5, 2), (29, 1), (49329066543600521975474053, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753700 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_2, prime_oneHundredTwentyOneDO_5, prime_oneHundredTwentyOneDO_29, prime_oneHundredTwentyOneDO_49329066543600521975474053]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyOneDO_143054292976441513728874753701 : Nat.totient 143054292976441513728874753701 = 94424847388447663932917829120 := by
  rw [← show ((([(3, 1), (157, 1), (281, 1), (216539023, 1), (4991573785810037, 1)] : List FactorBlock).map factorBlockValue).prod) = 143054292976441513728874753701 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyOneDO_3, prime_oneHundredTwentyOneDO_157, prime_oneHundredTwentyOneDO_281, prime_oneHundredTwentyOneDO_216539023, prime_oneHundredTwentyOneDO_4991573785810037]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64OneHundredTwentyOneDO : certifiedKill 1 143054292976441513728874753599 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_oneHundredTwentyOneDO_143054292976441513728874753600, phi_oneHundredTwentyOneDO_143054292976441513728874753601, phi_oneHundredTwentyOneDO_143054292976441513728874753602,
    phi_oneHundredTwentyOneDO_143054292976441513728874753603, phi_oneHundredTwentyOneDO_143054292976441513728874753604, phi_oneHundredTwentyOneDO_143054292976441513728874753605,
    phi_oneHundredTwentyOneDO_143054292976441513728874753606, phi_oneHundredTwentyOneDO_143054292976441513728874753607, phi_oneHundredTwentyOneDO_143054292976441513728874753608,
    phi_oneHundredTwentyOneDO_143054292976441513728874753609, phi_oneHundredTwentyOneDO_143054292976441513728874753610, phi_oneHundredTwentyOneDO_143054292976441513728874753611,
    phi_oneHundredTwentyOneDO_143054292976441513728874753612, phi_oneHundredTwentyOneDO_143054292976441513728874753613, phi_oneHundredTwentyOneDO_143054292976441513728874753614,
    phi_oneHundredTwentyOneDO_143054292976441513728874753615, phi_oneHundredTwentyOneDO_143054292976441513728874753616, phi_oneHundredTwentyOneDO_143054292976441513728874753617,
    phi_oneHundredTwentyOneDO_143054292976441513728874753618, phi_oneHundredTwentyOneDO_143054292976441513728874753619, phi_oneHundredTwentyOneDO_143054292976441513728874753620,
    phi_oneHundredTwentyOneDO_143054292976441513728874753621, phi_oneHundredTwentyOneDO_143054292976441513728874753622, phi_oneHundredTwentyOneDO_143054292976441513728874753623,
    phi_oneHundredTwentyOneDO_143054292976441513728874753624, phi_oneHundredTwentyOneDO_143054292976441513728874753625, phi_oneHundredTwentyOneDO_143054292976441513728874753626,
    phi_oneHundredTwentyOneDO_143054292976441513728874753627, phi_oneHundredTwentyOneDO_143054292976441513728874753628, phi_oneHundredTwentyOneDO_143054292976441513728874753629,
    phi_oneHundredTwentyOneDO_143054292976441513728874753630, phi_oneHundredTwentyOneDO_143054292976441513728874753631, phi_oneHundredTwentyOneDO_143054292976441513728874753632,
    phi_oneHundredTwentyOneDO_143054292976441513728874753633, phi_oneHundredTwentyOneDO_143054292976441513728874753634, phi_oneHundredTwentyOneDO_143054292976441513728874753635,
    phi_oneHundredTwentyOneDO_143054292976441513728874753636, phi_oneHundredTwentyOneDO_143054292976441513728874753637, phi_oneHundredTwentyOneDO_143054292976441513728874753638,
    phi_oneHundredTwentyOneDO_143054292976441513728874753639, phi_oneHundredTwentyOneDO_143054292976441513728874753640, phi_oneHundredTwentyOneDO_143054292976441513728874753641,
    phi_oneHundredTwentyOneDO_143054292976441513728874753642, phi_oneHundredTwentyOneDO_143054292976441513728874753643, phi_oneHundredTwentyOneDO_143054292976441513728874753644,
    phi_oneHundredTwentyOneDO_143054292976441513728874753645, phi_oneHundredTwentyOneDO_143054292976441513728874753646, phi_oneHundredTwentyOneDO_143054292976441513728874753647,
    phi_oneHundredTwentyOneDO_143054292976441513728874753648, phi_oneHundredTwentyOneDO_143054292976441513728874753649, phi_oneHundredTwentyOneDO_143054292976441513728874753650,
    phi_oneHundredTwentyOneDO_143054292976441513728874753651, phi_oneHundredTwentyOneDO_143054292976441513728874753652, phi_oneHundredTwentyOneDO_143054292976441513728874753653,
    phi_oneHundredTwentyOneDO_143054292976441513728874753654, phi_oneHundredTwentyOneDO_143054292976441513728874753655, phi_oneHundredTwentyOneDO_143054292976441513728874753656,
    phi_oneHundredTwentyOneDO_143054292976441513728874753657, phi_oneHundredTwentyOneDO_143054292976441513728874753658, phi_oneHundredTwentyOneDO_143054292976441513728874753659,
    phi_oneHundredTwentyOneDO_143054292976441513728874753660, phi_oneHundredTwentyOneDO_143054292976441513728874753661, phi_oneHundredTwentyOneDO_143054292976441513728874753662,
    phi_oneHundredTwentyOneDO_143054292976441513728874753663, phi_oneHundredTwentyOneDO_143054292976441513728874753664, phi_oneHundredTwentyOneDO_143054292976441513728874753665,
    phi_oneHundredTwentyOneDO_143054292976441513728874753666, phi_oneHundredTwentyOneDO_143054292976441513728874753667, phi_oneHundredTwentyOneDO_143054292976441513728874753668,
    phi_oneHundredTwentyOneDO_143054292976441513728874753669, phi_oneHundredTwentyOneDO_143054292976441513728874753670, phi_oneHundredTwentyOneDO_143054292976441513728874753671,
    phi_oneHundredTwentyOneDO_143054292976441513728874753672, phi_oneHundredTwentyOneDO_143054292976441513728874753673, phi_oneHundredTwentyOneDO_143054292976441513728874753674,
    phi_oneHundredTwentyOneDO_143054292976441513728874753675, phi_oneHundredTwentyOneDO_143054292976441513728874753676, phi_oneHundredTwentyOneDO_143054292976441513728874753677,
    phi_oneHundredTwentyOneDO_143054292976441513728874753678, phi_oneHundredTwentyOneDO_143054292976441513728874753679, phi_oneHundredTwentyOneDO_143054292976441513728874753680,
    phi_oneHundredTwentyOneDO_143054292976441513728874753681, phi_oneHundredTwentyOneDO_143054292976441513728874753682, phi_oneHundredTwentyOneDO_143054292976441513728874753683,
    phi_oneHundredTwentyOneDO_143054292976441513728874753684, phi_oneHundredTwentyOneDO_143054292976441513728874753685, phi_oneHundredTwentyOneDO_143054292976441513728874753686,
    phi_oneHundredTwentyOneDO_143054292976441513728874753687, phi_oneHundredTwentyOneDO_143054292976441513728874753688, phi_oneHundredTwentyOneDO_143054292976441513728874753689,
    phi_oneHundredTwentyOneDO_143054292976441513728874753690, phi_oneHundredTwentyOneDO_143054292976441513728874753691, phi_oneHundredTwentyOneDO_143054292976441513728874753692,
    phi_oneHundredTwentyOneDO_143054292976441513728874753693, phi_oneHundredTwentyOneDO_143054292976441513728874753694, phi_oneHundredTwentyOneDO_143054292976441513728874753695,
    phi_oneHundredTwentyOneDO_143054292976441513728874753696, phi_oneHundredTwentyOneDO_143054292976441513728874753697, phi_oneHundredTwentyOneDO_143054292976441513728874753698,
    phi_oneHundredTwentyOneDO_143054292976441513728874753699, phi_oneHundredTwentyOneDO_143054292976441513728874753700, phi_oneHundredTwentyOneDO_143054292976441513728874753701
    ]

end TotientTailPeriodKiller
end Erdos249257
