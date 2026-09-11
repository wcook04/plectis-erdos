import Erdos249257.DiagonalPincerCertificatesT64

/- Kernel-checked off-diagonal certificate at a freely chosen position. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def oneHundredFiftyFourEVFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem oneHundredFiftyFourEVFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : oneHundredFiftyFourEVFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [oneHundredFiftyFourEVFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [oneHundredFiftyFourEVFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then oneHundredFiftyFourEVFastPow a n * oneHundredFiftyFourEVFastPow a n * a else oneHundredFiftyFourEVFastPow a n * oneHundredFiftyFourEVFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_oneHundredFiftyFourEV_2 : Nat.Prime 2 := by norm_num

private theorem prime_oneHundredFiftyFourEV_3 : Nat.Prime 3 := by norm_num

private theorem prime_oneHundredFiftyFourEV_5 : Nat.Prime 5 := by norm_num

private theorem prime_oneHundredFiftyFourEV_7 : Nat.Prime 7 := by norm_num

private theorem prime_oneHundredFiftyFourEV_11 : Nat.Prime 11 := by norm_num

private theorem prime_oneHundredFiftyFourEV_13 : Nat.Prime 13 := by norm_num

private theorem prime_oneHundredFiftyFourEV_17 : Nat.Prime 17 := by norm_num

private theorem prime_oneHundredFiftyFourEV_19 : Nat.Prime 19 := by norm_num

private theorem prime_oneHundredFiftyFourEV_23 : Nat.Prime 23 := by norm_num

private theorem prime_oneHundredFiftyFourEV_29 : Nat.Prime 29 := by norm_num

private theorem prime_oneHundredFiftyFourEV_31 : Nat.Prime 31 := by norm_num

private theorem prime_oneHundredFiftyFourEV_37 : Nat.Prime 37 := by norm_num

private theorem prime_oneHundredFiftyFourEV_41 : Nat.Prime 41 := by norm_num

private theorem prime_oneHundredFiftyFourEV_43 : Nat.Prime 43 := by norm_num

private theorem prime_oneHundredFiftyFourEV_47 : Nat.Prime 47 := by norm_num

private theorem prime_oneHundredFiftyFourEV_53 : Nat.Prime 53 := by norm_num

private theorem prime_oneHundredFiftyFourEV_59 : Nat.Prime 59 := by norm_num

private theorem prime_oneHundredFiftyFourEV_61 : Nat.Prime 61 := by norm_num

private theorem prime_oneHundredFiftyFourEV_67 : Nat.Prime 67 := by norm_num

private theorem prime_oneHundredFiftyFourEV_71 : Nat.Prime 71 := by norm_num

private theorem prime_oneHundredFiftyFourEV_73 : Nat.Prime 73 := by norm_num

private theorem prime_oneHundredFiftyFourEV_79 : Nat.Prime 79 := by norm_num

private theorem prime_oneHundredFiftyFourEV_83 : Nat.Prime 83 := by norm_num

private theorem prime_oneHundredFiftyFourEV_89 : Nat.Prime 89 := by norm_num

private theorem prime_oneHundredFiftyFourEV_97 : Nat.Prime 97 := by norm_num

private theorem prime_oneHundredFiftyFourEV_101 : Nat.Prime 101 := by norm_num

private theorem prime_oneHundredFiftyFourEV_103 : Nat.Prime 103 := by norm_num

private theorem prime_oneHundredFiftyFourEV_107 : Nat.Prime 107 := by norm_num

private theorem prime_oneHundredFiftyFourEV_109 : Nat.Prime 109 := by norm_num

private theorem prime_oneHundredFiftyFourEV_113 : Nat.Prime 113 := by norm_num

private theorem prime_oneHundredFiftyFourEV_127 : Nat.Prime 127 := by norm_num

private theorem prime_oneHundredFiftyFourEV_131 : Nat.Prime 131 := by norm_num

private theorem prime_oneHundredFiftyFourEV_137 : Nat.Prime 137 := by norm_num

private theorem prime_oneHundredFiftyFourEV_139 : Nat.Prime 139 := by norm_num

private theorem prime_oneHundredFiftyFourEV_149 : Nat.Prime 149 := by norm_num

private theorem prime_oneHundredFiftyFourEV_151 : Nat.Prime 151 := by norm_num

private theorem prime_oneHundredFiftyFourEV_157 : Nat.Prime 157 := by norm_num

private theorem prime_oneHundredFiftyFourEV_163 : Nat.Prime 163 := by norm_num

private theorem prime_oneHundredFiftyFourEV_167 : Nat.Prime 167 := by norm_num

private theorem prime_oneHundredFiftyFourEV_173 : Nat.Prime 173 := by norm_num

private theorem prime_oneHundredFiftyFourEV_179 : Nat.Prime 179 := by norm_num

private theorem prime_oneHundredFiftyFourEV_181 : Nat.Prime 181 := by norm_num

private theorem prime_oneHundredFiftyFourEV_191 : Nat.Prime 191 := by norm_num

private theorem prime_oneHundredFiftyFourEV_193 : Nat.Prime 193 := by norm_num

private theorem prime_oneHundredFiftyFourEV_197 : Nat.Prime 197 := by norm_num

private theorem prime_oneHundredFiftyFourEV_199 : Nat.Prime 199 := by norm_num

private theorem prime_oneHundredFiftyFourEV_211 : Nat.Prime 211 := by norm_num

private theorem prime_oneHundredFiftyFourEV_223 : Nat.Prime 223 := by norm_num

private theorem prime_oneHundredFiftyFourEV_227 : Nat.Prime 227 := by norm_num

private theorem prime_oneHundredFiftyFourEV_233 : Nat.Prime 233 := by norm_num

private theorem prime_oneHundredFiftyFourEV_239 : Nat.Prime 239 := by norm_num

private theorem prime_oneHundredFiftyFourEV_241 : Nat.Prime 241 := by norm_num

private theorem prime_oneHundredFiftyFourEV_251 : Nat.Prime 251 := by norm_num

private theorem prime_oneHundredFiftyFourEV_257 : Nat.Prime 257 := by norm_num

private theorem prime_oneHundredFiftyFourEV_263 : Nat.Prime 263 := by norm_num

private theorem prime_oneHundredFiftyFourEV_277 : Nat.Prime 277 := by norm_num

private theorem prime_oneHundredFiftyFourEV_281 : Nat.Prime 281 := by norm_num

private theorem prime_oneHundredFiftyFourEV_293 : Nat.Prime 293 := by norm_num

private theorem prime_oneHundredFiftyFourEV_311 : Nat.Prime 311 := by norm_num

private theorem prime_oneHundredFiftyFourEV_313 : Nat.Prime 313 := by norm_num

private theorem prime_oneHundredFiftyFourEV_317 : Nat.Prime 317 := by norm_num

private theorem prime_oneHundredFiftyFourEV_331 : Nat.Prime 331 := by norm_num

private theorem prime_oneHundredFiftyFourEV_337 : Nat.Prime 337 := by norm_num

private theorem prime_oneHundredFiftyFourEV_347 : Nat.Prime 347 := by norm_num

private theorem prime_oneHundredFiftyFourEV_349 : Nat.Prime 349 := by norm_num

private theorem prime_oneHundredFiftyFourEV_353 : Nat.Prime 353 := by norm_num

private theorem prime_oneHundredFiftyFourEV_359 : Nat.Prime 359 := by norm_num

private theorem prime_oneHundredFiftyFourEV_373 : Nat.Prime 373 := by norm_num

private theorem prime_oneHundredFiftyFourEV_379 : Nat.Prime 379 := by norm_num

private theorem prime_oneHundredFiftyFourEV_383 : Nat.Prime 383 := by norm_num

private theorem prime_oneHundredFiftyFourEV_389 : Nat.Prime 389 := by norm_num

private theorem prime_oneHundredFiftyFourEV_397 : Nat.Prime 397 := by norm_num

private theorem prime_oneHundredFiftyFourEV_409 : Nat.Prime 409 := by norm_num

private theorem prime_oneHundredFiftyFourEV_421 : Nat.Prime 421 := by norm_num

private theorem prime_oneHundredFiftyFourEV_433 : Nat.Prime 433 := by norm_num

private theorem prime_oneHundredFiftyFourEV_461 : Nat.Prime 461 := by norm_num

private theorem prime_oneHundredFiftyFourEV_463 : Nat.Prime 463 := by norm_num

private theorem prime_oneHundredFiftyFourEV_479 : Nat.Prime 479 := by norm_num

private theorem prime_oneHundredFiftyFourEV_487 : Nat.Prime 487 := by norm_num

private theorem prime_oneHundredFiftyFourEV_491 : Nat.Prime 491 := by norm_num

private theorem prime_oneHundredFiftyFourEV_499 : Nat.Prime 499 := by norm_num

private theorem prime_oneHundredFiftyFourEV_503 : Nat.Prime 503 := by norm_num

private theorem prime_oneHundredFiftyFourEV_521 : Nat.Prime 521 := by norm_num

private theorem prime_oneHundredFiftyFourEV_523 : Nat.Prime 523 := by norm_num

private theorem prime_oneHundredFiftyFourEV_541 : Nat.Prime 541 := by norm_num

private theorem prime_oneHundredFiftyFourEV_587 : Nat.Prime 587 := by norm_num

private theorem prime_oneHundredFiftyFourEV_593 : Nat.Prime 593 := by norm_num

private theorem prime_oneHundredFiftyFourEV_607 : Nat.Prime 607 := by norm_num

private theorem prime_oneHundredFiftyFourEV_647 : Nat.Prime 647 := by norm_num

private theorem prime_oneHundredFiftyFourEV_659 : Nat.Prime 659 := by norm_num

private theorem prime_oneHundredFiftyFourEV_677 : Nat.Prime 677 := by norm_num

private theorem prime_oneHundredFiftyFourEV_691 : Nat.Prime 691 := by norm_num

private theorem prime_oneHundredFiftyFourEV_701 : Nat.Prime 701 := by norm_num

private theorem prime_oneHundredFiftyFourEV_709 : Nat.Prime 709 := by norm_num

private theorem prime_oneHundredFiftyFourEV_719 : Nat.Prime 719 := by norm_num

private theorem prime_oneHundredFiftyFourEV_739 : Nat.Prime 739 := by norm_num

private theorem prime_oneHundredFiftyFourEV_757 : Nat.Prime 757 := by norm_num

private theorem prime_oneHundredFiftyFourEV_761 : Nat.Prime 761 := by norm_num

private theorem prime_oneHundredFiftyFourEV_769 : Nat.Prime 769 := by norm_num

private theorem prime_oneHundredFiftyFourEV_797 : Nat.Prime 797 := by norm_num

private theorem prime_oneHundredFiftyFourEV_811 : Nat.Prime 811 := by norm_num

private theorem prime_oneHundredFiftyFourEV_827 : Nat.Prime 827 := by norm_num

private theorem prime_oneHundredFiftyFourEV_857 : Nat.Prime 857 := by norm_num

private theorem prime_oneHundredFiftyFourEV_859 : Nat.Prime 859 := by norm_num

private theorem prime_oneHundredFiftyFourEV_877 : Nat.Prime 877 := by norm_num

private theorem prime_oneHundredFiftyFourEV_883 : Nat.Prime 883 := by norm_num

private theorem prime_oneHundredFiftyFourEV_907 : Nat.Prime 907 := by norm_num

private theorem prime_oneHundredFiftyFourEV_919 : Nat.Prime 919 := by norm_num

private theorem prime_oneHundredFiftyFourEV_983 : Nat.Prime 983 := by norm_num

private theorem prime_oneHundredFiftyFourEV_1013 : Nat.Prime 1013 := by norm_num

private theorem prime_oneHundredFiftyFourEV_1019 : Nat.Prime 1019 := by norm_num

private theorem prime_oneHundredFiftyFourEV_1097 : Nat.Prime 1097 := by norm_num

private theorem prime_oneHundredFiftyFourEV_1109 : Nat.Prime 1109 := by norm_num

private theorem prime_oneHundredFiftyFourEV_1117 : Nat.Prime 1117 := by norm_num

private theorem prime_oneHundredFiftyFourEV_1193 : Nat.Prime 1193 := by norm_num

private theorem prime_oneHundredFiftyFourEV_1201 : Nat.Prime 1201 := by norm_num

private theorem prime_oneHundredFiftyFourEV_1213 : Nat.Prime 1213 := by norm_num

private theorem prime_oneHundredFiftyFourEV_1249 : Nat.Prime 1249 := by norm_num

private theorem prime_oneHundredFiftyFourEV_1277 : Nat.Prime 1277 := by norm_num

private theorem prime_oneHundredFiftyFourEV_1279 : Nat.Prime 1279 := by norm_num

private theorem prime_oneHundredFiftyFourEV_1283 : Nat.Prime 1283 := by norm_num

private theorem prime_oneHundredFiftyFourEV_1289 : Nat.Prime 1289 := by norm_num

private theorem prime_oneHundredFiftyFourEV_1301 : Nat.Prime 1301 := by norm_num

private theorem prime_oneHundredFiftyFourEV_1321 : Nat.Prime 1321 := by norm_num

private theorem prime_oneHundredFiftyFourEV_1327 : Nat.Prime 1327 := by norm_num

private theorem prime_oneHundredFiftyFourEV_1367 : Nat.Prime 1367 := by norm_num

private theorem prime_oneHundredFiftyFourEV_1373 : Nat.Prime 1373 := by norm_num

private theorem prime_oneHundredFiftyFourEV_1439 : Nat.Prime 1439 := by norm_num

private theorem prime_oneHundredFiftyFourEV_1451 : Nat.Prime 1451 := by norm_num

private theorem prime_oneHundredFiftyFourEV_1483 : Nat.Prime 1483 := by norm_num

private theorem prime_oneHundredFiftyFourEV_1487 : Nat.Prime 1487 := by norm_num

private theorem prime_oneHundredFiftyFourEV_1493 : Nat.Prime 1493 := by norm_num

private theorem prime_oneHundredFiftyFourEV_1511 : Nat.Prime 1511 := by norm_num

private theorem prime_oneHundredFiftyFourEV_1579 : Nat.Prime 1579 := by norm_num

private theorem prime_oneHundredFiftyFourEV_1583 : Nat.Prime 1583 := by norm_num

private theorem prime_oneHundredFiftyFourEV_1663 : Nat.Prime 1663 := by norm_num

private theorem prime_oneHundredFiftyFourEV_1667 : Nat.Prime 1667 := by norm_num

private theorem prime_oneHundredFiftyFourEV_1669 : Nat.Prime 1669 := by norm_num

private theorem prime_oneHundredFiftyFourEV_1693 : Nat.Prime 1693 := by norm_num

private theorem prime_oneHundredFiftyFourEV_1783 : Nat.Prime 1783 := by norm_num

private theorem prime_oneHundredFiftyFourEV_1811 : Nat.Prime 1811 := by norm_num

private theorem prime_oneHundredFiftyFourEV_1831 : Nat.Prime 1831 := by norm_num

private theorem prime_oneHundredFiftyFourEV_1889 : Nat.Prime 1889 := by norm_num

private theorem prime_oneHundredFiftyFourEV_1907 : Nat.Prime 1907 := by norm_num

private theorem prime_oneHundredFiftyFourEV_1913 : Nat.Prime 1913 := by norm_num

private theorem prime_oneHundredFiftyFourEV_1951 : Nat.Prime 1951 := by norm_num

private theorem prime_oneHundredFiftyFourEV_2027 : Nat.Prime 2027 := by norm_num

private theorem prime_oneHundredFiftyFourEV_2069 : Nat.Prime 2069 := by norm_num

private theorem prime_oneHundredFiftyFourEV_2137 : Nat.Prime 2137 := by norm_num

private theorem prime_oneHundredFiftyFourEV_2141 : Nat.Prime 2141 := by norm_num

private theorem prime_oneHundredFiftyFourEV_2161 : Nat.Prime 2161 := by norm_num

private theorem prime_oneHundredFiftyFourEV_2269 : Nat.Prime 2269 := by norm_num

private theorem prime_oneHundredFiftyFourEV_2339 : Nat.Prime 2339 := by norm_num

private theorem prime_oneHundredFiftyFourEV_2347 : Nat.Prime 2347 := by norm_num

private theorem prime_oneHundredFiftyFourEV_2377 : Nat.Prime 2377 := by norm_num

private theorem prime_oneHundredFiftyFourEV_2389 : Nat.Prime 2389 := by norm_num

private theorem prime_oneHundredFiftyFourEV_2411 : Nat.Prime 2411 := by norm_num

private theorem prime_oneHundredFiftyFourEV_2579 : Nat.Prime 2579 := by norm_num

private theorem prime_oneHundredFiftyFourEV_2633 : Nat.Prime 2633 := by norm_num

private theorem prime_oneHundredFiftyFourEV_2731 : Nat.Prime 2731 := by norm_num

private theorem prime_oneHundredFiftyFourEV_2789 : Nat.Prime 2789 := by norm_num

private theorem prime_oneHundredFiftyFourEV_2797 : Nat.Prime 2797 := by norm_num

private theorem prime_oneHundredFiftyFourEV_2819 : Nat.Prime 2819 := by norm_num

private theorem prime_oneHundredFiftyFourEV_3191 : Nat.Prime 3191 := by norm_num

private theorem prime_oneHundredFiftyFourEV_3229 : Nat.Prime 3229 := by norm_num

private theorem prime_oneHundredFiftyFourEV_3359 : Nat.Prime 3359 := by norm_num

private theorem prime_oneHundredFiftyFourEV_3413 : Nat.Prime 3413 := by norm_num

private theorem prime_oneHundredFiftyFourEV_3457 : Nat.Prime 3457 := by norm_num

private theorem prime_oneHundredFiftyFourEV_3631 : Nat.Prime 3631 := by norm_num

private theorem prime_oneHundredFiftyFourEV_3659 : Nat.Prime 3659 := by norm_num

private theorem prime_oneHundredFiftyFourEV_3671 : Nat.Prime 3671 := by norm_num

private theorem prime_oneHundredFiftyFourEV_3931 : Nat.Prime 3931 := by norm_num

private theorem prime_oneHundredFiftyFourEV_4021 : Nat.Prime 4021 := by norm_num

private theorem prime_oneHundredFiftyFourEV_4073 : Nat.Prime 4073 := by norm_num

private theorem prime_oneHundredFiftyFourEV_4133 : Nat.Prime 4133 := by norm_num

private theorem prime_oneHundredFiftyFourEV_4273 : Nat.Prime 4273 := by norm_num

private theorem prime_oneHundredFiftyFourEV_4421 : Nat.Prime 4421 := by norm_num

private theorem prime_oneHundredFiftyFourEV_4547 : Nat.Prime 4547 := by norm_num

private theorem prime_oneHundredFiftyFourEV_4603 : Nat.Prime 4603 := by norm_num

private theorem prime_oneHundredFiftyFourEV_4703 : Nat.Prime 4703 := by norm_num

private theorem prime_oneHundredFiftyFourEV_4801 : Nat.Prime 4801 := by norm_num

private theorem prime_oneHundredFiftyFourEV_4871 : Nat.Prime 4871 := by norm_num

private theorem prime_oneHundredFiftyFourEV_5683 : Nat.Prime 5683 := by norm_num

private theorem prime_oneHundredFiftyFourEV_5783 : Nat.Prime 5783 := by norm_num

private theorem prime_oneHundredFiftyFourEV_5851 : Nat.Prime 5851 := by norm_num

private theorem prime_oneHundredFiftyFourEV_5923 : Nat.Prime 5923 := by norm_num

private theorem prime_oneHundredFiftyFourEV_6133 : Nat.Prime 6133 := by norm_num

private theorem prime_oneHundredFiftyFourEV_6389 : Nat.Prime 6389 := by norm_num

private theorem prime_oneHundredFiftyFourEV_6451 : Nat.Prime 6451 := by norm_num

private theorem prime_oneHundredFiftyFourEV_6619 : Nat.Prime 6619 := by norm_num

private theorem prime_oneHundredFiftyFourEV_6637 : Nat.Prime 6637 := by norm_num

private theorem prime_oneHundredFiftyFourEV_6829 : Nat.Prime 6829 := by norm_num

private theorem prime_oneHundredFiftyFourEV_7027 : Nat.Prime 7027 := by norm_num

private theorem prime_oneHundredFiftyFourEV_7039 : Nat.Prime 7039 := by norm_num

private theorem prime_oneHundredFiftyFourEV_7187 : Nat.Prime 7187 := by norm_num

private theorem prime_oneHundredFiftyFourEV_7213 : Nat.Prime 7213 := by norm_num

private theorem prime_oneHundredFiftyFourEV_7307 : Nat.Prime 7307 := by norm_num

private theorem prime_oneHundredFiftyFourEV_7591 : Nat.Prime 7591 := by norm_num

private theorem prime_oneHundredFiftyFourEV_7823 : Nat.Prime 7823 := by norm_num

private theorem prime_oneHundredFiftyFourEV_8237 : Nat.Prime 8237 := by norm_num

private theorem prime_oneHundredFiftyFourEV_8263 : Nat.Prime 8263 := by norm_num

private theorem prime_oneHundredFiftyFourEV_8273 : Nat.Prime 8273 := by norm_num

private theorem prime_oneHundredFiftyFourEV_8287 : Nat.Prime 8287 := by norm_num

private theorem prime_oneHundredFiftyFourEV_8317 : Nat.Prime 8317 := by norm_num

private theorem prime_oneHundredFiftyFourEV_8647 : Nat.Prime 8647 := by norm_num

private theorem prime_oneHundredFiftyFourEV_8707 : Nat.Prime 8707 := by norm_num

private theorem prime_oneHundredFiftyFourEV_8741 : Nat.Prime 8741 := by norm_num

private theorem prime_oneHundredFiftyFourEV_9011 : Nat.Prime 9011 := by norm_num

private theorem prime_oneHundredFiftyFourEV_9769 : Nat.Prime 9769 := by norm_num

private theorem prime_oneHundredFiftyFourEV_9787 : Nat.Prime 9787 := by norm_num

private theorem prime_oneHundredFiftyFourEV_10211 : Nat.Prime 10211 := by norm_num

private theorem prime_oneHundredFiftyFourEV_11789 : Nat.Prime 11789 := by norm_num

private theorem prime_oneHundredFiftyFourEV_12893 : Nat.Prime 12893 := by norm_num

private theorem prime_oneHundredFiftyFourEV_13751 : Nat.Prime 13751 := by norm_num

private theorem prime_oneHundredFiftyFourEV_13859 : Nat.Prime 13859 := by norm_num

private theorem prime_oneHundredFiftyFourEV_13873 : Nat.Prime 13873 := by norm_num

private theorem prime_oneHundredFiftyFourEV_14771 : Nat.Prime 14771 := by norm_num

private theorem prime_oneHundredFiftyFourEV_15569 : Nat.Prime 15569 := by norm_num

private theorem prime_oneHundredFiftyFourEV_15773 : Nat.Prime 15773 := by norm_num

private theorem prime_oneHundredFiftyFourEV_15817 : Nat.Prime 15817 := by norm_num

private theorem prime_oneHundredFiftyFourEV_15877 : Nat.Prime 15877 := by norm_num

private theorem prime_oneHundredFiftyFourEV_16339 : Nat.Prime 16339 := by norm_num

private theorem prime_oneHundredFiftyFourEV_16573 : Nat.Prime 16573 := by norm_num

private theorem prime_oneHundredFiftyFourEV_16787 : Nat.Prime 16787 := by norm_num

private theorem prime_oneHundredFiftyFourEV_17203 : Nat.Prime 17203 := by norm_num

private theorem prime_oneHundredFiftyFourEV_17207 : Nat.Prime 17207 := by norm_num

private theorem prime_oneHundredFiftyFourEV_17389 : Nat.Prime 17389 := by norm_num

private theorem prime_oneHundredFiftyFourEV_17509 : Nat.Prime 17509 := by norm_num

private theorem prime_oneHundredFiftyFourEV_17609 : Nat.Prime 17609 := by norm_num

private theorem prime_oneHundredFiftyFourEV_18143 : Nat.Prime 18143 := by norm_num

private theorem prime_oneHundredFiftyFourEV_18541 : Nat.Prime 18541 := by norm_num

private theorem prime_oneHundredFiftyFourEV_19417 : Nat.Prime 19417 := by norm_num

private theorem prime_oneHundredFiftyFourEV_19861 : Nat.Prime 19861 := by norm_num

private theorem prime_oneHundredFiftyFourEV_20753 : Nat.Prime 20753 := by norm_num

private theorem prime_oneHundredFiftyFourEV_20773 : Nat.Prime 20773 := by norm_num

private theorem prime_oneHundredFiftyFourEV_21617 : Nat.Prime 21617 := by norm_num

private theorem prime_oneHundredFiftyFourEV_21773 : Nat.Prime 21773 := by norm_num

private theorem prime_oneHundredFiftyFourEV_23431 : Nat.Prime 23431 := by norm_num

private theorem prime_oneHundredFiftyFourEV_23531 : Nat.Prime 23531 := by norm_num

private theorem prime_oneHundredFiftyFourEV_24151 : Nat.Prime 24151 := by norm_num

private theorem prime_oneHundredFiftyFourEV_24439 : Nat.Prime 24439 := by norm_num

private theorem prime_oneHundredFiftyFourEV_25031 : Nat.Prime 25031 := by norm_num

private theorem prime_oneHundredFiftyFourEV_25703 : Nat.Prime 25703 := by norm_num

private theorem prime_oneHundredFiftyFourEV_26399 : Nat.Prime 26399 := by norm_num

private theorem prime_oneHundredFiftyFourEV_27583 : Nat.Prime 27583 := by norm_num

private theorem prime_oneHundredFiftyFourEV_28513 : Nat.Prime 28513 := by norm_num

private theorem prime_oneHundredFiftyFourEV_29501 : Nat.Prime 29501 := by norm_num

private theorem prime_oneHundredFiftyFourEV_33179 : Nat.Prime 33179 := by norm_num

private theorem prime_oneHundredFiftyFourEV_34487 : Nat.Prime 34487 := by norm_num

private theorem prime_oneHundredFiftyFourEV_34543 : Nat.Prime 34543 := by norm_num

private theorem prime_oneHundredFiftyFourEV_35879 : Nat.Prime 35879 := by norm_num

private theorem prime_oneHundredFiftyFourEV_36671 : Nat.Prime 36671 := by norm_num

private theorem prime_oneHundredFiftyFourEV_39827 : Nat.Prime 39827 := by norm_num

private theorem prime_oneHundredFiftyFourEV_41729 : Nat.Prime 41729 := by norm_num

private theorem prime_oneHundredFiftyFourEV_42557 : Nat.Prime 42557 := by norm_num

private theorem prime_oneHundredFiftyFourEV_43759 : Nat.Prime 43759 := by norm_num

private theorem prime_oneHundredFiftyFourEV_43777 : Nat.Prime 43777 := by norm_num

private theorem prime_oneHundredFiftyFourEV_44797 : Nat.Prime 44797 := by norm_num

private theorem prime_oneHundredFiftyFourEV_48017 : Nat.Prime 48017 := by norm_num

private theorem prime_oneHundredFiftyFourEV_52879 : Nat.Prime 52879 := by norm_num

private theorem prime_oneHundredFiftyFourEV_53959 : Nat.Prime 53959 := by norm_num

private theorem prime_oneHundredFiftyFourEV_54287 : Nat.Prime 54287 := by norm_num

private theorem prime_oneHundredFiftyFourEV_61471 : Nat.Prime 61471 := by norm_num

private theorem prime_oneHundredFiftyFourEV_63337 : Nat.Prime 63337 := by norm_num

private theorem prime_oneHundredFiftyFourEV_65033 : Nat.Prime 65033 := by norm_num

private theorem prime_oneHundredFiftyFourEV_65881 : Nat.Prime 65881 := by norm_num

private theorem prime_oneHundredFiftyFourEV_68351 : Nat.Prime 68351 := by norm_num

private theorem prime_oneHundredFiftyFourEV_69997 : Nat.Prime 69997 := by norm_num

private theorem prime_oneHundredFiftyFourEV_70207 : Nat.Prime 70207 := by norm_num

private theorem prime_oneHundredFiftyFourEV_70289 : Nat.Prime 70289 := by norm_num

private theorem prime_oneHundredFiftyFourEV_75743 : Nat.Prime 75743 := by norm_num

private theorem prime_oneHundredFiftyFourEV_76249 : Nat.Prime 76249 := by norm_num

private theorem prime_oneHundredFiftyFourEV_76387 : Nat.Prime 76387 := by norm_num

private theorem prime_oneHundredFiftyFourEV_82483 : Nat.Prime 82483 := by norm_num

private theorem prime_oneHundredFiftyFourEV_83561 : Nat.Prime 83561 := by norm_num

private theorem prime_oneHundredFiftyFourEV_83639 : Nat.Prime 83639 := by norm_num

private theorem prime_oneHundredFiftyFourEV_86381 : Nat.Prime 86381 := by norm_num

private theorem prime_oneHundredFiftyFourEV_91199 : Nat.Prime 91199 := by norm_num

private theorem prime_oneHundredFiftyFourEV_96001 : Nat.Prime 96001 := by norm_num

private theorem prime_oneHundredFiftyFourEV_100769 : Nat.Prime 100769 := by norm_num

private theorem prime_oneHundredFiftyFourEV_103549 : Nat.Prime 103549 := by norm_num

private theorem prime_oneHundredFiftyFourEV_105407 : Nat.Prime 105407 := by norm_num

private theorem prime_oneHundredFiftyFourEV_110083 : Nat.Prime 110083 := by norm_num

private theorem prime_oneHundredFiftyFourEV_118297 : Nat.Prime 118297 := by norm_num

private theorem prime_oneHundredFiftyFourEV_123701 : Nat.Prime 123701 := by norm_num

private theorem prime_oneHundredFiftyFourEV_137279 : Nat.Prime 137279 := by norm_num

private theorem prime_oneHundredFiftyFourEV_137993 : Nat.Prime 137993 := by norm_num

private theorem prime_oneHundredFiftyFourEV_138739 : Nat.Prime 138739 := by norm_num

private theorem prime_oneHundredFiftyFourEV_141707 : Nat.Prime 141707 := by norm_num

private theorem prime_oneHundredFiftyFourEV_141793 : Nat.Prime 141793 := by norm_num

private theorem prime_oneHundredFiftyFourEV_143419 : Nat.Prime 143419 := by norm_num

private theorem prime_oneHundredFiftyFourEV_145829 : Nat.Prime 145829 := by norm_num

private theorem prime_oneHundredFiftyFourEV_152879 : Nat.Prime 152879 := by norm_num

private theorem prime_oneHundredFiftyFourEV_162263 : Nat.Prime 162263 := by norm_num

private theorem prime_oneHundredFiftyFourEV_171401 : Nat.Prime 171401 := by norm_num

private theorem prime_oneHundredFiftyFourEV_180233 : Nat.Prime 180233 := by norm_num

private theorem prime_oneHundredFiftyFourEV_184409 : Nat.Prime 184409 := by norm_num

private theorem prime_oneHundredFiftyFourEV_188941 : Nat.Prime 188941 := by norm_num

private theorem prime_oneHundredFiftyFourEV_212117 : Nat.Prime 212117 := by norm_num

private theorem prime_oneHundredFiftyFourEV_220217 : Nat.Prime 220217 := by norm_num

private theorem prime_oneHundredFiftyFourEV_229841 : Nat.Prime 229841 := by norm_num

private theorem prime_oneHundredFiftyFourEV_229949 : Nat.Prime 229949 := by norm_num

private theorem prime_oneHundredFiftyFourEV_244043 : Nat.Prime 244043 := by norm_num

private theorem prime_oneHundredFiftyFourEV_244747 : Nat.Prime 244747 := by norm_num

private theorem prime_oneHundredFiftyFourEV_245711 : Nat.Prime 245711 := by norm_num

private theorem prime_oneHundredFiftyFourEV_248533 : Nat.Prime 248533 := by norm_num

private theorem prime_oneHundredFiftyFourEV_249497 : Nat.Prime 249497 := by norm_num

private theorem prime_oneHundredFiftyFourEV_271163 : Nat.Prime 271163 := by norm_num

private theorem prime_oneHundredFiftyFourEV_277577 : Nat.Prime 277577 := by norm_num

private theorem prime_oneHundredFiftyFourEV_291751 : Nat.Prime 291751 := by norm_num

private theorem prime_oneHundredFiftyFourEV_306529 : Nat.Prime 306529 := by norm_num

private theorem prime_oneHundredFiftyFourEV_331603 : Nat.Prime 331603 := by norm_num

private theorem prime_oneHundredFiftyFourEV_337751 : Nat.Prime 337751 := by norm_num

private theorem prime_oneHundredFiftyFourEV_346111 : Nat.Prime 346111 := by norm_num

private theorem prime_oneHundredFiftyFourEV_357659 : Nat.Prime 357659 := by norm_num

private theorem prime_oneHundredFiftyFourEV_368873 : Nat.Prime 368873 := by norm_num

private theorem prime_oneHundredFiftyFourEV_370679 : Nat.Prime 370679 := by norm_num

private theorem prime_oneHundredFiftyFourEV_374929 : Nat.Prime 374929 := by norm_num

private theorem prime_oneHundredFiftyFourEV_382883 : Nat.Prime 382883 := by norm_num

private theorem prime_oneHundredFiftyFourEV_454231 : Nat.Prime 454231 := by norm_num

private theorem prime_oneHundredFiftyFourEV_477359 : Nat.Prime 477359 := by norm_num

private theorem prime_oneHundredFiftyFourEV_527981 : Nat.Prime 527981 := by norm_num

private theorem prime_oneHundredFiftyFourEV_536491 : Nat.Prime 536491 := by norm_num

private theorem prime_oneHundredFiftyFourEV_592639 : Nat.Prime 592639 := by norm_num

private theorem prime_oneHundredFiftyFourEV_601651 : Nat.Prime 601651 := by norm_num

private theorem prime_oneHundredFiftyFourEV_653647 : Nat.Prime 653647 := by norm_num

private theorem prime_oneHundredFiftyFourEV_674173 : Nat.Prime 674173 := by norm_num

private theorem prime_oneHundredFiftyFourEV_675179 : Nat.Prime 675179 := by norm_num

private theorem prime_oneHundredFiftyFourEV_741721 : Nat.Prime 741721 := by norm_num

private theorem prime_oneHundredFiftyFourEV_758111 : Nat.Prime 758111 := by norm_num

private theorem prime_oneHundredFiftyFourEV_805873 : Nat.Prime 805873 := by norm_num

private theorem prime_oneHundredFiftyFourEV_807523 : Nat.Prime 807523 := by norm_num

private theorem prime_oneHundredFiftyFourEV_849103 : Nat.Prime 849103 := by norm_num

private theorem prime_oneHundredFiftyFourEV_857453 : Nat.Prime 857453 := by norm_num

private theorem prime_oneHundredFiftyFourEV_967427 : Nat.Prime 967427 := by norm_num

private theorem prime_oneHundredFiftyFourEV_980393 : Nat.Prime 980393 := by norm_num

private theorem prime_oneHundredFiftyFourEV_985729 : Nat.Prime 985729 := by norm_num

private theorem prime_oneHundredFiftyFourEV_1024669 : Nat.Prime 1024669 := by norm_num

private theorem prime_oneHundredFiftyFourEV_1116593 : Nat.Prime 1116593 := by norm_num

private theorem prime_oneHundredFiftyFourEV_1133947 : Nat.Prime 1133947 := by norm_num

private theorem prime_oneHundredFiftyFourEV_1159259 : Nat.Prime 1159259 := by norm_num

private theorem prime_oneHundredFiftyFourEV_1161233 : Nat.Prime 1161233 := by norm_num

private theorem prime_oneHundredFiftyFourEV_1231757 : Nat.Prime 1231757 := by norm_num

private theorem prime_oneHundredFiftyFourEV_1233899 : Nat.Prime 1233899 := by norm_num

private theorem prime_oneHundredFiftyFourEV_1276397 : Nat.Prime 1276397 := by norm_num

private theorem prime_oneHundredFiftyFourEV_1387849 : Nat.Prime 1387849 := by norm_num

private theorem prime_oneHundredFiftyFourEV_1397761 : Nat.Prime 1397761 := by norm_num

private theorem prime_oneHundredFiftyFourEV_1492289 : Nat.Prime 1492289 := by norm_num

private theorem prime_oneHundredFiftyFourEV_1592737 : Nat.Prime 1592737 := by norm_num

private theorem prime_oneHundredFiftyFourEV_1636457 : Nat.Prime 1636457 := by norm_num

private theorem prime_oneHundredFiftyFourEV_1656521 : Nat.Prime 1656521 := by norm_num

private theorem prime_oneHundredFiftyFourEV_1662103 : Nat.Prime 1662103 := by norm_num

private theorem prime_oneHundredFiftyFourEV_1731589 : Nat.Prime 1731589 := by norm_num

private theorem prime_oneHundredFiftyFourEV_1739533 : Nat.Prime 1739533 := by norm_num

private theorem prime_oneHundredFiftyFourEV_1758307 : Nat.Prime 1758307 := by norm_num

private theorem prime_oneHundredFiftyFourEV_1885943 : Nat.Prime 1885943 := by norm_num

private theorem prime_oneHundredFiftyFourEV_2109179 : Nat.Prime 2109179 := by norm_num

private theorem prime_oneHundredFiftyFourEV_2186603 : Nat.Prime 2186603 := by norm_num

private theorem prime_oneHundredFiftyFourEV_2195989 : Nat.Prime 2195989 := by norm_num

private theorem prime_oneHundredFiftyFourEV_2361221 : Nat.Prime 2361221 := by norm_num

private theorem prime_oneHundredFiftyFourEV_2489909 : Nat.Prime 2489909 := by norm_num

private theorem prime_oneHundredFiftyFourEV_2535527 : Nat.Prime 2535527 := by norm_num

private theorem prime_oneHundredFiftyFourEV_2983457 : Nat.Prime 2983457 := by norm_num

private theorem prime_oneHundredFiftyFourEV_2990279 : Nat.Prime 2990279 := by norm_num

private theorem prime_oneHundredFiftyFourEV_3165203 : Nat.Prime 3165203 := by norm_num

private theorem prime_oneHundredFiftyFourEV_3240359 : Nat.Prime 3240359 := by norm_num

private theorem prime_oneHundredFiftyFourEV_3249863 : Nat.Prime 3249863 := by norm_num

private theorem prime_oneHundredFiftyFourEV_3258569 : Nat.Prime 3258569 := by norm_num

private theorem prime_oneHundredFiftyFourEV_3283807 : Nat.Prime 3283807 := by norm_num

private theorem prime_oneHundredFiftyFourEV_3697849 : Nat.Prime 3697849 := by norm_num

private theorem prime_oneHundredFiftyFourEV_3700691 : Nat.Prime 3700691 := by norm_num

private theorem prime_oneHundredFiftyFourEV_3804221 : Nat.Prime 3804221 := by norm_num

private theorem prime_oneHundredFiftyFourEV_3894329 : Nat.Prime 3894329 := by norm_num

private theorem prime_oneHundredFiftyFourEV_4079189 : Nat.Prime 4079189 := by norm_num

private theorem prime_oneHundredFiftyFourEV_4167661 : Nat.Prime 4167661 := by norm_num

private theorem prime_oneHundredFiftyFourEV_4282273 : Nat.Prime 4282273 := by norm_num

private theorem prime_oneHundredFiftyFourEV_4307131 : Nat.Prime 4307131 := by norm_num

private theorem prime_oneHundredFiftyFourEV_4362719 : Nat.Prime 4362719 := by norm_num

private theorem prime_oneHundredFiftyFourEV_5106029 : Nat.Prime 5106029 := by norm_num

private theorem prime_oneHundredFiftyFourEV_5178163 : Nat.Prime 5178163 := by norm_num

private theorem prime_oneHundredFiftyFourEV_5341319 : Nat.Prime 5341319 := by norm_num

private theorem prime_oneHundredFiftyFourEV_5854993 : Nat.Prime 5854993 := by norm_num

private theorem prime_oneHundredFiftyFourEV_5893337 : Nat.Prime 5893337 := by norm_num

private theorem prime_oneHundredFiftyFourEV_6198299 : Nat.Prime 6198299 := by norm_num

private theorem prime_oneHundredFiftyFourEV_6266657 : Nat.Prime 6266657 := by norm_num

private theorem prime_oneHundredFiftyFourEV_6314617 : Nat.Prime 6314617 := by norm_num

private theorem prime_oneHundredFiftyFourEV_6444443 : Nat.Prime 6444443 := by norm_num

private theorem prime_oneHundredFiftyFourEV_6501791 : Nat.Prime 6501791 := by norm_num

private theorem prime_oneHundredFiftyFourEV_6794779 : Nat.Prime 6794779 := by norm_num

private theorem prime_oneHundredFiftyFourEV_6834613 : Nat.Prime 6834613 := by norm_num

private theorem prime_oneHundredFiftyFourEV_6959261 : Nat.Prime 6959261 := by norm_num

private theorem prime_oneHundredFiftyFourEV_7083383 : Nat.Prime 7083383 := by norm_num

private theorem prime_oneHundredFiftyFourEV_7922443 : Nat.Prime 7922443 := by norm_num

private theorem prime_oneHundredFiftyFourEV_8144443 : Nat.Prime 8144443 := by norm_num

private theorem prime_oneHundredFiftyFourEV_8146423 : Nat.Prime 8146423 := by norm_num

private theorem prime_oneHundredFiftyFourEV_8279743 : Nat.Prime 8279743 := by norm_num

private theorem prime_oneHundredFiftyFourEV_8348687 : Nat.Prime 8348687 := by norm_num

private theorem prime_oneHundredFiftyFourEV_8421529 : Nat.Prime 8421529 := by norm_num

private theorem prime_oneHundredFiftyFourEV_9770851 : Nat.Prime 9770851 := by norm_num

private theorem prime_oneHundredFiftyFourEV_10712743 : Nat.Prime 10712743 := by norm_num

private theorem prime_oneHundredFiftyFourEV_10820141 : Nat.Prime 10820141 := by norm_num

private theorem prime_oneHundredFiftyFourEV_11282923 : Nat.Prime 11282923 := by norm_num

private theorem prime_oneHundredFiftyFourEV_11294809 : Nat.Prime 11294809 := by norm_num

private theorem prime_oneHundredFiftyFourEV_12139691 : Nat.Prime 12139691 := by norm_num

private theorem prime_oneHundredFiftyFourEV_12159703 : Nat.Prime 12159703 := by norm_num

private theorem prime_oneHundredFiftyFourEV_12268583 : Nat.Prime 12268583 := by norm_num

private theorem prime_oneHundredFiftyFourEV_12767897 : Nat.Prime 12767897 := by norm_num

private theorem prime_oneHundredFiftyFourEV_12983963 : Nat.Prime 12983963 := by norm_num

private theorem prime_oneHundredFiftyFourEV_13504471 : Nat.Prime 13504471 := by norm_num

private theorem prime_oneHundredFiftyFourEV_13686091 : Nat.Prime 13686091 := by norm_num

private theorem prime_oneHundredFiftyFourEV_13890209 : Nat.Prime 13890209 := by norm_num

private theorem prime_oneHundredFiftyFourEV_14080019 : Nat.Prime 14080019 := by norm_num

private theorem prime_oneHundredFiftyFourEV_14126627 : Nat.Prime 14126627 := by norm_num

private theorem prime_oneHundredFiftyFourEV_15389993 : Nat.Prime 15389993 := by norm_num

private theorem prime_oneHundredFiftyFourEV_15826513 : Nat.Prime 15826513 := by norm_num

private theorem prime_oneHundredFiftyFourEV_18701987 : Nat.Prime 18701987 := by norm_num

private theorem prime_oneHundredFiftyFourEV_18737507 : Nat.Prime 18737507 := by norm_num

private theorem prime_oneHundredFiftyFourEV_19976597 : Nat.Prime 19976597 := by norm_num

private theorem prime_oneHundredFiftyFourEV_20303441 : Nat.Prime 20303441 := by norm_num

private theorem prime_oneHundredFiftyFourEV_21031463 : Nat.Prime 21031463 := by norm_num

private theorem prime_oneHundredFiftyFourEV_22796231 : Nat.Prime 22796231 := by norm_num

private theorem prime_oneHundredFiftyFourEV_28233607 : Nat.Prime 28233607 := by norm_num

private theorem prime_oneHundredFiftyFourEV_28250711 : Nat.Prime 28250711 := by norm_num

private theorem prime_oneHundredFiftyFourEV_29923811 : Nat.Prime 29923811 := by norm_num

private theorem prime_oneHundredFiftyFourEV_30612443 : Nat.Prime 30612443 := by
  apply lucas_primality 30612443 (2 : ZMod 30612443)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (2186603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (2186603, 1)] : List FactorBlock).map factorBlockValue).prod) = 30612443 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_7
      · exact prime_oneHundredFiftyFourEV_2186603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 30612443) ^ 15306221 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 30612443) ^ 4373206 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 30612443) ^ 14 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_32701811 : Nat.Prime 32701811 := by
  apply lucas_primality 32701811 (2 : ZMod 32701811)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (73, 1), (44797, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (73, 1), (44797, 1)] : List FactorBlock).map factorBlockValue).prod) = 32701811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_5
      · exact prime_oneHundredFiftyFourEV_73
      · exact prime_oneHundredFiftyFourEV_44797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 32701811) ^ 16350905 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 32701811) ^ 6540362 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 32701811) ^ 447970 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 32701811) ^ 730 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_33050341 : Nat.Prime 33050341 := by
  apply lucas_primality 33050341 (2 : ZMod 33050341)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (31, 1), (5923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (31, 1), (5923, 1)] : List FactorBlock).map factorBlockValue).prod) = 33050341 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_5
      · exact prime_oneHundredFiftyFourEV_31
      · exact prime_oneHundredFiftyFourEV_5923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 33050341) ^ 16525170 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 33050341) ^ 11016780 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 33050341) ^ 6610068 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 33050341) ^ 1066140 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 33050341) ^ 5580 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_33452129 : Nat.Prime 33452129 := by
  apply lucas_primality 33452129 (3 : ZMod 33452129)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (811, 1), (1289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (811, 1), (1289, 1)] : List FactorBlock).map factorBlockValue).prod) = 33452129 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_811
      · exact prime_oneHundredFiftyFourEV_1289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 33452129) ^ 16726064 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 33452129) ^ 41248 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 33452129) ^ 25952 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_34858727 : Nat.Prime 34858727 := by
  apply lucas_primality 34858727 (7 : ZMod 34858727)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (2489909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (2489909, 1)] : List FactorBlock).map factorBlockValue).prod) = 34858727 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_7
      · exact prime_oneHundredFiftyFourEV_2489909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 34858727) ^ 17429363 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (7 : ZMod 34858727) ^ 4979818 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (7 : ZMod 34858727) ^ 14 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_35360023 : Nat.Prime 35360023 := by
  apply lucas_primality 35360023 (3 : ZMod 35360023)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5893337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5893337, 1)] : List FactorBlock).map factorBlockValue).prod) = 35360023 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_5893337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 35360023) ^ 17680011 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 35360023) ^ 11786674 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 35360023) ^ 6 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_40674451 : Nat.Prime 40674451 := by
  apply lucas_primality 40674451 (2 : ZMod 40674451)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (271163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (271163, 1)] : List FactorBlock).map factorBlockValue).prod) = 40674451 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_5
      · exact prime_oneHundredFiftyFourEV_271163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 40674451) ^ 20337225 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 40674451) ^ 13558150 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 40674451) ^ 8134890 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 40674451) ^ 150 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_43001837 : Nat.Prime 43001837 := by
  apply lucas_primality 43001837 (2 : ZMod 43001837)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (31, 1), (239, 1), (1451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (31, 1), (239, 1), (1451, 1)] : List FactorBlock).map factorBlockValue).prod) = 43001837 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_31
      · exact prime_oneHundredFiftyFourEV_239
      · exact prime_oneHundredFiftyFourEV_1451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 43001837) ^ 21500918 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 43001837) ^ 1387156 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 43001837) ^ 179924 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 43001837) ^ 29636 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_44693083 : Nat.Prime 44693083 := by
  apply lucas_primality 44693083 (2 : ZMod 44693083)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (43, 1), (73, 1), (113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (43, 1), (73, 1), (113, 1)] : List FactorBlock).map factorBlockValue).prod) = 44693083 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_7
      · exact prime_oneHundredFiftyFourEV_43
      · exact prime_oneHundredFiftyFourEV_73
      · exact prime_oneHundredFiftyFourEV_113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 44693083) ^ 22346541 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 44693083) ^ 14897694 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 44693083) ^ 6384726 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 44693083) ^ 1039374 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 44693083) ^ 612234 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 44693083) ^ 395514 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_45764899 : Nat.Prime 45764899 := by
  apply lucas_primality 45764899 (2 : ZMod 45764899)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (647, 1), (11789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (647, 1), (11789, 1)] : List FactorBlock).map factorBlockValue).prod) = 45764899 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_647
      · exact prime_oneHundredFiftyFourEV_11789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 45764899) ^ 22882449 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 45764899) ^ 15254966 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 45764899) ^ 70734 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 45764899) ^ 3882 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_47024249 : Nat.Prime 47024249 := by
  apply lucas_primality 47024249 (3 : ZMod 47024249)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (1277, 1), (4603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (1277, 1), (4603, 1)] : List FactorBlock).map factorBlockValue).prod) = 47024249 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_1277
      · exact prime_oneHundredFiftyFourEV_4603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 47024249) ^ 23512124 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 47024249) ^ 36824 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 47024249) ^ 10216 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_49471423 : Nat.Prime 49471423 := by
  apply lucas_primality 49471423 (3 : ZMod 49471423)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (11, 1), (13, 1), (8237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (11, 1), (13, 1), (8237, 1)] : List FactorBlock).map factorBlockValue).prod) = 49471423 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_7
      · exact prime_oneHundredFiftyFourEV_11
      · exact prime_oneHundredFiftyFourEV_13
      · exact prime_oneHundredFiftyFourEV_8237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 49471423) ^ 24735711 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 49471423) ^ 16490474 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 49471423) ^ 7067346 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 49471423) ^ 4497402 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 49471423) ^ 3805494 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 49471423) ^ 6006 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_54520607 : Nat.Prime 54520607 := by
  apply lucas_primality 54520607 (7 : ZMod 54520607)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (3894329, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (3894329, 1)] : List FactorBlock).map factorBlockValue).prod) = 54520607 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_7
      · exact prime_oneHundredFiftyFourEV_3894329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 54520607) ^ 27260303 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (7 : ZMod 54520607) ^ 7788658 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (7 : ZMod 54520607) ^ 14 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_54661237 : Nat.Prime 54661237 := by
  apply lucas_primality 54661237 (2 : ZMod 54661237)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (521, 1), (1249, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (521, 1), (1249, 1)] : List FactorBlock).map factorBlockValue).prod) = 54661237 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_7
      · exact prime_oneHundredFiftyFourEV_521
      · exact prime_oneHundredFiftyFourEV_1249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 54661237) ^ 27330618 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 54661237) ^ 18220412 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 54661237) ^ 7808748 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 54661237) ^ 104916 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 54661237) ^ 43764 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_54902009 : Nat.Prime 54902009 := by
  apply lucas_primality 54902009 (6 : ZMod 54902009)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (980393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (980393, 1)] : List FactorBlock).map factorBlockValue).prod) = 54902009 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_7
      · exact prime_oneHundredFiftyFourEV_980393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 54902009) ^ 27451004 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (6 : ZMod 54902009) ^ 7843144 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (6 : ZMod 54902009) ^ 56 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_59929613 : Nat.Prime 59929613 := by
  apply lucas_primality 59929613 (2 : ZMod 59929613)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1811, 1), (8273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1811, 1), (8273, 1)] : List FactorBlock).map factorBlockValue).prod) = 59929613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_1811
      · exact prime_oneHundredFiftyFourEV_8273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 59929613) ^ 29964806 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 59929613) ^ 33092 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 59929613) ^ 7244 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_68513737 : Nat.Prime 68513737 := by
  apply lucas_primality 68513737 (7 : ZMod 68513737)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (53, 1), (61, 1), (883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (53, 1), (61, 1), (883, 1)] : List FactorBlock).map factorBlockValue).prod) = 68513737 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_53
      · exact prime_oneHundredFiftyFourEV_61
      · exact prime_oneHundredFiftyFourEV_883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 68513737) ^ 34256868 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (7 : ZMod 68513737) ^ 22837912 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (7 : ZMod 68513737) ^ 1292712 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (7 : ZMod 68513737) ^ 1123176 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (7 : ZMod 68513737) ^ 77592 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_69758081 : Nat.Prime 69758081 := by
  apply lucas_primality 69758081 (3 : ZMod 69758081)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (5, 1), (7, 1), (23, 1), (677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (5, 1), (7, 1), (23, 1), (677, 1)] : List FactorBlock).map factorBlockValue).prod) = 69758081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_5
      · exact prime_oneHundredFiftyFourEV_7
      · exact prime_oneHundredFiftyFourEV_23
      · exact prime_oneHundredFiftyFourEV_677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 69758081) ^ 34879040 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 69758081) ^ 13951616 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 69758081) ^ 9965440 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 69758081) ^ 3032960 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 69758081) ^ 103040 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_70810063 : Nat.Prime 70810063 := by
  apply lucas_primality 70810063 (6 : ZMod 70810063)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1783, 1), (6619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1783, 1), (6619, 1)] : List FactorBlock).map factorBlockValue).prod) = 70810063 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_1783
      · exact prime_oneHundredFiftyFourEV_6619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 70810063) ^ 35405031 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (6 : ZMod 70810063) ^ 23603354 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (6 : ZMod 70810063) ^ 39714 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (6 : ZMod 70810063) ^ 10698 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_81610219 : Nat.Prime 81610219 := by
  apply lucas_primality 81610219 (2 : ZMod 81610219)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (1097, 1), (4133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (1097, 1), (4133, 1)] : List FactorBlock).map factorBlockValue).prod) = 81610219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_1097
      · exact prime_oneHundredFiftyFourEV_4133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 81610219) ^ 40805109 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 81610219) ^ 27203406 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 81610219) ^ 74394 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 81610219) ^ 19746 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_82790789 : Nat.Prime 82790789 := by
  apply lucas_primality 82790789 (2 : ZMod 82790789)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (2027, 1), (10211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (2027, 1), (10211, 1)] : List FactorBlock).map factorBlockValue).prod) = 82790789 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_2027
      · exact prime_oneHundredFiftyFourEV_10211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 82790789) ^ 41395394 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 82790789) ^ 40844 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 82790789) ^ 8108 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_87016001 : Nat.Prime 87016001 := by
  apply lucas_primality 87016001 (3 : ZMod 87016001)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (5, 3), (73, 1), (149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (5, 3), (73, 1), (149, 1)] : List FactorBlock).map factorBlockValue).prod) = 87016001 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_5
      · exact prime_oneHundredFiftyFourEV_73
      · exact prime_oneHundredFiftyFourEV_149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 87016001) ^ 43508000 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 87016001) ^ 17403200 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 87016001) ^ 1192000 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 87016001) ^ 584000 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_87094849 : Nat.Prime 87094849 := by
  apply lucas_primality 87094849 (19 : ZMod 87094849)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (71, 1), (6389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (71, 1), (6389, 1)] : List FactorBlock).map factorBlockValue).prod) = 87094849 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_71
      · exact prime_oneHundredFiftyFourEV_6389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 87094849) ^ 43547424 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (19 : ZMod 87094849) ^ 29031616 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (19 : ZMod 87094849) ^ 1226688 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (19 : ZMod 87094849) ^ 13632 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_90391069 : Nat.Prime 90391069 := by
  apply lucas_primality 90391069 (2 : ZMod 90391069)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (59, 1), (42557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (59, 1), (42557, 1)] : List FactorBlock).map factorBlockValue).prod) = 90391069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_59
      · exact prime_oneHundredFiftyFourEV_42557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 90391069) ^ 45195534 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 90391069) ^ 30130356 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 90391069) ^ 1532052 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 90391069) ^ 2124 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_94480049 : Nat.Prime 94480049 := by
  apply lucas_primality 94480049 (3 : ZMod 94480049)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (13, 1), (454231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (13, 1), (454231, 1)] : List FactorBlock).map factorBlockValue).prod) = 94480049 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_13
      · exact prime_oneHundredFiftyFourEV_454231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 94480049) ^ 47240024 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 94480049) ^ 7267696 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 94480049) ^ 208 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_107804831 : Nat.Prime 107804831 := by
  apply lucas_primality 107804831 (14 : ZMod 107804831)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (97, 1), (15877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (97, 1), (15877, 1)] : List FactorBlock).map factorBlockValue).prod) = 107804831 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_5
      · exact prime_oneHundredFiftyFourEV_7
      · exact prime_oneHundredFiftyFourEV_97
      · exact prime_oneHundredFiftyFourEV_15877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 107804831) ^ 53902415 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (14 : ZMod 107804831) ^ 21560966 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (14 : ZMod 107804831) ^ 15400690 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (14 : ZMod 107804831) ^ 1111390 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (14 : ZMod 107804831) ^ 6790 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_117238469 : Nat.Prime 117238469 := by
  apply lucas_primality 117238469 (2 : ZMod 117238469)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (43, 1), (97, 1), (7027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (43, 1), (97, 1), (7027, 1)] : List FactorBlock).map factorBlockValue).prod) = 117238469 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_43
      · exact prime_oneHundredFiftyFourEV_97
      · exact prime_oneHundredFiftyFourEV_7027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 117238469) ^ 58619234 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 117238469) ^ 2726476 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 117238469) ^ 1208644 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 117238469) ^ 16684 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_119285167 : Nat.Prime 119285167 := by
  apply lucas_primality 119285167 (5 : ZMod 119285167)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (11, 1), (13, 1), (19861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (11, 1), (13, 1), (19861, 1)] : List FactorBlock).map factorBlockValue).prod) = 119285167 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_7
      · exact prime_oneHundredFiftyFourEV_11
      · exact prime_oneHundredFiftyFourEV_13
      · exact prime_oneHundredFiftyFourEV_19861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 119285167) ^ 59642583 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 119285167) ^ 39761722 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 119285167) ^ 17040738 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 119285167) ^ 10844106 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 119285167) ^ 9175782 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 119285167) ^ 6006 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_130311089 : Nat.Prime 130311089 := by
  apply lucas_primality 130311089 (3 : ZMod 130311089)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (8144443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (8144443, 1)] : List FactorBlock).map factorBlockValue).prod) = 130311089 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_8144443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 130311089) ^ 65155544 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 130311089) ^ 16 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_158265131 : Nat.Prime 158265131 := by
  apply lucas_primality 158265131 (2 : ZMod 158265131)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (15826513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (15826513, 1)] : List FactorBlock).map factorBlockValue).prod) = 158265131 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_5
      · exact prime_oneHundredFiftyFourEV_15826513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 158265131) ^ 79132565 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 158265131) ^ 31653026 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 158265131) ^ 10 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_165581579 : Nat.Prime 165581579 := by
  apply lucas_primality 165581579 (2 : ZMod 165581579)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (82790789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (82790789, 1)] : List FactorBlock).map factorBlockValue).prod) = 165581579 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_82790789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 165581579) ^ 82790789 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 165581579) ^ 2 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_188960099 : Nat.Prime 188960099 := by
  apply lucas_primality 188960099 (2 : ZMod 188960099)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (94480049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (94480049, 1)] : List FactorBlock).map factorBlockValue).prod) = 188960099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_94480049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 188960099) ^ 94480049 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 188960099) ^ 2 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_190746943 : Nat.Prime 190746943 := by
  apply lucas_primality 190746943 (3 : ZMod 190746943)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (257, 1), (123701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (257, 1), (123701, 1)] : List FactorBlock).map factorBlockValue).prod) = 190746943 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_257
      · exact prime_oneHundredFiftyFourEV_123701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 190746943) ^ 95373471 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 190746943) ^ 63582314 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 190746943) ^ 742206 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 190746943) ^ 1542 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_200272519 : Nat.Prime 200272519 := by
  apply lucas_primality 200272519 (15 : ZMod 200272519)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (181, 1), (61471, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (181, 1), (61471, 1)] : List FactorBlock).map factorBlockValue).prod) = 200272519 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_181
      · exact prime_oneHundredFiftyFourEV_61471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (15 : ZMod 200272519) ^ 100136259 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (15 : ZMod 200272519) ^ 66757506 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (15 : ZMod 200272519) ^ 1106478 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (15 : ZMod 200272519) ^ 3258 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_211505011 : Nat.Prime 211505011 := by
  apply lucas_primality 211505011 (3 : ZMod 211505011)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (23, 1), (306529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (23, 1), (306529, 1)] : List FactorBlock).map factorBlockValue).prod) = 211505011 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_5
      · exact prime_oneHundredFiftyFourEV_23
      · exact prime_oneHundredFiftyFourEV_306529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 211505011) ^ 105752505 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 211505011) ^ 70501670 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 211505011) ^ 42301002 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 211505011) ^ 9195870 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 211505011) ^ 690 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_215449931 : Nat.Prime 215449931 := by
  apply lucas_primality 215449931 (2 : ZMod 215449931)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (19, 1), (1133947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (19, 1), (1133947, 1)] : List FactorBlock).map factorBlockValue).prod) = 215449931 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_5
      · exact prime_oneHundredFiftyFourEV_19
      · exact prime_oneHundredFiftyFourEV_1133947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 215449931) ^ 107724965 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 215449931) ^ 43089986 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 215449931) ^ 11339470 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 215449931) ^ 190 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_260622179 : Nat.Prime 260622179 := by
  apply lucas_primality 260622179 (2 : ZMod 260622179)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (130311089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (130311089, 1)] : List FactorBlock).map factorBlockValue).prod) = 260622179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_130311089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 260622179) ^ 130311089 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 260622179) ^ 2 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_283812547 : Nat.Prime 283812547 := by
  apply lucas_primality 283812547 (7 : ZMod 283812547)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (223, 1), (212117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (223, 1), (212117, 1)] : List FactorBlock).map factorBlockValue).prod) = 283812547 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_223
      · exact prime_oneHundredFiftyFourEV_212117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 283812547) ^ 141906273 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (7 : ZMod 283812547) ^ 94604182 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (7 : ZMod 283812547) ^ 1272702 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (7 : ZMod 283812547) ^ 1338 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_307799861 : Nat.Prime 307799861 := by
  apply lucas_primality 307799861 (3 : ZMod 307799861)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (15389993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (15389993, 1)] : List FactorBlock).map factorBlockValue).prod) = 307799861 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_5
      · exact prime_oneHundredFiftyFourEV_15389993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 307799861) ^ 153899930 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 307799861) ^ 61559972 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 307799861) ^ 20 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_307863041 : Nat.Prime 307863041 := by
  apply lucas_primality 307863041 (3 : ZMod 307863041)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 9), (5, 1), (241, 1), (499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 9), (5, 1), (241, 1), (499, 1)] : List FactorBlock).map factorBlockValue).prod) = 307863041 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_5
      · exact prime_oneHundredFiftyFourEV_241
      · exact prime_oneHundredFiftyFourEV_499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 307863041) ^ 153931520 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 307863041) ^ 61572608 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 307863041) ^ 1277440 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 307863041) ^ 616960 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_320491439 : Nat.Prime 320491439 := by
  apply lucas_primality 320491439 (7 : ZMod 320491439)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (61, 1), (317, 1), (8287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (61, 1), (317, 1), (8287, 1)] : List FactorBlock).map factorBlockValue).prod) = 320491439 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_61
      · exact prime_oneHundredFiftyFourEV_317
      · exact prime_oneHundredFiftyFourEV_8287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 320491439) ^ 160245719 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (7 : ZMod 320491439) ^ 5253958 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (7 : ZMod 320491439) ^ 1011014 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (7 : ZMod 320491439) ^ 38674 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_340058183 : Nat.Prime 340058183 := by
  apply lucas_primality 340058183 (5 : ZMod 340058183)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (59, 1), (70289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (59, 1), (70289, 1)] : List FactorBlock).map factorBlockValue).prod) = 340058183 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_41
      · exact prime_oneHundredFiftyFourEV_59
      · exact prime_oneHundredFiftyFourEV_70289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 340058183) ^ 170029091 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 340058183) ^ 8294102 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 340058183) ^ 5763698 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 340058183) ^ 4838 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_400915547 : Nat.Prime 400915547 := by
  apply lucas_primality 400915547 (2 : ZMod 400915547)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (47, 1), (61, 1), (2411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (47, 1), (61, 1), (2411, 1)] : List FactorBlock).map factorBlockValue).prod) = 400915547 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_29
      · exact prime_oneHundredFiftyFourEV_47
      · exact prime_oneHundredFiftyFourEV_61
      · exact prime_oneHundredFiftyFourEV_2411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 400915547) ^ 200457773 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 400915547) ^ 13824674 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 400915547) ^ 8530118 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 400915547) ^ 6572386 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 400915547) ^ 166286 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_409849511 : Nat.Prime 409849511 := by
  apply lucas_primality 409849511 (7 : ZMod 409849511)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (5854993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (5854993, 1)] : List FactorBlock).map factorBlockValue).prod) = 409849511 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_5
      · exact prime_oneHundredFiftyFourEV_7
      · exact prime_oneHundredFiftyFourEV_5854993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 409849511) ^ 204924755 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (7 : ZMod 409849511) ^ 81969902 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (7 : ZMod 409849511) ^ 58549930 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (7 : ZMod 409849511) ^ 70 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_415934677 : Nat.Prime 415934677 := by
  apply lucas_primality 415934677 (2 : ZMod 415934677)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (199, 1), (6451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (199, 1), (6451, 1)] : List FactorBlock).map factorBlockValue).prod) = 415934677 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_199
      · exact prime_oneHundredFiftyFourEV_6451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 415934677) ^ 207967338 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 415934677) ^ 138644892 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 415934677) ^ 2090124 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 415934677) ^ 64476 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_429295049 : Nat.Prime 429295049 := by
  apply lucas_primality 429295049 (3 : ZMod 429295049)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (13, 1), (491, 1), (1201, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (13, 1), (491, 1), (1201, 1)] : List FactorBlock).map factorBlockValue).prod) = 429295049 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_7
      · exact prime_oneHundredFiftyFourEV_13
      · exact prime_oneHundredFiftyFourEV_491
      · exact prime_oneHundredFiftyFourEV_1201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 429295049) ^ 214647524 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 429295049) ^ 61327864 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 429295049) ^ 33022696 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 429295049) ^ 874328 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 429295049) ^ 357448 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_430899863 : Nat.Prime 430899863 := by
  apply lucas_primality 430899863 (5 : ZMod 430899863)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (215449931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (215449931, 1)] : List FactorBlock).map factorBlockValue).prod) = 430899863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_215449931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 430899863) ^ 215449931 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 430899863) ^ 2 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_478020317 : Nat.Prime 478020317 := by
  apply lucas_primality 478020317 (2 : ZMod 478020317)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 2), (23, 1), (37, 1), (389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 2), (23, 1), (37, 1), (389, 1)] : List FactorBlock).map factorBlockValue).prod) = 478020317 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_19
      · exact prime_oneHundredFiftyFourEV_23
      · exact prime_oneHundredFiftyFourEV_37
      · exact prime_oneHundredFiftyFourEV_389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 478020317) ^ 239010158 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 478020317) ^ 25158964 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 478020317) ^ 20783492 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 478020317) ^ 12919468 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 478020317) ^ 1228844 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_486388121 : Nat.Prime 486388121 := by
  apply lucas_primality 486388121 (3 : ZMod 486388121)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (12159703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (12159703, 1)] : List FactorBlock).map factorBlockValue).prod) = 486388121 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_5
      · exact prime_oneHundredFiftyFourEV_12159703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 486388121) ^ 243194060 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 486388121) ^ 97277624 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 486388121) ^ 40 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_544380313 : Nat.Prime 544380313 := by
  apply lucas_primality 544380313 (10 : ZMod 544380313)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (3240359, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (3240359, 1)] : List FactorBlock).map factorBlockValue).prod) = 544380313 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_7
      · exact prime_oneHundredFiftyFourEV_3240359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 544380313) ^ 272190156 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (10 : ZMod 544380313) ^ 181460104 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (10 : ZMod 544380313) ^ 77768616 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (10 : ZMod 544380313) ^ 168 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_545326447 : Nat.Prime 545326447 := by
  apply lucas_primality 545326447 (6 : ZMod 545326447)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (12983963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (12983963, 1)] : List FactorBlock).map factorBlockValue).prod) = 545326447 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_7
      · exact prime_oneHundredFiftyFourEV_12983963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 545326447) ^ 272663223 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (6 : ZMod 545326447) ^ 181775482 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (6 : ZMod 545326447) ^ 77903778 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (6 : ZMod 545326447) ^ 42 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_567187783 : Nat.Prime 567187783 := by
  apply lucas_primality 567187783 (3 : ZMod 567187783)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (13504471, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (13504471, 1)] : List FactorBlock).map factorBlockValue).prod) = 567187783 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_7
      · exact prime_oneHundredFiftyFourEV_13504471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 567187783) ^ 283593891 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 567187783) ^ 189062594 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 567187783) ^ 81026826 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 567187783) ^ 42 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_573304639 : Nat.Prime 573304639 := by
  apply lucas_primality 573304639 (3 : ZMod 573304639)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (43, 2), (1667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (43, 2), (1667, 1)] : List FactorBlock).map factorBlockValue).prod) = 573304639 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_31
      · exact prime_oneHundredFiftyFourEV_43
      · exact prime_oneHundredFiftyFourEV_1667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 573304639) ^ 286652319 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 573304639) ^ 191101546 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 573304639) ^ 18493698 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 573304639) ^ 13332666 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 573304639) ^ 343914 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_666730033 : Nat.Prime 666730033 := by
  apply lucas_primality 666730033 (10 : ZMod 666730033)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (13890209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (13890209, 1)] : List FactorBlock).map factorBlockValue).prod) = 666730033 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_13890209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 666730033) ^ 333365016 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (10 : ZMod 666730033) ^ 222243344 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (10 : ZMod 666730033) ^ 48 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_696128009 : Nat.Prime 696128009 := by
  apply lucas_primality 696128009 (3 : ZMod 696128009)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (87016001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (87016001, 1)] : List FactorBlock).map factorBlockValue).prod) = 696128009 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_87016001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 696128009) ^ 348064004 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 696128009) ^ 8 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_714027719 : Nat.Prime 714027719 := by
  apply lucas_primality 714027719 (11 : ZMod 714027719)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) = 714027719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_17203
      · exact prime_oneHundredFiftyFourEV_20753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 714027719) ^ 357013859 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 41506 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 34406 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_729919451 : Nat.Prime 729919451 := by
  apply lucas_primality 729919451 (2 : ZMod 729919451)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (13, 2), (86381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (13, 2), (86381, 1)] : List FactorBlock).map factorBlockValue).prod) = 729919451 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_5
      · exact prime_oneHundredFiftyFourEV_13
      · exact prime_oneHundredFiftyFourEV_86381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 729919451) ^ 364959725 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 729919451) ^ 145983890 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 729919451) ^ 56147650 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 729919451) ^ 8450 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_858077879 : Nat.Prime 858077879 := by
  apply lucas_primality 858077879 (7 : ZMod 858077879)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (37, 1), (1656521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (37, 1), (1656521, 1)] : List FactorBlock).map factorBlockValue).prod) = 858077879 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_7
      · exact prime_oneHundredFiftyFourEV_37
      · exact prime_oneHundredFiftyFourEV_1656521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 858077879) ^ 429038939 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (7 : ZMod 858077879) ^ 122582554 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (7 : ZMod 858077879) ^ 23191294 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (7 : ZMod 858077879) ^ 518 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_965163109 : Nat.Prime 965163109 := by
  apply lucas_primality 965163109 (2 : ZMod 965163109)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (13, 1), (409, 1), (2161, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (13, 1), (409, 1), (2161, 1)] : List FactorBlock).map factorBlockValue).prod) = 965163109 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_7
      · exact prime_oneHundredFiftyFourEV_13
      · exact prime_oneHundredFiftyFourEV_409
      · exact prime_oneHundredFiftyFourEV_2161
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 965163109) ^ 482581554 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 965163109) ^ 321721036 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 965163109) ^ 137880444 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 965163109) ^ 74243316 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 965163109) ^ 2359812 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 965163109) ^ 446628 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_977085101 : Nat.Prime 977085101 := by
  apply lucas_primality 977085101 (2 : ZMod 977085101)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (9770851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (9770851, 1)] : List FactorBlock).map factorBlockValue).prod) = 977085101 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_5
      · exact prime_oneHundredFiftyFourEV_9770851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 977085101) ^ 488542550 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 977085101) ^ 195417020 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 977085101) ^ 100 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_1012197971 : Nat.Prime 1012197971 := by
  apply lucas_primality 1012197971 (7 : ZMod 1012197971)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (797, 1), (18143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (797, 1), (18143, 1)] : List FactorBlock).map factorBlockValue).prod) = 1012197971 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_5
      · exact prime_oneHundredFiftyFourEV_7
      · exact prime_oneHundredFiftyFourEV_797
      · exact prime_oneHundredFiftyFourEV_18143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1012197971) ^ 506098985 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (7 : ZMod 1012197971) ^ 202439594 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (7 : ZMod 1012197971) ^ 144599710 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (7 : ZMod 1012197971) ^ 1270010 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (7 : ZMod 1012197971) ^ 55790 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_1188628943 : Nat.Prime 1188628943 := by
  apply lucas_primality 1188628943 (5 : ZMod 1188628943)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (907, 1), (34487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (907, 1), (34487, 1)] : List FactorBlock).map factorBlockValue).prod) = 1188628943 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_19
      · exact prime_oneHundredFiftyFourEV_907
      · exact prime_oneHundredFiftyFourEV_34487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1188628943) ^ 594314471 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 1188628943) ^ 62559418 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 1188628943) ^ 1310506 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 1188628943) ^ 34466 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_1400369249 : Nat.Prime 1400369249 := by
  apply lucas_primality 1400369249 (3 : ZMod 1400369249)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (59, 1), (741721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (59, 1), (741721, 1)] : List FactorBlock).map factorBlockValue).prod) = 1400369249 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_59
      · exact prime_oneHundredFiftyFourEV_741721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1400369249) ^ 700184624 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1400369249) ^ 23735072 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1400369249) ^ 1888 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_1563186511 : Nat.Prime 1563186511 := by
  apply lucas_primality 1563186511 (12 : ZMod 1563186511)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (2377, 1), (7307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (2377, 1), (7307, 1)] : List FactorBlock).map factorBlockValue).prod) = 1563186511 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_5
      · exact prime_oneHundredFiftyFourEV_2377
      · exact prime_oneHundredFiftyFourEV_7307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (12 : ZMod 1563186511) ^ 781593255 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (12 : ZMod 1563186511) ^ 521062170 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (12 : ZMod 1563186511) ^ 312637302 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (12 : ZMod 1563186511) ^ 657630 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (12 : ZMod 1563186511) ^ 213930 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_1631470259 : Nat.Prime 1631470259 := by
  apply lucas_primality 1631470259 (2 : ZMod 1631470259)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (523, 1), (141793, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (523, 1), (141793, 1)] : List FactorBlock).map factorBlockValue).prod) = 1631470259 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_11
      · exact prime_oneHundredFiftyFourEV_523
      · exact prime_oneHundredFiftyFourEV_141793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1631470259) ^ 815735129 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1631470259) ^ 148315478 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1631470259) ^ 3119446 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1631470259) ^ 11506 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_1758386051 : Nat.Prime 1758386051 := by
  apply lucas_primality 1758386051 (2 : ZMod 1758386051)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (1439, 1), (24439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (1439, 1), (24439, 1)] : List FactorBlock).map factorBlockValue).prod) = 1758386051 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_5
      · exact prime_oneHundredFiftyFourEV_1439
      · exact prime_oneHundredFiftyFourEV_24439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1758386051) ^ 879193025 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1758386051) ^ 351677210 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1758386051) ^ 1221950 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1758386051) ^ 71950 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_1922881481 : Nat.Prime 1922881481 := by
  apply lucas_primality 1922881481 (3 : ZMod 1922881481)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (13, 1), (3697849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (13, 1), (3697849, 1)] : List FactorBlock).map factorBlockValue).prod) = 1922881481 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_5
      · exact prime_oneHundredFiftyFourEV_13
      · exact prime_oneHundredFiftyFourEV_3697849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1922881481) ^ 961440740 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1922881481) ^ 384576296 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1922881481) ^ 147913960 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1922881481) ^ 520 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_2202221347 : Nat.Prime 2202221347 := by
  apply lucas_primality 2202221347 (2 : ZMod 2202221347)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (28233607, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (28233607, 1)] : List FactorBlock).map factorBlockValue).prod) = 2202221347 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_13
      · exact prime_oneHundredFiftyFourEV_28233607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2202221347) ^ 1101110673 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2202221347) ^ 734073782 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2202221347) ^ 169401642 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2202221347) ^ 78 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_2267521189 : Nat.Prime 2267521189 := by
  apply lucas_primality 2267521189 (2 : ZMod 2267521189)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (188960099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (188960099, 1)] : List FactorBlock).map factorBlockValue).prod) = 2267521189 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_188960099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2267521189) ^ 1133760594 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2267521189) ^ 755840396 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2267521189) ^ 12 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_2502790933 : Nat.Prime 2502790933 := by
  apply lucas_primality 2502790933 (2 : ZMod 2502790933)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (12268583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (12268583, 1)] : List FactorBlock).map factorBlockValue).prod) = 2502790933 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_17
      · exact prime_oneHundredFiftyFourEV_12268583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2502790933) ^ 1251395466 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2502790933) ^ 834263644 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2502790933) ^ 147222996 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2502790933) ^ 204 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_2545939001 : Nat.Prime 2545939001 := by
  apply lucas_primality 2545939001 (3 : ZMod 2545939001)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 3), (11, 1), (23, 1), (29, 1), (347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 3), (11, 1), (23, 1), (29, 1), (347, 1)] : List FactorBlock).map factorBlockValue).prod) = 2545939001 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_5
      · exact prime_oneHundredFiftyFourEV_11
      · exact prime_oneHundredFiftyFourEV_23
      · exact prime_oneHundredFiftyFourEV_29
      · exact prime_oneHundredFiftyFourEV_347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2545939001) ^ 1272969500 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 2545939001) ^ 509187800 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 2545939001) ^ 231449000 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 2545939001) ^ 110693000 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 2545939001) ^ 87791000 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 2545939001) ^ 7337000 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_2640219503 : Nat.Prime 2640219503 := by
  apply lucas_primality 2640219503 (5 : ZMod 2640219503)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13751, 1), (96001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13751, 1), (96001, 1)] : List FactorBlock).map factorBlockValue).prod) = 2640219503 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_13751
      · exact prime_oneHundredFiftyFourEV_96001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 2640219503) ^ 1320109751 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 2640219503) ^ 192002 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 2640219503) ^ 27502 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_2786860621 : Nat.Prime 2786860621 := by
  apply lucas_primality 2786860621 (7 : ZMod 2786860621)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 1), (181, 1), (28513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 1), (181, 1), (28513, 1)] : List FactorBlock).map factorBlockValue).prod) = 2786860621 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_5
      · exact prime_oneHundredFiftyFourEV_181
      · exact prime_oneHundredFiftyFourEV_28513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 2786860621) ^ 1393430310 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (7 : ZMod 2786860621) ^ 928953540 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (7 : ZMod 2786860621) ^ 557372124 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (7 : ZMod 2786860621) ^ 15397020 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (7 : ZMod 2786860621) ^ 97740 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_2868121903 : Nat.Prime 2868121903 := by
  apply lucas_primality 2868121903 (5 : ZMod 2868121903)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (478020317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (478020317, 1)] : List FactorBlock).map factorBlockValue).prod) = 2868121903 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_478020317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 2868121903) ^ 1434060951 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 2868121903) ^ 956040634 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 2868121903) ^ 6 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_3262940519 : Nat.Prime 3262940519 := by
  apply lucas_primality 3262940519 (11 : ZMod 3262940519)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1631470259, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1631470259, 1)] : List FactorBlock).map factorBlockValue).prod) = 3262940519 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_1631470259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (11 : ZMod 3262940519) ^ 1631470259 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (11 : ZMod 3262940519) ^ 2 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_3278796089 : Nat.Prime 3278796089 := by
  apply lucas_primality 3278796089 (3 : ZMod 3278796089)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (409849511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (409849511, 1)] : List FactorBlock).map factorBlockValue).prod) = 3278796089 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_409849511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 3278796089) ^ 1639398044 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 3278796089) ^ 8 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_3526355297 : Nat.Prime 3526355297 := by
  apply lucas_primality 3526355297 (3 : ZMod 3526355297)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (71, 1), (1193, 1), (1301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (71, 1), (1193, 1), (1301, 1)] : List FactorBlock).map factorBlockValue).prod) = 3526355297 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_71
      · exact prime_oneHundredFiftyFourEV_1193
      · exact prime_oneHundredFiftyFourEV_1301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3526355297) ^ 1763177648 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 3526355297) ^ 49666976 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 3526355297) ^ 2955872 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 3526355297) ^ 2710496 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_3766347163 : Nat.Prime 3766347163 := by
  apply lucas_primality 3766347163 (2 : ZMod 3766347163)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (19, 1), (47, 1), (53, 1), (4421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (19, 1), (47, 1), (53, 1), (4421, 1)] : List FactorBlock).map factorBlockValue).prod) = 3766347163 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_19
      · exact prime_oneHundredFiftyFourEV_47
      · exact prime_oneHundredFiftyFourEV_53
      · exact prime_oneHundredFiftyFourEV_4421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3766347163) ^ 1883173581 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 3766347163) ^ 1255449054 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 3766347163) ^ 198228798 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 3766347163) ^ 80135046 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 3766347163) ^ 71063154 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 3766347163) ^ 851922 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_4505031589 : Nat.Prime 4505031589 := by
  apply lucas_primality 4505031589 (6 : ZMod 4505031589)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (53, 1), (7083383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (53, 1), (7083383, 1)] : List FactorBlock).map factorBlockValue).prod) = 4505031589 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_53
      · exact prime_oneHundredFiftyFourEV_7083383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 4505031589) ^ 2252515794 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (6 : ZMod 4505031589) ^ 1501677196 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (6 : ZMod 4505031589) ^ 85000596 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (6 : ZMod 4505031589) ^ 636 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_4608282073 : Nat.Prime 4608282073 := by
  apply lucas_primality 4608282073 (11 : ZMod 4608282073)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (17, 1), (11294809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (17, 1), (11294809, 1)] : List FactorBlock).map factorBlockValue).prod) = 4608282073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_17
      · exact prime_oneHundredFiftyFourEV_11294809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 4608282073) ^ 2304141036 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (11 : ZMod 4608282073) ^ 1536094024 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (11 : ZMod 4608282073) ^ 271075416 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (11 : ZMod 4608282073) ^ 408 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_4914242863 : Nat.Prime 4914242863 := by
  apply lucas_primality 4914242863 (3 : ZMod 4914242863)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (41, 1), (19976597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (41, 1), (19976597, 1)] : List FactorBlock).map factorBlockValue).prod) = 4914242863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_41
      · exact prime_oneHundredFiftyFourEV_19976597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4914242863) ^ 2457121431 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 4914242863) ^ 1638080954 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 4914242863) ^ 119859582 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 4914242863) ^ 246 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_5276183617 : Nat.Prime 5276183617 := by
  apply lucas_primality 5276183617 (7 : ZMod 5276183617)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (11, 1), (277577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (11, 1), (277577, 1)] : List FactorBlock).map factorBlockValue).prod) = 5276183617 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_11
      · exact prime_oneHundredFiftyFourEV_277577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 5276183617) ^ 2638091808 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (7 : ZMod 5276183617) ^ 1758727872 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (7 : ZMod 5276183617) ^ 479653056 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (7 : ZMod 5276183617) ^ 19008 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_5298610529 : Nat.Prime 5298610529 := by
  apply lucas_primality 5298610529 (3 : ZMod 5298610529)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (165581579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (165581579, 1)] : List FactorBlock).map factorBlockValue).prod) = 5298610529 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_165581579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 5298610529) ^ 2649305264 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 5298610529) ^ 32 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_5429792839 : Nat.Prime 5429792839 := by
  apply lucas_primality 5429792839 (6 : ZMod 5429792839)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (709, 1), (1276397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (709, 1), (1276397, 1)] : List FactorBlock).map factorBlockValue).prod) = 5429792839 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_709
      · exact prime_oneHundredFiftyFourEV_1276397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 5429792839) ^ 2714896419 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (6 : ZMod 5429792839) ^ 1809930946 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (6 : ZMod 5429792839) ^ 7658382 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (6 : ZMod 5429792839) ^ 4254 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_5839355609 : Nat.Prime 5839355609 := by
  apply lucas_primality 5839355609 (3 : ZMod 5839355609)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (729919451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (729919451, 1)] : List FactorBlock).map factorBlockValue).prod) = 5839355609 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_729919451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 5839355609) ^ 2919677804 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 5839355609) ^ 8 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_6037638679 : Nat.Prime 6037638679 := by
  apply lucas_primality 6037638679 (3 : ZMod 6037638679)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) = 6037638679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_31
      · exact prime_oneHundredFiftyFourEV_10820141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6037638679) ^ 3018819339 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 2012546226 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 194762538 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 558 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_6393737663 : Nat.Prime 6393737663 := by
  apply lucas_primality 6393737663 (5 : ZMod 6393737663)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (23, 1), (31, 1), (311, 1), (1109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (23, 1), (31, 1), (311, 1), (1109, 1)] : List FactorBlock).map factorBlockValue).prod) = 6393737663 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_13
      · exact prime_oneHundredFiftyFourEV_23
      · exact prime_oneHundredFiftyFourEV_31
      · exact prime_oneHundredFiftyFourEV_311
      · exact prime_oneHundredFiftyFourEV_1109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 6393737663) ^ 3196868831 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 6393737663) ^ 491825974 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 6393737663) ^ 277988594 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 6393737663) ^ 206249602 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 6393737663) ^ 20558642 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 6393737663) ^ 5765318 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_8334709931 : Nat.Prime 8334709931 := by
  apply lucas_primality 8334709931 (2 : ZMod 8334709931)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (59, 1), (14126627, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (59, 1), (14126627, 1)] : List FactorBlock).map factorBlockValue).prod) = 8334709931 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_5
      · exact prime_oneHundredFiftyFourEV_59
      · exact prime_oneHundredFiftyFourEV_14126627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 8334709931) ^ 4167354965 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 8334709931) ^ 1666941986 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 8334709931) ^ 141266270 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 8334709931) ^ 590 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_8595025147 : Nat.Prime 8595025147 := by
  apply lucas_primality 8595025147 (2 : ZMod 8595025147)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (1951, 1), (244747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (1951, 1), (244747, 1)] : List FactorBlock).map factorBlockValue).prod) = 8595025147 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_1951
      · exact prime_oneHundredFiftyFourEV_244747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 8595025147) ^ 4297512573 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 8595025147) ^ 2865008382 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 8595025147) ^ 4405446 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 8595025147) ^ 35118 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_10326046771 : Nat.Prime 10326046771 := by
  apply lucas_primality 10326046771 (10 : ZMod 10326046771)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (13, 1), (107, 1), (82483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (13, 1), (107, 1), (82483, 1)] : List FactorBlock).map factorBlockValue).prod) = 10326046771 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_5
      · exact prime_oneHundredFiftyFourEV_13
      · exact prime_oneHundredFiftyFourEV_107
      · exact prime_oneHundredFiftyFourEV_82483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 10326046771) ^ 5163023385 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (10 : ZMod 10326046771) ^ 3442015590 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (10 : ZMod 10326046771) ^ 2065209354 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (10 : ZMod 10326046771) ^ 794311290 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (10 : ZMod 10326046771) ^ 96505110 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (10 : ZMod 10326046771) ^ 125190 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_12229767619 : Nat.Prime 12229767619 := by
  apply lucas_primality 12229767619 (3 : ZMod 12229767619)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (14771, 1), (137993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (14771, 1), (137993, 1)] : List FactorBlock).map factorBlockValue).prod) = 12229767619 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_14771
      · exact prime_oneHundredFiftyFourEV_137993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 12229767619) ^ 6114883809 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 12229767619) ^ 4076589206 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 12229767619) ^ 827958 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 12229767619) ^ 88626 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_12382161317 : Nat.Prime 12382161317 := by
  apply lucas_primality 12382161317 (5 : ZMod 12382161317)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (1193, 1), (370679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (1193, 1), (370679, 1)] : List FactorBlock).map factorBlockValue).prod) = 12382161317 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_7
      · exact prime_oneHundredFiftyFourEV_1193
      · exact prime_oneHundredFiftyFourEV_370679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 12382161317) ^ 6191080658 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 12382161317) ^ 1768880188 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 12382161317) ^ 10379012 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 12382161317) ^ 33404 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_12455523343 : Nat.Prime 12455523343 := by
  apply lucas_primality 12455523343 (5 : ZMod 12455523343)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (37, 1), (18701987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (37, 1), (18701987, 1)] : List FactorBlock).map factorBlockValue).prod) = 12455523343 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_37
      · exact prime_oneHundredFiftyFourEV_18701987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 12455523343) ^ 6227761671 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 12455523343) ^ 4151841114 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 12455523343) ^ 336635766 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 12455523343) ^ 666 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_14026408709 : Nat.Prime 14026408709 := by
  apply lucas_primality 14026408709 (2 : ZMod 14026408709)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (83, 1), (3249863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (83, 1), (3249863, 1)] : List FactorBlock).map factorBlockValue).prod) = 14026408709 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_13
      · exact prime_oneHundredFiftyFourEV_83
      · exact prime_oneHundredFiftyFourEV_3249863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 14026408709) ^ 7013204354 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 14026408709) ^ 1078954516 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 14026408709) ^ 168992876 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 14026408709) ^ 4316 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_15631865111 : Nat.Prime 15631865111 := by
  apply lucas_primality 15631865111 (7 : ZMod 15631865111)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1563186511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1563186511, 1)] : List FactorBlock).map factorBlockValue).prod) = 15631865111 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_5
      · exact prime_oneHundredFiftyFourEV_1563186511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 15631865111) ^ 7815932555 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (7 : ZMod 15631865111) ^ 3126373022 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (7 : ZMod 15631865111) ^ 10 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_16669419863 : Nat.Prime 16669419863 := by
  apply lucas_primality 16669419863 (5 : ZMod 16669419863)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (8334709931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (8334709931, 1)] : List FactorBlock).map factorBlockValue).prod) = 16669419863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_8334709931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 16669419863) ^ 8334709931 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 16669419863) ^ 2 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_17655048491 : Nat.Prime 17655048491 := by
  apply lucas_primality 17655048491 (2 : ZMod 17655048491)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (59, 1), (29923811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (59, 1), (29923811, 1)] : List FactorBlock).map factorBlockValue).prod) = 17655048491 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_5
      · exact prime_oneHundredFiftyFourEV_59
      · exact prime_oneHundredFiftyFourEV_29923811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 17655048491) ^ 8827524245 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 17655048491) ^ 3531009698 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 17655048491) ^ 299238110 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 17655048491) ^ 590 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_19595768371 : Nat.Prime 19595768371 := by
  apply lucas_primality 19595768371 (3 : ZMod 19595768371)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (19, 1), (41, 1), (503, 1), (1667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (19, 1), (41, 1), (503, 1), (1667, 1)] : List FactorBlock).map factorBlockValue).prod) = 19595768371 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_5
      · exact prime_oneHundredFiftyFourEV_19
      · exact prime_oneHundredFiftyFourEV_41
      · exact prime_oneHundredFiftyFourEV_503
      · exact prime_oneHundredFiftyFourEV_1667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 19595768371) ^ 9797884185 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 19595768371) ^ 6531922790 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 19595768371) ^ 3919153674 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 19595768371) ^ 1031356230 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 19595768371) ^ 477945570 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 19595768371) ^ 38957790 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 19595768371) ^ 11755110 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_20106275743 : Nat.Prime 20106275743 := by
  apply lucas_primality 20106275743 (3 : ZMod 20106275743)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 2), (22796231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 2), (22796231, 1)] : List FactorBlock).map factorBlockValue).prod) = 20106275743 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_7
      · exact prime_oneHundredFiftyFourEV_22796231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 20106275743) ^ 10053137871 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 20106275743) ^ 6702091914 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 20106275743) ^ 2872325106 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 20106275743) ^ 882 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_20138181659 : Nat.Prime 20138181659 := by
  apply lucas_primality 20138181659 (2 : ZMod 20138181659)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (43, 1), (33452129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (43, 1), (33452129, 1)] : List FactorBlock).map factorBlockValue).prod) = 20138181659 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_7
      · exact prime_oneHundredFiftyFourEV_43
      · exact prime_oneHundredFiftyFourEV_33452129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 20138181659) ^ 10069090829 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 20138181659) ^ 2876883094 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 20138181659) ^ 468329806 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 20138181659) ^ 602 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_21058876099 : Nat.Prime 21058876099 := by
  apply lucas_primality 21058876099 (2 : ZMod 21058876099)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (13, 1), (359, 1), (83561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (13, 1), (359, 1), (83561, 1)] : List FactorBlock).map factorBlockValue).prod) = 21058876099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_13
      · exact prime_oneHundredFiftyFourEV_359
      · exact prime_oneHundredFiftyFourEV_83561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 21058876099) ^ 10529438049 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 21058876099) ^ 7019625366 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 21058876099) ^ 1619913546 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 21058876099) ^ 58659822 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 21058876099) ^ 252018 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_22276814491 : Nat.Prime 22276814491 := by
  apply lucas_primality 22276814491 (2 : ZMod 22276814491)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 1), (35360023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 1), (35360023, 1)] : List FactorBlock).map factorBlockValue).prod) = 22276814491 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_5
      · exact prime_oneHundredFiftyFourEV_7
      · exact prime_oneHundredFiftyFourEV_35360023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 22276814491) ^ 11138407245 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 22276814491) ^ 7425604830 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 22276814491) ^ 4455362898 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 22276814491) ^ 3182402070 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 22276814491) ^ 630 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_22280530319 : Nat.Prime 22280530319 := by
  apply lucas_primality 22280530319 (11 : ZMod 22280530319)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2731, 1), (4079189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2731, 1), (4079189, 1)] : List FactorBlock).map factorBlockValue).prod) = 22280530319 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_2731
      · exact prime_oneHundredFiftyFourEV_4079189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 22280530319) ^ 11140265159 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (11 : ZMod 22280530319) ^ 8158378 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (11 : ZMod 22280530319) ^ 5462 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_25368913001 : Nat.Prime 25368913001 := by
  apply lucas_primality 25368913001 (3 : ZMod 25368913001)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 3), (17, 1), (1492289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 3), (17, 1), (1492289, 1)] : List FactorBlock).map factorBlockValue).prod) = 25368913001 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_5
      · exact prime_oneHundredFiftyFourEV_17
      · exact prime_oneHundredFiftyFourEV_1492289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 25368913001) ^ 12684456500 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 25368913001) ^ 5073782600 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 25368913001) ^ 1492289000 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 25368913001) ^ 17000 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_27649692439 : Nat.Prime 27649692439 := by
  apply lucas_primality 27649692439 (3 : ZMod 27649692439)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (4608282073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (4608282073, 1)] : List FactorBlock).map factorBlockValue).prod) = 27649692439 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_4608282073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 27649692439) ^ 13824846219 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 27649692439) ^ 9216564146 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 27649692439) ^ 6 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_27918548017 : Nat.Prime 27918548017 := by
  apply lucas_primality 27918548017 (5 : ZMod 27918548017)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (19, 1), (30612443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (19, 1), (30612443, 1)] : List FactorBlock).map factorBlockValue).prod) = 27918548017 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_19
      · exact prime_oneHundredFiftyFourEV_30612443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 27918548017) ^ 13959274008 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 27918548017) ^ 9306182672 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 27918548017) ^ 1469397264 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 27918548017) ^ 912 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_29485457179 : Nat.Prime 29485457179 := by
  apply lucas_primality 29485457179 (2 : ZMod 29485457179)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (4914242863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (4914242863, 1)] : List FactorBlock).map factorBlockValue).prod) = 29485457179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_4914242863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 29485457179) ^ 14742728589 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 29485457179) ^ 9828485726 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 29485457179) ^ 6 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_33446361583 : Nat.Prime 33446361583 := by
  apply lucas_primality 33446361583 (3 : ZMod 33446361583)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (23, 1), (211, 1), (382883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (23, 1), (211, 1), (382883, 1)] : List FactorBlock).map factorBlockValue).prod) = 33446361583 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_23
      · exact prime_oneHundredFiftyFourEV_211
      · exact prime_oneHundredFiftyFourEV_382883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 33446361583) ^ 16723180791 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 33446361583) ^ 11148787194 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 33446361583) ^ 1454189634 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 33446361583) ^ 158513562 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 33446361583) ^ 87354 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_33595162049 : Nat.Prime 33595162049 := by
  apply lucas_primality 33595162049 (3 : ZMod 33595162049)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (7, 2), (10712743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (7, 2), (10712743, 1)] : List FactorBlock).map factorBlockValue).prod) = 33595162049 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_7
      · exact prime_oneHundredFiftyFourEV_10712743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 33595162049) ^ 16797581024 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 33595162049) ^ 4799308864 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 33595162049) ^ 3136 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_36300018113 : Nat.Prime 36300018113 := by
  apply lucas_primality 36300018113 (3 : ZMod 36300018113)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (567187783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (567187783, 1)] : List FactorBlock).map factorBlockValue).prod) = 36300018113 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_567187783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 36300018113) ^ 18150009056 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 36300018113) ^ 64 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_36476141627 : Nat.Prime 36476141627 := by
  apply lucas_primality 36476141627 (2 : ZMod 36476141627)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (8647, 1), (2109179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (8647, 1), (2109179, 1)] : List FactorBlock).map factorBlockValue).prod) = 36476141627 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_8647
      · exact prime_oneHundredFiftyFourEV_2109179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 36476141627) ^ 18238070813 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 36476141627) ^ 4218358 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 36476141627) ^ 17294 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_36935983321 : Nat.Prime 36935983321 := by
  apply lucas_primality 36935983321 (7 : ZMod 36935983321)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (307799861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (307799861, 1)] : List FactorBlock).map factorBlockValue).prod) = 36935983321 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_5
      · exact prime_oneHundredFiftyFourEV_307799861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 36935983321) ^ 18467991660 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (7 : ZMod 36935983321) ^ 12311994440 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (7 : ZMod 36935983321) ^ 7387196664 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (7 : ZMod 36935983321) ^ 120 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_45549551461 : Nat.Prime 45549551461 := by
  apply lucas_primality 45549551461 (6 : ZMod 45549551461)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (17, 1), (293, 1), (21773, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (17, 1), (293, 1), (21773, 1)] : List FactorBlock).map factorBlockValue).prod) = 45549551461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_5
      · exact prime_oneHundredFiftyFourEV_7
      · exact prime_oneHundredFiftyFourEV_17
      · exact prime_oneHundredFiftyFourEV_293
      · exact prime_oneHundredFiftyFourEV_21773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 45549551461) ^ 22774775730 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (6 : ZMod 45549551461) ^ 15183183820 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (6 : ZMod 45549551461) ^ 9109910292 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (6 : ZMod 45549551461) ^ 6507078780 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (6 : ZMod 45549551461) ^ 2679385380 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (6 : ZMod 45549551461) ^ 155459220 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (6 : ZMod 45549551461) ^ 2092020 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_45636734023 : Nat.Prime 45636734023 := by
  apply lucas_primality 45636734023 (6 : ZMod 45636734023)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (17, 1), (40674451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (17, 1), (40674451, 1)] : List FactorBlock).map factorBlockValue).prod) = 45636734023 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_11
      · exact prime_oneHundredFiftyFourEV_17
      · exact prime_oneHundredFiftyFourEV_40674451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 45636734023) ^ 22818367011 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (6 : ZMod 45636734023) ^ 15212244674 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (6 : ZMod 45636734023) ^ 4148794002 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (6 : ZMod 45636734023) ^ 2684513766 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (6 : ZMod 45636734023) ^ 1122 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_51345366139 : Nat.Prime 51345366139 := by
  apply lucas_primality 51345366139 (2 : ZMod 51345366139)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (1889, 1), (137279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (1889, 1), (137279, 1)] : List FactorBlock).map factorBlockValue).prod) = 51345366139 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_11
      · exact prime_oneHundredFiftyFourEV_1889
      · exact prime_oneHundredFiftyFourEV_137279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 51345366139) ^ 25672683069 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 51345366139) ^ 17115122046 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 51345366139) ^ 4667760558 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 51345366139) ^ 27181242 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 51345366139) ^ 374022 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_54404582207 : Nat.Prime 54404582207 := by
  apply lucas_primality 54404582207 (5 : ZMod 54404582207)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (43, 1), (1327, 1), (36671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (43, 1), (1327, 1), (36671, 1)] : List FactorBlock).map factorBlockValue).prod) = 54404582207 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_13
      · exact prime_oneHundredFiftyFourEV_43
      · exact prime_oneHundredFiftyFourEV_1327
      · exact prime_oneHundredFiftyFourEV_36671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 54404582207) ^ 27202291103 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 54404582207) ^ 4184967862 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 54404582207) ^ 1265222842 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 54404582207) ^ 40998178 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 54404582207) ^ 1483586 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_56645794981 : Nat.Prime 56645794981 := by
  apply lucas_primality 56645794981 (7 : ZMod 56645794981)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (59, 1), (1907, 1), (2797, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (59, 1), (1907, 1), (2797, 1)] : List FactorBlock).map factorBlockValue).prod) = 56645794981 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_5
      · exact prime_oneHundredFiftyFourEV_59
      · exact prime_oneHundredFiftyFourEV_1907
      · exact prime_oneHundredFiftyFourEV_2797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 56645794981) ^ 28322897490 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (7 : ZMod 56645794981) ^ 18881931660 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (7 : ZMod 56645794981) ^ 11329158996 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (7 : ZMod 56645794981) ^ 960098220 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (7 : ZMod 56645794981) ^ 29704140 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (7 : ZMod 56645794981) ^ 20252340 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_57700314109 : Nat.Prime 57700314109 := by
  apply lucas_primality 57700314109 (6 : ZMod 57700314109)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (17, 1), (499, 1), (188941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (17, 1), (499, 1), (188941, 1)] : List FactorBlock).map factorBlockValue).prod) = 57700314109 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_17
      · exact prime_oneHundredFiftyFourEV_499
      · exact prime_oneHundredFiftyFourEV_188941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 57700314109) ^ 28850157054 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (6 : ZMod 57700314109) ^ 19233438036 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (6 : ZMod 57700314109) ^ 3394136124 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (6 : ZMod 57700314109) ^ 115631892 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (6 : ZMod 57700314109) ^ 305388 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_60918052201 : Nat.Prime 60918052201 := by
  apply lucas_primality 60918052201 (31 : ZMod 60918052201)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 2), (103, 1), (985729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 2), (103, 1), (985729, 1)] : List FactorBlock).map factorBlockValue).prod) = 60918052201 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_5
      · exact prime_oneHundredFiftyFourEV_103
      · exact prime_oneHundredFiftyFourEV_985729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (31 : ZMod 60918052201) ^ 30459026100 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (31 : ZMod 60918052201) ^ 20306017400 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (31 : ZMod 60918052201) ^ 12183610440 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (31 : ZMod 60918052201) ^ 591437400 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (31 : ZMod 60918052201) ^ 61800 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_63583326349 : Nat.Prime 63583326349 := by
  apply lucas_primality 63583326349 (2 : ZMod 63583326349)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5298610529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5298610529, 1)] : List FactorBlock).map factorBlockValue).prod) = 63583326349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_5298610529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 63583326349) ^ 31791663174 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 63583326349) ^ 21194442116 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 63583326349) ^ 12 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_64002540631 : Nat.Prime 64002540631 := by
  apply lucas_primality 64002540631 (3 : ZMod 64002540631)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (19, 1), (89, 1), (180233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (19, 1), (89, 1), (180233, 1)] : List FactorBlock).map factorBlockValue).prod) = 64002540631 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_5
      · exact prime_oneHundredFiftyFourEV_7
      · exact prime_oneHundredFiftyFourEV_19
      · exact prime_oneHundredFiftyFourEV_89
      · exact prime_oneHundredFiftyFourEV_180233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 64002540631) ^ 32001270315 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 64002540631) ^ 21334180210 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 64002540631) ^ 12800508126 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 64002540631) ^ 9143220090 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 64002540631) ^ 3368554770 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 64002540631) ^ 719129670 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 64002540631) ^ 355110 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_146223704779 : Nat.Prime 146223704779 := by
  apply lucas_primality 146223704779 (2 : ZMod 146223704779)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (53, 1), (97, 1), (249497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (53, 1), (97, 1), (249497, 1)] : List FactorBlock).map factorBlockValue).prod) = 146223704779 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_19
      · exact prime_oneHundredFiftyFourEV_53
      · exact prime_oneHundredFiftyFourEV_97
      · exact prime_oneHundredFiftyFourEV_249497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 146223704779) ^ 73111852389 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 146223704779) ^ 48741234926 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 146223704779) ^ 7695984462 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 146223704779) ^ 2758937826 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 146223704779) ^ 1507460874 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 146223704779) ^ 586074 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_155440836073 : Nat.Prime 155440836073 := by
  apply lucas_primality 155440836073 (5 : ZMod 155440836073)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (89, 1), (373, 1), (65033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (89, 1), (373, 1), (65033, 1)] : List FactorBlock).map factorBlockValue).prod) = 155440836073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_89
      · exact prime_oneHundredFiftyFourEV_373
      · exact prime_oneHundredFiftyFourEV_65033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 155440836073) ^ 77720418036 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 155440836073) ^ 51813612024 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 155440836073) ^ 1746526248 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 155440836073) ^ 416731464 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 155440836073) ^ 2390184 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_166467108527 : Nat.Prime 166467108527 := by
  apply lucas_primality 166467108527 (5 : ZMod 166467108527)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (97, 1), (858077879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (97, 1), (858077879, 1)] : List FactorBlock).map factorBlockValue).prod) = 166467108527 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_97
      · exact prime_oneHundredFiftyFourEV_858077879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 166467108527) ^ 83233554263 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 166467108527) ^ 1716155758 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 166467108527) ^ 194 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_186461254597 : Nat.Prime 186461254597 := by
  apply lucas_primality 186461254597 (6 : ZMod 186461254597)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (463, 1), (491, 1), (68351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (463, 1), (491, 1), (68351, 1)] : List FactorBlock).map factorBlockValue).prod) = 186461254597 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_463
      · exact prime_oneHundredFiftyFourEV_491
      · exact prime_oneHundredFiftyFourEV_68351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 186461254597) ^ 93230627298 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (6 : ZMod 186461254597) ^ 62153751532 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (6 : ZMod 186461254597) ^ 402724092 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (6 : ZMod 186461254597) ^ 379758156 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (6 : ZMod 186461254597) ^ 2727996 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_191606627809 : Nat.Prime 191606627809 := by
  apply lucas_primality 191606627809 (23 : ZMod 191606627809)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (79, 1), (8421529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (79, 1), (8421529, 1)] : List FactorBlock).map factorBlockValue).prod) = 191606627809 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_79
      · exact prime_oneHundredFiftyFourEV_8421529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (23 : ZMod 191606627809) ^ 95803313904 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (23 : ZMod 191606627809) ^ 63868875936 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (23 : ZMod 191606627809) ^ 2425400352 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (23 : ZMod 191606627809) ^ 22752 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_210359508407 : Nat.Prime 210359508407 := by
  apply lucas_primality 210359508407 (5 : ZMod 210359508407)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (859, 1), (6444443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (859, 1), (6444443, 1)] : List FactorBlock).map factorBlockValue).prod) = 210359508407 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_19
      · exact prime_oneHundredFiftyFourEV_859
      · exact prime_oneHundredFiftyFourEV_6444443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 210359508407) ^ 105179754203 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 210359508407) ^ 11071553074 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 210359508407) ^ 244888834 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 210359508407) ^ 32642 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_211729106731 : Nat.Prime 211729106731 := by
  apply lucas_primality 211729106731 (2 : ZMod 211729106731)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (37, 1), (190746943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (37, 1), (190746943, 1)] : List FactorBlock).map factorBlockValue).prod) = 211729106731 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_5
      · exact prime_oneHundredFiftyFourEV_37
      · exact prime_oneHundredFiftyFourEV_190746943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 211729106731) ^ 105864553365 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 211729106731) ^ 70576368910 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 211729106731) ^ 42345821346 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 211729106731) ^ 5722408290 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 211729106731) ^ 1110 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_213948011897 : Nat.Prime 213948011897 := by
  apply lucas_primality 213948011897 (3 : ZMod 213948011897)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (331, 1), (2339, 1), (34543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (331, 1), (2339, 1), (34543, 1)] : List FactorBlock).map factorBlockValue).prod) = 213948011897 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_331
      · exact prime_oneHundredFiftyFourEV_2339
      · exact prime_oneHundredFiftyFourEV_34543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 213948011897) ^ 106974005948 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 213948011897) ^ 646368616 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 213948011897) ^ 91469864 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 213948011897) ^ 6193672 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_221450079283 : Nat.Prime 221450079283 := by
  apply lucas_primality 221450079283 (2 : ZMod 221450079283)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (89, 1), (139, 1), (2983457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (89, 1), (139, 1), (2983457, 1)] : List FactorBlock).map factorBlockValue).prod) = 221450079283 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_89
      · exact prime_oneHundredFiftyFourEV_139
      · exact prime_oneHundredFiftyFourEV_2983457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 221450079283) ^ 110725039641 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 221450079283) ^ 73816693094 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 221450079283) ^ 2488203138 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 221450079283) ^ 1593166038 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 221450079283) ^ 74226 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_222060357569 : Nat.Prime 222060357569 := by
  apply lucas_primality 222060357569 (6 : ZMod 222060357569)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (7, 2), (70810063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (7, 2), (70810063, 1)] : List FactorBlock).map factorBlockValue).prod) = 222060357569 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_7
      · exact prime_oneHundredFiftyFourEV_70810063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 222060357569) ^ 111030178784 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (6 : ZMod 222060357569) ^ 31722908224 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (6 : ZMod 222060357569) ^ 3136 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_229144217941 : Nat.Prime 229144217941 := by
  apply lucas_primality 229144217941 (2 : ZMod 229144217941)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (11, 1), (757, 1), (152879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (11, 1), (757, 1), (152879, 1)] : List FactorBlock).map factorBlockValue).prod) = 229144217941 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_5
      · exact prime_oneHundredFiftyFourEV_11
      · exact prime_oneHundredFiftyFourEV_757
      · exact prime_oneHundredFiftyFourEV_152879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 229144217941) ^ 114572108970 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 229144217941) ^ 76381405980 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 229144217941) ^ 45828843588 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 229144217941) ^ 20831292540 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 229144217941) ^ 302700420 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 229144217941) ^ 1498860 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_247705291543 : Nat.Prime 247705291543 := by
  apply lucas_primality 247705291543 (5 : ZMod 247705291543)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (3659, 1), (11282923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (3659, 1), (11282923, 1)] : List FactorBlock).map factorBlockValue).prod) = 247705291543 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_3659
      · exact prime_oneHundredFiftyFourEV_11282923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 247705291543) ^ 123852645771 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 247705291543) ^ 82568430514 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 247705291543) ^ 67697538 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 247705291543) ^ 21954 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_265357644379 : Nat.Prime 265357644379 := by
  apply lucas_primality 265357644379 (10 : ZMod 265357644379)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (1922881481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (1922881481, 1)] : List FactorBlock).map factorBlockValue).prod) = 265357644379 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_23
      · exact prime_oneHundredFiftyFourEV_1922881481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 265357644379) ^ 132678822189 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (10 : ZMod 265357644379) ^ 88452548126 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (10 : ZMod 265357644379) ^ 11537288886 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (10 : ZMod 265357644379) ^ 138 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_269575124101 : Nat.Prime 269575124101 := by
  apply lucas_primality 269575124101 (2 : ZMod 269575124101)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (59, 1), (167, 1), (91199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (59, 1), (167, 1), (91199, 1)] : List FactorBlock).map factorBlockValue).prod) = 269575124101 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_5
      · exact prime_oneHundredFiftyFourEV_59
      · exact prime_oneHundredFiftyFourEV_167
      · exact prime_oneHundredFiftyFourEV_91199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 269575124101) ^ 134787562050 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 269575124101) ^ 89858374700 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 269575124101) ^ 53915024820 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 269575124101) ^ 4569069900 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 269575124101) ^ 1614222300 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 269575124101) ^ 2955900 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_282674030603 : Nat.Prime 282674030603 := by
  apply lucas_primality 282674030603 (2 : ZMod 282674030603)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (397, 1), (18737507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (397, 1), (18737507, 1)] : List FactorBlock).map factorBlockValue).prod) = 282674030603 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_19
      · exact prime_oneHundredFiftyFourEV_397
      · exact prime_oneHundredFiftyFourEV_18737507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 282674030603) ^ 141337015301 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 282674030603) ^ 14877580558 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 282674030603) ^ 712025266 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 282674030603) ^ 15086 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_343588771969 : Nat.Prime 343588771969 := by
  apply lucas_primality 343588771969 (31 : ZMod 343588771969)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (13, 1), (3931, 1), (17509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (13, 1), (3931, 1), (17509, 1)] : List FactorBlock).map factorBlockValue).prod) = 343588771969 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_13
      · exact prime_oneHundredFiftyFourEV_3931
      · exact prime_oneHundredFiftyFourEV_17509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (31 : ZMod 343588771969) ^ 171794385984 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (31 : ZMod 343588771969) ^ 114529590656 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (31 : ZMod 343588771969) ^ 26429905536 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (31 : ZMod 343588771969) ^ 87404928 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (31 : ZMod 343588771969) ^ 19623552 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_364306411607 : Nat.Prime 364306411607 := by
  apply lucas_primality 364306411607 (5 : ZMod 364306411607)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (761, 1), (14080019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (761, 1), (14080019, 1)] : List FactorBlock).map factorBlockValue).prod) = 364306411607 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_17
      · exact prime_oneHundredFiftyFourEV_761
      · exact prime_oneHundredFiftyFourEV_14080019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 364306411607) ^ 182153205803 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 364306411607) ^ 21429788918 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 364306411607) ^ 478720646 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 364306411607) ^ 25874 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_367910052721 : Nat.Prime 367910052721 := by
  apply lucas_primality 367910052721 (11 : ZMod 367910052721)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (7, 1), (41, 1), (5341319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (7, 1), (41, 1), (5341319, 1)] : List FactorBlock).map factorBlockValue).prod) = 367910052721 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_5
      · exact prime_oneHundredFiftyFourEV_7
      · exact prime_oneHundredFiftyFourEV_41
      · exact prime_oneHundredFiftyFourEV_5341319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 367910052721) ^ 183955026360 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (11 : ZMod 367910052721) ^ 122636684240 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (11 : ZMod 367910052721) ^ 73582010544 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (11 : ZMod 367910052721) ^ 52558578960 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (11 : ZMod 367910052721) ^ 8973415920 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (11 : ZMod 367910052721) ^ 68880 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_443231799853 : Nat.Prime 443231799853 := by
  apply lucas_primality 443231799853 (2 : ZMod 443231799853)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (36935983321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (36935983321, 1)] : List FactorBlock).map factorBlockValue).prod) = 443231799853 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_36935983321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 443231799853) ^ 221615899926 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 443231799853) ^ 147743933284 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 443231799853) ^ 12 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_455495514611 : Nat.Prime 455495514611 := by
  apply lucas_primality 455495514611 (2 : ZMod 455495514611)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (45549551461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (45549551461, 1)] : List FactorBlock).map factorBlockValue).prod) = 455495514611 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_5
      · exact prime_oneHundredFiftyFourEV_45549551461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 455495514611) ^ 227747757305 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 455495514611) ^ 91099102922 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 455495514611) ^ 10 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_476907466417 : Nat.Prime 476907466417 := by
  apply lucas_primality 476907466417 (10 : ZMod 476907466417)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (43, 1), (73, 1), (3165203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (43, 1), (73, 1), (3165203, 1)] : List FactorBlock).map factorBlockValue).prod) = 476907466417 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_43
      · exact prime_oneHundredFiftyFourEV_73
      · exact prime_oneHundredFiftyFourEV_3165203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 476907466417) ^ 238453733208 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (10 : ZMod 476907466417) ^ 158969155472 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (10 : ZMod 476907466417) ^ 11090871312 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (10 : ZMod 476907466417) ^ 6532978992 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (10 : ZMod 476907466417) ^ 150672 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_566275802233 : Nat.Prime 566275802233 := by
  apply lucas_primality 566275802233 (5 : ZMod 566275802233)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (20773, 1), (162263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (20773, 1), (162263, 1)] : List FactorBlock).map factorBlockValue).prod) = 566275802233 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_7
      · exact prime_oneHundredFiftyFourEV_20773
      · exact prime_oneHundredFiftyFourEV_162263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 566275802233) ^ 283137901116 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 566275802233) ^ 188758600744 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 566275802233) ^ 80896543176 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 566275802233) ^ 27260184 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 566275802233) ^ 3489864 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_700722673081 : Nat.Prime 700722673081 := by
  apply lucas_primality 700722673081 (13 : ZMod 700722673081)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (5839355609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (5839355609, 1)] : List FactorBlock).map factorBlockValue).prod) = 700722673081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_5
      · exact prime_oneHundredFiftyFourEV_5839355609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 700722673081) ^ 350361336540 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (13 : ZMod 700722673081) ^ 233574224360 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (13 : ZMod 700722673081) ^ 140144534616 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (13 : ZMod 700722673081) ^ 120 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_705282323897 : Nat.Prime 705282323897 := by
  apply lucas_primality 705282323897 (3 : ZMod 705282323897)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (659, 1), (3359, 1), (39827, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (659, 1), (3359, 1), (39827, 1)] : List FactorBlock).map factorBlockValue).prod) = 705282323897 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_659
      · exact prime_oneHundredFiftyFourEV_3359
      · exact prime_oneHundredFiftyFourEV_39827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 705282323897) ^ 352641161948 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 705282323897) ^ 1070231144 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 705282323897) ^ 209967944 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 705282323897) ^ 17708648 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_1295508299753 : Nat.Prime 1295508299753 := by
  apply lucas_primality 1295508299753 (3 : ZMod 1295508299753)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (43759, 1), (3700691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (43759, 1), (3700691, 1)] : List FactorBlock).map factorBlockValue).prod) = 1295508299753 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_43759
      · exact prime_oneHundredFiftyFourEV_3700691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1295508299753) ^ 647754149876 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1295508299753) ^ 29605528 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1295508299753) ^ 350072 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_1382416129541 : Nat.Prime 1382416129541 := by
  apply lucas_primality 1382416129541 (3 : ZMod 1382416129541)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (19, 1), (2069, 1), (1758307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (19, 1), (2069, 1), (1758307, 1)] : List FactorBlock).map factorBlockValue).prod) = 1382416129541 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_5
      · exact prime_oneHundredFiftyFourEV_19
      · exact prime_oneHundredFiftyFourEV_2069
      · exact prime_oneHundredFiftyFourEV_1758307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1382416129541) ^ 691208064770 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1382416129541) ^ 276483225908 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1382416129541) ^ 72758743660 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1382416129541) ^ 668156660 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1382416129541) ^ 786220 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_1405796033527 : Nat.Prime 1405796033527 := by
  apply lucas_primality 1405796033527 (3 : ZMod 1405796033527)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 1), (31, 1), (260622179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 1), (31, 1), (260622179, 1)] : List FactorBlock).map factorBlockValue).prod) = 1405796033527 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_29
      · exact prime_oneHundredFiftyFourEV_31
      · exact prime_oneHundredFiftyFourEV_260622179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1405796033527) ^ 702898016763 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1405796033527) ^ 468598677842 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1405796033527) ^ 48475725294 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1405796033527) ^ 45348259146 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1405796033527) ^ 5394 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_1408055893883 : Nat.Prime 1408055893883 := by
  apply lucas_primality 1408055893883 (5 : ZMod 1408055893883)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (64002540631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (64002540631, 1)] : List FactorBlock).map factorBlockValue).prod) = 1408055893883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_11
      · exact prime_oneHundredFiftyFourEV_64002540631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1408055893883) ^ 704027946941 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 1408055893883) ^ 128005081262 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 1408055893883) ^ 22 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_1408520993987 : Nat.Prime 1408520993987 := by
  apply lucas_primality 1408520993987 (2 : ZMod 1408520993987)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (109, 1), (340058183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (109, 1), (340058183, 1)] : List FactorBlock).map factorBlockValue).prod) = 1408520993987 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_19
      · exact prime_oneHundredFiftyFourEV_109
      · exact prime_oneHundredFiftyFourEV_340058183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1408520993987) ^ 704260496993 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1408520993987) ^ 74132683894 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1408520993987) ^ 12922210954 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1408520993987) ^ 4142 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_1486231749259 : Nat.Prime 1486231749259 := by
  apply lucas_primality 1486231749259 (3 : ZMod 1486231749259)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (247705291543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (247705291543, 1)] : List FactorBlock).map factorBlockValue).prod) = 1486231749259 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_247705291543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1486231749259) ^ 743115874629 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1486231749259) ^ 495410583086 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1486231749259) ^ 6 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_2282563331837 : Nat.Prime 2282563331837 := by
  apply lucas_primality 2282563331837 (2 : ZMod 2282563331837)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (157, 1), (6133, 1), (592639, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (157, 1), (6133, 1), (592639, 1)] : List FactorBlock).map factorBlockValue).prod) = 2282563331837 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_157
      · exact prime_oneHundredFiftyFourEV_6133
      · exact prime_oneHundredFiftyFourEV_592639
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2282563331837) ^ 1141281665918 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2282563331837) ^ 14538619948 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2282563331837) ^ 372177292 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2282563331837) ^ 3851524 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_2486991238073 : Nat.Prime 2486991238073 := by
  apply lucas_primality 2486991238073 (3 : ZMod 2486991238073)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (19, 1), (859, 1), (1731589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (19, 1), (859, 1), (1731589, 1)] : List FactorBlock).map factorBlockValue).prod) = 2486991238073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_11
      · exact prime_oneHundredFiftyFourEV_19
      · exact prime_oneHundredFiftyFourEV_859
      · exact prime_oneHundredFiftyFourEV_1731589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2486991238073) ^ 1243495619036 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 2486991238073) ^ 226090112552 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 2486991238073) ^ 130894275688 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 2486991238073) ^ 2895216808 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 2486991238073) ^ 1436248 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_2546871139697 : Nat.Prime 2546871139697 := by
  apply lucas_primality 2546871139697 (3 : ZMod 2546871139697)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (13, 1), (7039, 1), (1739533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (13, 1), (7039, 1), (1739533, 1)] : List FactorBlock).map factorBlockValue).prod) = 2546871139697 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_13
      · exact prime_oneHundredFiftyFourEV_7039
      · exact prime_oneHundredFiftyFourEV_1739533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2546871139697) ^ 1273435569848 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 2546871139697) ^ 195913164592 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 2546871139697) ^ 361822864 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 2546871139697) ^ 1464112 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_3643964116889 : Nat.Prime 3643964116889 := by
  apply lucas_primality 3643964116889 (3 : ZMod 3643964116889)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (455495514611, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (455495514611, 1)] : List FactorBlock).map factorBlockValue).prod) = 3643964116889 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_455495514611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 3643964116889) ^ 1821982058444 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 3643964116889) ^ 8 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_3803346056467 : Nat.Prime 3803346056467 := by
  apply lucas_primality 3803346056467 (5 : ZMod 3803346056467)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 6), (11, 1), (5683, 1), (41729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 6), (11, 1), (5683, 1), (41729, 1)] : List FactorBlock).map factorBlockValue).prod) = 3803346056467 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_11
      · exact prime_oneHundredFiftyFourEV_5683
      · exact prime_oneHundredFiftyFourEV_41729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 3803346056467) ^ 1901673028233 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 3803346056467) ^ 1267782018822 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 3803346056467) ^ 345758732406 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 3803346056467) ^ 669249702 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 3803346056467) ^ 91143954 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_3811123921159 : Nat.Prime 3811123921159 := by
  apply lucas_primality 3811123921159 (7 : ZMod 3811123921159)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (211729106731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (211729106731, 1)] : List FactorBlock).map factorBlockValue).prod) = 3811123921159 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_211729106731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 3811123921159) ^ 1905561960579 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (7 : ZMod 3811123921159) ^ 1270374640386 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (7 : ZMod 3811123921159) ^ 18 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_4952042310107 : Nat.Prime 4952042310107 := by
  apply lucas_primality 4952042310107 (2 : ZMod 4952042310107)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (118297, 1), (675179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (118297, 1), (675179, 1)] : List FactorBlock).map factorBlockValue).prod) = 4952042310107 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_31
      · exact prime_oneHundredFiftyFourEV_118297
      · exact prime_oneHundredFiftyFourEV_675179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4952042310107) ^ 2476021155053 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 4952042310107) ^ 159743300326 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 4952042310107) ^ 41861098 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 4952042310107) ^ 7334414 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_5082002535821 : Nat.Prime 5082002535821 := by
  apply lucas_primality 5082002535821 (3 : ZMod 5082002535821)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (36300018113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (36300018113, 1)] : List FactorBlock).map factorBlockValue).prod) = 5082002535821 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_5
      · exact prime_oneHundredFiftyFourEV_7
      · exact prime_oneHundredFiftyFourEV_36300018113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 5082002535821) ^ 2541001267910 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 5082002535821) ^ 1016400507164 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 5082002535821) ^ 726000362260 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 5082002535821) ^ 140 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_5134536613901 : Nat.Prime 5134536613901 := by
  apply lucas_primality 5134536613901 (2 : ZMod 5134536613901)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (51345366139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (51345366139, 1)] : List FactorBlock).map factorBlockValue).prod) = 5134536613901 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_5
      · exact prime_oneHundredFiftyFourEV_51345366139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 5134536613901) ^ 2567268306950 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 5134536613901) ^ 1026907322780 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 5134536613901) ^ 100 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_6728720156339 : Nat.Prime 6728720156339 := by
  apply lucas_primality 6728720156339 (2 : ZMod 6728720156339)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (151, 1), (22280530319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (151, 1), (22280530319, 1)] : List FactorBlock).map factorBlockValue).prod) = 6728720156339 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_151
      · exact prime_oneHundredFiftyFourEV_22280530319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 6728720156339) ^ 3364360078169 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 6728720156339) ^ 44561060638 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 6728720156339) ^ 302 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_7128916307287 : Nat.Prime 7128916307287 := by
  apply lucas_primality 7128916307287 (3 : ZMod 7128916307287)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (59, 1), (20138181659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (59, 1), (20138181659, 1)] : List FactorBlock).map factorBlockValue).prod) = 7128916307287 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_59
      · exact prime_oneHundredFiftyFourEV_20138181659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 7128916307287) ^ 3564458153643 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 7128916307287) ^ 2376305435762 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 7128916307287) ^ 120829089954 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 7128916307287) ^ 354 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_8998596912829 : Nat.Prime 8998596912829 := by
  apply lucas_primality 8998596912829 (2 : ZMod 8998596912829)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (23, 1), (7823, 1), (4167661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (23, 1), (7823, 1), (4167661, 1)] : List FactorBlock).map factorBlockValue).prod) = 8998596912829 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_23
      · exact prime_oneHundredFiftyFourEV_7823
      · exact prime_oneHundredFiftyFourEV_4167661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8998596912829) ^ 4499298456414 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 8998596912829) ^ 2999532304276 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 8998596912829) ^ 391243344036 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 8998596912829) ^ 1150274436 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 8998596912829) ^ 2159148 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_9231195796909 : Nat.Prime 9231195796909 := by
  apply lucas_primality 9231195796909 (2 : ZMod 9231195796909)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (23, 1), (33446361583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (23, 1), (33446361583, 1)] : List FactorBlock).map factorBlockValue).prod) = 9231195796909 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_23
      · exact prime_oneHundredFiftyFourEV_33446361583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 9231195796909) ^ 4615597898454 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 9231195796909) ^ 3077065265636 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 9231195796909) ^ 401356338996 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 9231195796909) ^ 276 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_10301481476189 : Nat.Prime 10301481476189 := by
  apply lucas_primality 10301481476189 (2 : ZMod 10301481476189)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (367910052721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (367910052721, 1)] : List FactorBlock).map factorBlockValue).prod) = 10301481476189 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_7
      · exact prime_oneHundredFiftyFourEV_367910052721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 10301481476189) ^ 5150740738094 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 10301481476189) ^ 1471640210884 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 10301481476189) ^ 28 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_17160791887493 : Nat.Prime 17160791887493 := by
  apply lucas_primality 17160791887493 (2 : ZMod 17160791887493)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (61, 1), (6393737663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (61, 1), (6393737663, 1)] : List FactorBlock).map factorBlockValue).prod) = 17160791887493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_11
      · exact prime_oneHundredFiftyFourEV_61
      · exact prime_oneHundredFiftyFourEV_6393737663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 17160791887493) ^ 8580395943746 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 17160791887493) ^ 1560071989772 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 17160791887493) ^ 281324457172 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 17160791887493) ^ 2684 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_17765105536579 : Nat.Prime 17765105536579 := by
  apply lucas_primality 17765105536579 (2 : ZMod 17765105536579)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (193, 1), (3631, 1), (248533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (193, 1), (3631, 1), (248533, 1)] : List FactorBlock).map factorBlockValue).prod) = 17765105536579 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_17
      · exact prime_oneHundredFiftyFourEV_193
      · exact prime_oneHundredFiftyFourEV_3631
      · exact prime_oneHundredFiftyFourEV_248533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 17765105536579) ^ 8882552768289 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 17765105536579) ^ 5921701845526 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 17765105536579) ^ 1045006208034 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 17765105536579) ^ 92047178946 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 17765105536579) ^ 4892620638 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 17765105536579) ^ 71479866 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_18584745588337 : Nat.Prime 18584745588337 := by
  apply lucas_primality 18584745588337 (5 : ZMod 18584745588337)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (109, 1), (281, 1), (2633, 1), (4801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (109, 1), (281, 1), (2633, 1), (4801, 1)] : List FactorBlock).map factorBlockValue).prod) = 18584745588337 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_109
      · exact prime_oneHundredFiftyFourEV_281
      · exact prime_oneHundredFiftyFourEV_2633
      · exact prime_oneHundredFiftyFourEV_4801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 18584745588337) ^ 9292372794168 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 18584745588337) ^ 6194915196112 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 18584745588337) ^ 170502253104 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 18584745588337) ^ 66137884656 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 18584745588337) ^ 7058391792 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 18584745588337) ^ 3871015536 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_19005048782851 : Nat.Prime 19005048782851 := by
  apply lucas_primality 19005048782851 (10 : ZMod 19005048782851)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (13, 1), (17, 1), (573304639, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (13, 1), (17, 1), (573304639, 1)] : List FactorBlock).map factorBlockValue).prod) = 19005048782851 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_5
      · exact prime_oneHundredFiftyFourEV_13
      · exact prime_oneHundredFiftyFourEV_17
      · exact prime_oneHundredFiftyFourEV_573304639
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 19005048782851) ^ 9502524391425 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (10 : ZMod 19005048782851) ^ 6335016260950 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (10 : ZMod 19005048782851) ^ 3801009756570 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (10 : ZMod 19005048782851) ^ 1461926829450 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (10 : ZMod 19005048782851) ^ 1117944046050 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (10 : ZMod 19005048782851) ^ 33150 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_27230588007787 : Nat.Prime 27230588007787 := by
  apply lucas_primality 27230588007787 (2 : ZMod 27230588007787)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (2269, 1), (666730033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (2269, 1), (666730033, 1)] : List FactorBlock).map factorBlockValue).prod) = 27230588007787 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_2269
      · exact prime_oneHundredFiftyFourEV_666730033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 27230588007787) ^ 13615294003893 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 27230588007787) ^ 9076862669262 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 27230588007787) ^ 12001140594 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 27230588007787) ^ 40842 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_29868647145209 : Nat.Prime 29868647145209 := by
  apply lucas_primality 29868647145209 (3 : ZMod 29868647145209)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (536491, 1), (6959261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (536491, 1), (6959261, 1)] : List FactorBlock).map factorBlockValue).prod) = 29868647145209 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_536491
      · exact prime_oneHundredFiftyFourEV_6959261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 29868647145209) ^ 14934323572604 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 29868647145209) ^ 55674088 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 29868647145209) ^ 4291928 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_39616338480857 : Nat.Prime 39616338480857 := by
  apply lucas_primality 39616338480857 (3 : ZMod 39616338480857)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (4952042310107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (4952042310107, 1)] : List FactorBlock).map factorBlockValue).prod) = 39616338480857 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_4952042310107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 39616338480857) ^ 19808169240428 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 39616338480857) ^ 8 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_40954565563883 : Nat.Prime 40954565563883 := by
  apply lucas_primality 40954565563883 (2 : ZMod 40954565563883)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (883, 1), (3413, 1), (6794779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (883, 1), (3413, 1), (6794779, 1)] : List FactorBlock).map factorBlockValue).prod) = 40954565563883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_883
      · exact prime_oneHundredFiftyFourEV_3413
      · exact prime_oneHundredFiftyFourEV_6794779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 40954565563883) ^ 20477282781941 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 40954565563883) ^ 46381161454 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 40954565563883) ^ 11999579714 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 40954565563883) ^ 6027358 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_42899271839561 : Nat.Prime 42899271839561 := by
  apply lucas_primality 42899271839561 (6 : ZMod 42899271839561)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (487, 1), (2202221347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (487, 1), (2202221347, 1)] : List FactorBlock).map factorBlockValue).prod) = 42899271839561 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_5
      · exact prime_oneHundredFiftyFourEV_487
      · exact prime_oneHundredFiftyFourEV_2202221347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 42899271839561) ^ 21449635919780 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (6 : ZMod 42899271839561) ^ 8579854367912 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (6 : ZMod 42899271839561) ^ 88088853880 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (6 : ZMod 42899271839561) ^ 19480 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_49718679039509 : Nat.Prime 49718679039509 := by
  apply lucas_primality 49718679039509 (2 : ZMod 49718679039509)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (43, 1), (193, 1), (239, 1), (6266657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (43, 1), (193, 1), (239, 1), (6266657, 1)] : List FactorBlock).map factorBlockValue).prod) = 49718679039509 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_43
      · exact prime_oneHundredFiftyFourEV_193
      · exact prime_oneHundredFiftyFourEV_239
      · exact prime_oneHundredFiftyFourEV_6266657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 49718679039509) ^ 24859339519754 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 49718679039509) ^ 1156248349756 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 49718679039509) ^ 257609735956 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 49718679039509) ^ 208027945772 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 49718679039509) ^ 7933844 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_53022278245693 : Nat.Prime 53022278245693 := by
  apply lucas_primality 53022278245693 (2 : ZMod 53022278245693)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (179, 1), (3526355297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (179, 1), (3526355297, 1)] : List FactorBlock).map factorBlockValue).prod) = 53022278245693 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_7
      · exact prime_oneHundredFiftyFourEV_179
      · exact prime_oneHundredFiftyFourEV_3526355297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 53022278245693) ^ 26511139122846 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 53022278245693) ^ 17674092748564 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 53022278245693) ^ 7574611177956 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 53022278245693) ^ 296213844948 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 53022278245693) ^ 15036 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_66139999399751 : Nat.Prime 66139999399751 := by
  apply lucas_primality 66139999399751 (7 : ZMod 66139999399751)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 3), (1321, 1), (200272519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 3), (1321, 1), (200272519, 1)] : List FactorBlock).map factorBlockValue).prod) = 66139999399751 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_5
      · exact prime_oneHundredFiftyFourEV_1321
      · exact prime_oneHundredFiftyFourEV_200272519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 66139999399751) ^ 33069999699875 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (7 : ZMod 66139999399751) ^ 13227999879950 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (7 : ZMod 66139999399751) ^ 50068129750 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (7 : ZMod 66139999399751) ^ 330250 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_77274666225553 : Nat.Prime 77274666225553 := by
  apply lucas_primality 77274666225553 (7 : ZMod 77274666225553)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (491, 1), (3278796089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (491, 1), (3278796089, 1)] : List FactorBlock).map factorBlockValue).prod) = 77274666225553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_491
      · exact prime_oneHundredFiftyFourEV_3278796089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 77274666225553) ^ 38637333112776 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (7 : ZMod 77274666225553) ^ 25758222075184 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (7 : ZMod 77274666225553) ^ 157382212272 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (7 : ZMod 77274666225553) ^ 23568 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_81909131127767 : Nat.Prime 81909131127767 := by
  apply lucas_primality 81909131127767 (5 : ZMod 81909131127767)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (40954565563883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (40954565563883, 1)] : List FactorBlock).map factorBlockValue).prod) = 81909131127767 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_40954565563883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 81909131127767) ^ 40954565563883 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 81909131127767) ^ 2 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_95775768498253 : Nat.Prime 95775768498253 := by
  apply lucas_primality 95775768498253 (2 : ZMod 95775768498253)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (379, 1), (21058876099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (379, 1), (21058876099, 1)] : List FactorBlock).map factorBlockValue).prod) = 95775768498253 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_379
      · exact prime_oneHundredFiftyFourEV_21058876099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 95775768498253) ^ 47887884249126 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 95775768498253) ^ 31925256166084 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 95775768498253) ^ 252706513188 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 95775768498253) ^ 4548 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_100121730683839 : Nat.Prime 100121730683839 := by
  apply lucas_primality 100121730683839 (3 : ZMod 100121730683839)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (463, 1), (100769, 1), (357659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (463, 1), (100769, 1), (357659, 1)] : List FactorBlock).map factorBlockValue).prod) = 100121730683839 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_463
      · exact prime_oneHundredFiftyFourEV_100769
      · exact prime_oneHundredFiftyFourEV_357659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 100121730683839) ^ 50060865341919 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 100121730683839) ^ 33373910227946 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 100121730683839) ^ 216245638626 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 100121730683839) ^ 993576702 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 100121730683839) ^ 279936282 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_141087634660187 : Nat.Prime 141087634660187 := by
  apply lucas_primality 141087634660187 (2 : ZMod 141087634660187)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (149, 1), (1493, 1), (1579, 1), (4273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (149, 1), (1493, 1), (1579, 1), (4273, 1)] : List FactorBlock).map factorBlockValue).prod) = 141087634660187 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_47
      · exact prime_oneHundredFiftyFourEV_149
      · exact prime_oneHundredFiftyFourEV_1493
      · exact prime_oneHundredFiftyFourEV_1579
      · exact prime_oneHundredFiftyFourEV_4273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 141087634660187) ^ 70543817330093 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 141087634660187) ^ 3001864567238 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 141087634660187) ^ 946896876914 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 141087634660187) ^ 94499420402 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 141087634660187) ^ 89352523534 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 141087634660187) ^ 33018402682 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_145043184037397 : Nat.Prime 145043184037397 := by
  apply lucas_primality 145043184037397 (2 : ZMod 145043184037397)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (163, 1), (229949, 1), (967427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (163, 1), (229949, 1), (967427, 1)] : List FactorBlock).map factorBlockValue).prod) = 145043184037397 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_163
      · exact prime_oneHundredFiftyFourEV_229949
      · exact prime_oneHundredFiftyFourEV_967427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 145043184037397) ^ 72521592018698 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 145043184037397) ^ 889835484892 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 145043184037397) ^ 630762404 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 145043184037397) ^ 149926748 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_145561541879123 : Nat.Prime 145561541879123 := by
  apply lucas_primality 145561541879123 (2 : ZMod 145561541879123)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3671, 1), (52879, 1), (374929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3671, 1), (52879, 1), (374929, 1)] : List FactorBlock).map factorBlockValue).prod) = 145561541879123 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3671
      · exact prime_oneHundredFiftyFourEV_52879
      · exact prime_oneHundredFiftyFourEV_374929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 145561541879123) ^ 72780770939561 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 145561541879123) ^ 39651741182 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 145561541879123) ^ 2752728718 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 145561541879123) ^ 388237618 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_163383528046723 : Nat.Prime 163383528046723 := by
  apply lucas_primality 163383528046723 (5 : ZMod 163383528046723)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (27230588007787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (27230588007787, 1)] : List FactorBlock).map factorBlockValue).prod) = 163383528046723 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_27230588007787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 163383528046723) ^ 81691764023361 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 163383528046723) ^ 54461176015574 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 163383528046723) ^ 6 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_170506772610893 : Nat.Prime 170506772610893 := by
  apply lucas_primality 170506772610893 (2 : ZMod 170506772610893)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (1831, 1), (1012197971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (1831, 1), (1012197971, 1)] : List FactorBlock).map factorBlockValue).prod) = 170506772610893 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_23
      · exact prime_oneHundredFiftyFourEV_1831
      · exact prime_oneHundredFiftyFourEV_1012197971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 170506772610893) ^ 85253386305446 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 170506772610893) ^ 7413337939604 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 170506772610893) ^ 93122213332 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 170506772610893) ^ 168452 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_171536160021871 : Nat.Prime 171536160021871 := by
  apply lucas_primality 171536160021871 (6 : ZMod 171536160021871)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 2), (70207, 1), (1662103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 2), (70207, 1), (1662103, 1)] : List FactorBlock).map factorBlockValue).prod) = 171536160021871 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_5
      · exact prime_oneHundredFiftyFourEV_7
      · exact prime_oneHundredFiftyFourEV_70207
      · exact prime_oneHundredFiftyFourEV_1662103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 171536160021871) ^ 85768080010935 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (6 : ZMod 171536160021871) ^ 57178720007290 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (6 : ZMod 171536160021871) ^ 34307232004374 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (6 : ZMod 171536160021871) ^ 24505165717410 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (6 : ZMod 171536160021871) ^ 2443291410 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (6 : ZMod 171536160021871) ^ 103204290 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_174841368000787 : Nat.Prime 174841368000787 := by
  apply lucas_primality 174841368000787 (2 : ZMod 174841368000787)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (2579, 1), (3766347163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (2579, 1), (3766347163, 1)] : List FactorBlock).map factorBlockValue).prod) = 174841368000787 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_2579
      · exact prime_oneHundredFiftyFourEV_3766347163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 174841368000787) ^ 87420684000393 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 174841368000787) ^ 58280456000262 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 174841368000787) ^ 67794248934 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 174841368000787) ^ 46422 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_240339789298547 : Nat.Prime 240339789298547 := by
  apply lucas_primality 240339789298547 (2 : ZMod 240339789298547)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (73, 1), (33595162049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (73, 1), (33595162049, 1)] : List FactorBlock).map factorBlockValue).prod) = 240339789298547 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_7
      · exact prime_oneHundredFiftyFourEV_73
      · exact prime_oneHundredFiftyFourEV_33595162049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 240339789298547) ^ 120169894649273 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 240339789298547) ^ 34334255614078 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 240339789298547) ^ 3292325880802 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 240339789298547) ^ 7154 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_282940467043753 : Nat.Prime 282940467043753 := by
  apply lucas_primality 282940467043753 (11 : ZMod 282940467043753)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (7, 1), (53, 1), (79, 1), (44693083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (7, 1), (53, 1), (79, 1), (44693083, 1)] : List FactorBlock).map factorBlockValue).prod) = 282940467043753 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_7
      · exact prime_oneHundredFiftyFourEV_53
      · exact prime_oneHundredFiftyFourEV_79
      · exact prime_oneHundredFiftyFourEV_44693083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 282940467043753) ^ 141470233521876 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (11 : ZMod 282940467043753) ^ 94313489014584 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (11 : ZMod 282940467043753) ^ 40420066720536 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (11 : ZMod 282940467043753) ^ 5338499378184 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (11 : ZMod 282940467043753) ^ 3581524899288 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (11 : ZMod 282940467043753) ^ 6330744 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_481886308435871 : Nat.Prime 481886308435871 := by
  apply lucas_primality 481886308435871 (11 : ZMod 481886308435871)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (53, 1), (857, 1), (81610219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (53, 1), (857, 1), (81610219, 1)] : List FactorBlock).map factorBlockValue).prod) = 481886308435871 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_5
      · exact prime_oneHundredFiftyFourEV_13
      · exact prime_oneHundredFiftyFourEV_53
      · exact prime_oneHundredFiftyFourEV_857
      · exact prime_oneHundredFiftyFourEV_81610219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 481886308435871) ^ 240943154217935 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (11 : ZMod 481886308435871) ^ 96377261687174 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (11 : ZMod 481886308435871) ^ 37068177571990 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (11 : ZMod 481886308435871) ^ 9092194498790 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (11 : ZMod 481886308435871) ^ 562294408910 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (11 : ZMod 481886308435871) ^ 5904730 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_605401060944023 : Nat.Prime 605401060944023 := by
  apply lucas_primality 605401060944023 (5 : ZMod 605401060944023)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (701, 1), (9769, 1), (6314617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (701, 1), (9769, 1), (6314617, 1)] : List FactorBlock).map factorBlockValue).prod) = 605401060944023 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_7
      · exact prime_oneHundredFiftyFourEV_701
      · exact prime_oneHundredFiftyFourEV_9769
      · exact prime_oneHundredFiftyFourEV_6314617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 605401060944023) ^ 302700530472011 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 605401060944023) ^ 86485865849146 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 605401060944023) ^ 863624908622 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 605401060944023) ^ 61971651238 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 605401060944023) ^ 95872966 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_808371479548991 : Nat.Prime 808371479548991 := by
  apply lucas_primality 808371479548991 (7 : ZMod 808371479548991)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (31, 1), (73, 1), (89, 1), (757, 1), (75743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (31, 1), (73, 1), (89, 1), (757, 1), (75743, 1)] : List FactorBlock).map factorBlockValue).prod) = 808371479548991 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_5
      · exact prime_oneHundredFiftyFourEV_7
      · exact prime_oneHundredFiftyFourEV_31
      · exact prime_oneHundredFiftyFourEV_73
      · exact prime_oneHundredFiftyFourEV_89
      · exact prime_oneHundredFiftyFourEV_757
      · exact prime_oneHundredFiftyFourEV_75743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 808371479548991) ^ 404185739774495 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (7 : ZMod 808371479548991) ^ 161674295909798 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (7 : ZMod 808371479548991) ^ 115481639935570 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (7 : ZMod 808371479548991) ^ 26076499340290 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (7 : ZMod 808371479548991) ^ 11073581911630 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (7 : ZMod 808371479548991) ^ 9082825612910 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (7 : ZMod 808371479548991) ^ 1067861928070 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (7 : ZMod 808371479548991) ^ 10672556930 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_998188812141893 : Nat.Prime 998188812141893 := by
  apply lucas_primality 998188812141893 (2 : ZMod 998188812141893)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (758111, 1), (47024249, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (758111, 1), (47024249, 1)] : List FactorBlock).map factorBlockValue).prod) = 998188812141893 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_7
      · exact prime_oneHundredFiftyFourEV_758111
      · exact prime_oneHundredFiftyFourEV_47024249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 998188812141893) ^ 499094406070946 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 998188812141893) ^ 142598401734556 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 998188812141893) ^ 1316678972 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 998188812141893) ^ 21227108 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_1088521762147013 : Nat.Prime 1088521762147013 := by
  apply lucas_primality 1088521762147013 (2 : ZMod 1088521762147013)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (53, 1), (5134536613901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (53, 1), (5134536613901, 1)] : List FactorBlock).map factorBlockValue).prod) = 1088521762147013 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_53
      · exact prime_oneHundredFiftyFourEV_5134536613901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1088521762147013) ^ 544260881073506 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1088521762147013) ^ 20538146455604 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1088521762147013) ^ 212 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_1640799851181937 : Nat.Prime 1640799851181937 := by
  apply lucas_primality 1640799851181937 (11 : ZMod 1640799851181937)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (23, 1), (1486231749259, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (23, 1), (1486231749259, 1)] : List FactorBlock).map factorBlockValue).prod) = 1640799851181937 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_23
      · exact prime_oneHundredFiftyFourEV_1486231749259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 1640799851181937) ^ 820399925590968 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (11 : ZMod 1640799851181937) ^ 546933283727312 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (11 : ZMod 1640799851181937) ^ 71339123964432 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (11 : ZMod 1640799851181937) ^ 1104 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_2145847865892989 : Nat.Prime 2145847865892989 := by
  apply lucas_primality 2145847865892989 (2 : ZMod 2145847865892989)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (101, 1), (16573, 1), (320491439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (101, 1), (16573, 1), (320491439, 1)] : List FactorBlock).map factorBlockValue).prod) = 2145847865892989 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_101
      · exact prime_oneHundredFiftyFourEV_16573
      · exact prime_oneHundredFiftyFourEV_320491439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2145847865892989) ^ 1072923932946494 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2145847865892989) ^ 21246018474188 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2145847865892989) ^ 129478541356 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2145847865892989) ^ 6695492 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_2345758929978757 : Nat.Prime 2345758929978757 := by
  apply lucas_primality 2345758929978757 (2 : ZMod 2345758929978757)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (907, 1), (1019, 1), (211505011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (907, 1), (1019, 1), (211505011, 1)] : List FactorBlock).map factorBlockValue).prod) = 2345758929978757 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_907
      · exact prime_oneHundredFiftyFourEV_1019
      · exact prime_oneHundredFiftyFourEV_211505011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2345758929978757) ^ 1172879464989378 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2345758929978757) ^ 781919643326252 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2345758929978757) ^ 2586283274508 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2345758929978757) ^ 2302020539724 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2345758929978757) ^ 11090796 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_3663748043973649 : Nat.Prime 3663748043973649 := by
  apply lucas_primality 3663748043973649 (19 : ZMod 3663748043973649)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 5), (8741, 1), (107804831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 5), (8741, 1), (107804831, 1)] : List FactorBlock).map factorBlockValue).prod) = 3663748043973649 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_8741
      · exact prime_oneHundredFiftyFourEV_107804831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 3663748043973649) ^ 1831874021986824 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (19 : ZMod 3663748043973649) ^ 1221249347991216 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (19 : ZMod 3663748043973649) ^ 419145182928 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (19 : ZMod 3663748043973649) ^ 33985008 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_3695141951608433 : Nat.Prime 3695141951608433 := by
  apply lucas_primality 3695141951608433 (3 : ZMod 3695141951608433)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (13, 1), (17765105536579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (13, 1), (17765105536579, 1)] : List FactorBlock).map factorBlockValue).prod) = 3695141951608433 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_13
      · exact prime_oneHundredFiftyFourEV_17765105536579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 3695141951608433) ^ 1847570975804216 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 3695141951608433) ^ 284241688585264 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 3695141951608433) ^ 208 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_6982819718723939 : Nat.Prime 6982819718723939 := by
  apply lucas_primality 6982819718723939 (2 : ZMod 6982819718723939)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (79, 1), (1583, 1), (27918548017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (79, 1), (1583, 1), (27918548017, 1)] : List FactorBlock).map factorBlockValue).prod) = 6982819718723939 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_79
      · exact prime_oneHundredFiftyFourEV_1583
      · exact prime_oneHundredFiftyFourEV_27918548017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 6982819718723939) ^ 3491409859361969 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 6982819718723939) ^ 88390123021822 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 6982819718723939) ^ 4411130586686 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 6982819718723939) ^ 250114 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_7446823087884163 : Nat.Prime 7446823087884163 := by
  apply lucas_primality 7446823087884163 (3 : ZMod 7446823087884163)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (63337, 1), (19595768371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (63337, 1), (19595768371, 1)] : List FactorBlock).map factorBlockValue).prod) = 7446823087884163 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_63337
      · exact prime_oneHundredFiftyFourEV_19595768371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 7446823087884163) ^ 3723411543942081 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 7446823087884163) ^ 2482274362628054 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 7446823087884163) ^ 117574610226 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 7446823087884163) ^ 380022 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_12778610572777171 : Nat.Prime 12778610572777171 := by
  apply lucas_primality 12778610572777171 (2 : ZMod 12778610572777171)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (23, 1), (101, 1), (16669419863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (23, 1), (101, 1), (16669419863, 1)] : List FactorBlock).map factorBlockValue).prod) = 12778610572777171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_5
      · exact prime_oneHundredFiftyFourEV_11
      · exact prime_oneHundredFiftyFourEV_23
      · exact prime_oneHundredFiftyFourEV_101
      · exact prime_oneHundredFiftyFourEV_16669419863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 12778610572777171) ^ 6389305286388585 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 12778610572777171) ^ 4259536857592390 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 12778610572777171) ^ 2555722114555434 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 12778610572777171) ^ 1161691870252470 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 12778610572777171) ^ 555591764033790 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 12778610572777171) ^ 126520896760170 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 12778610572777171) ^ 766590 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_13901183530423523 : Nat.Prime 13901183530423523 := by
  apply lucas_primality 13901183530423523 (2 : ZMod 13901183530423523)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (12767897, 1), (544380313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (12767897, 1), (544380313, 1)] : List FactorBlock).map factorBlockValue).prod) = 13901183530423523 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_12767897
      · exact prime_oneHundredFiftyFourEV_544380313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 13901183530423523) ^ 6950591765211761 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 13901183530423523) ^ 1088760626 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 13901183530423523) ^ 25535794 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_16695774487261171 : Nat.Prime 16695774487261171 := by
  apply lucas_primality 16695774487261171 (3 : ZMod 16695774487261171)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (7, 1), (97, 1), (167, 1), (545326447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (7, 1), (97, 1), (167, 1), (545326447, 1)] : List FactorBlock).map factorBlockValue).prod) = 16695774487261171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_5
      · exact prime_oneHundredFiftyFourEV_7
      · exact prime_oneHundredFiftyFourEV_97
      · exact prime_oneHundredFiftyFourEV_167
      · exact prime_oneHundredFiftyFourEV_545326447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 16695774487261171) ^ 8347887243630585 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 16695774487261171) ^ 5565258162420390 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 16695774487261171) ^ 3339154897452234 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 16695774487261171) ^ 2385110641037310 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 16695774487261171) ^ 172121386466610 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 16695774487261171) ^ 99974697528510 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 16695774487261171) ^ 30616110 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_16884820210972061 : Nat.Prime 16884820210972061 := by
  apply lucas_primality 16884820210972061 (2 : ZMod 16884820210972061)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (331603, 1), (2545939001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (331603, 1), (2545939001, 1)] : List FactorBlock).map factorBlockValue).prod) = 16884820210972061 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_5
      · exact prime_oneHundredFiftyFourEV_331603
      · exact prime_oneHundredFiftyFourEV_2545939001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 16884820210972061) ^ 8442410105486030 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 16884820210972061) ^ 3376964042194412 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 16884820210972061) ^ 50918780020 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 16884820210972061) ^ 6632060 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_17231294836313119 : Nat.Prime 17231294836313119 := by
  apply lucas_primality 17231294836313119 (3 : ZMod 17231294836313119)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (11, 1), (17, 1), (137, 1), (12455523343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (11, 1), (17, 1), (137, 1), (12455523343, 1)] : List FactorBlock).map factorBlockValue).prod) = 17231294836313119 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_11
      · exact prime_oneHundredFiftyFourEV_17
      · exact prime_oneHundredFiftyFourEV_137
      · exact prime_oneHundredFiftyFourEV_12455523343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 17231294836313119) ^ 8615647418156559 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 17231294836313119) ^ 5743764945437706 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 17231294836313119) ^ 1566481348755738 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 17231294836313119) ^ 1013605578606654 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 17231294836313119) ^ 125775874717614 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 17231294836313119) ^ 1383426 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_23935384454729591 : Nat.Prime 23935384454729591 := by
  apply lucas_primality 23935384454729591 (7 : ZMod 23935384454729591)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1663, 1), (26399, 1), (54520607, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1663, 1), (26399, 1), (54520607, 1)] : List FactorBlock).map factorBlockValue).prod) = 23935384454729591 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_5
      · exact prime_oneHundredFiftyFourEV_1663
      · exact prime_oneHundredFiftyFourEV_26399
      · exact prime_oneHundredFiftyFourEV_54520607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 23935384454729591) ^ 11967692227364795 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (7 : ZMod 23935384454729591) ^ 4787076890945918 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (7 : ZMod 23935384454729591) ^ 14392895041930 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (7 : ZMod 23935384454729591) ^ 906677694410 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (7 : ZMod 23935384454729591) ^ 439015370 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_28294900080643093 : Nat.Prime 28294900080643093 := by
  apply lucas_primality 28294900080643093 (2 : ZMod 28294900080643093)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (19, 1), (29, 1), (110083, 1), (2990279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (19, 1), (29, 1), (110083, 1), (2990279, 1)] : List FactorBlock).map factorBlockValue).prod) = 28294900080643093 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_13
      · exact prime_oneHundredFiftyFourEV_19
      · exact prime_oneHundredFiftyFourEV_29
      · exact prime_oneHundredFiftyFourEV_110083
      · exact prime_oneHundredFiftyFourEV_2990279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 28294900080643093) ^ 14147450040321546 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 28294900080643093) ^ 9431633360214364 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 28294900080643093) ^ 2176530775434084 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 28294900080643093) ^ 1489205267402268 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 28294900080643093) ^ 975686209677348 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 28294900080643093) ^ 257032421724 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 28294900080643093) ^ 9462294348 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_29787292351536653 : Nat.Prime 29787292351536653 := by
  apply lucas_primality 29787292351536653 (2 : ZMod 29787292351536653)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7446823087884163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7446823087884163, 1)] : List FactorBlock).map factorBlockValue).prod) = 29787292351536653 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_7446823087884163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 29787292351536653) ^ 14893646175768326 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 29787292351536653) ^ 4 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_30084753901930547 : Nat.Prime 30084753901930547 := by
  apply lucas_primality 30084753901930547 (7 : ZMod 30084753901930547)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (13, 1), (73, 1), (179, 1), (349, 1), (5178163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (13, 1), (73, 1), (179, 1), (349, 1), (5178163, 1)] : List FactorBlock).map factorBlockValue).prod) = 30084753901930547 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_7
      · exact prime_oneHundredFiftyFourEV_13
      · exact prime_oneHundredFiftyFourEV_73
      · exact prime_oneHundredFiftyFourEV_179
      · exact prime_oneHundredFiftyFourEV_349
      · exact prime_oneHundredFiftyFourEV_5178163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 30084753901930547) ^ 15042376950965273 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (7 : ZMod 30084753901930547) ^ 4297821985990078 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (7 : ZMod 30084753901930547) ^ 2314211838610042 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (7 : ZMod 30084753901930547) ^ 412119916464802 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (7 : ZMod 30084753901930547) ^ 168071250848774 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (7 : ZMod 30084753901930547) ^ 86202733243354 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (7 : ZMod 30084753901930547) ^ 5809927942 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_47870768909459183 : Nat.Prime 47870768909459183 := by
  apply lucas_primality 47870768909459183 (5 : ZMod 47870768909459183)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23935384454729591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23935384454729591, 1)] : List FactorBlock).map factorBlockValue).prod) = 47870768909459183 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_23935384454729591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 47870768909459183) ^ 23935384454729591 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 47870768909459183) ^ 2 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_53241274286720537 : Nat.Prime 53241274286720537 := by
  apply lucas_primality 53241274286720537 (3 : ZMod 53241274286720537)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (145829, 1), (45636734023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (145829, 1), (45636734023, 1)] : List FactorBlock).map factorBlockValue).prod) = 53241274286720537 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_145829
      · exact prime_oneHundredFiftyFourEV_45636734023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 53241274286720537) ^ 26620637143360268 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 53241274286720537) ^ 365093872184 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 53241274286720537) ^ 1166632 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_75661240059006293 : Nat.Prime 75661240059006293 := by
  apply lucas_primality 75661240059006293 (2 : ZMod 75661240059006293)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (849103, 1), (22276814491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (849103, 1), (22276814491, 1)] : List FactorBlock).map factorBlockValue).prod) = 75661240059006293 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_849103
      · exact prime_oneHundredFiftyFourEV_22276814491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 75661240059006293) ^ 37830620029503146 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 75661240059006293) ^ 89107257964 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 75661240059006293) ^ 3396412 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_78511797954027271 : Nat.Prime 78511797954027271 := by
  apply lucas_primality 78511797954027271 (3 : ZMod 78511797954027271)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 1), (3457, 1), (8263, 1), (4362719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 1), (3457, 1), (8263, 1), (4362719, 1)] : List FactorBlock).map factorBlockValue).prod) = 78511797954027271 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_5
      · exact prime_oneHundredFiftyFourEV_7
      · exact prime_oneHundredFiftyFourEV_3457
      · exact prime_oneHundredFiftyFourEV_8263
      · exact prime_oneHundredFiftyFourEV_4362719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 78511797954027271) ^ 39255898977013635 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 78511797954027271) ^ 26170599318009090 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 78511797954027271) ^ 15702359590805454 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 78511797954027271) ^ 11215971136289610 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 78511797954027271) ^ 22710962671110 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 78511797954027271) ^ 9501609337290 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 78511797954027271) ^ 17996070330 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_114838352397056749 : Nat.Prime 114838352397056749 := by
  apply lucas_primality 114838352397056749 (6 : ZMod 114838352397056749)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (346111, 1), (27649692439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (346111, 1), (27649692439, 1)] : List FactorBlock).map factorBlockValue).prod) = 114838352397056749 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_346111
      · exact prime_oneHundredFiftyFourEV_27649692439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 114838352397056749) ^ 57419176198528374 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (6 : ZMod 114838352397056749) ^ 38279450799018916 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (6 : ZMod 114838352397056749) ^ 331796309268 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (6 : ZMod 114838352397056749) ^ 4153332 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_117929653649192977 : Nat.Prime 117929653649192977 := by
  apply lucas_primality 117929653649192977 (5 : ZMod 117929653649192977)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (17, 1), (211, 1), (701, 1), (977085101, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (17, 1), (211, 1), (701, 1), (977085101, 1)] : List FactorBlock).map factorBlockValue).prod) = 117929653649192977 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_17
      · exact prime_oneHundredFiftyFourEV_211
      · exact prime_oneHundredFiftyFourEV_701
      · exact prime_oneHundredFiftyFourEV_977085101
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 117929653649192977) ^ 58964826824596488 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 117929653649192977) ^ 39309884549730992 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 117929653649192977) ^ 6937038449952528 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 117929653649192977) ^ 558908311133616 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 117929653649192977) ^ 168230604349776 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 117929653649192977) ^ 120695376 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_167315665732025891 : Nat.Prime 167315665732025891 := by
  apply lucas_primality 167315665732025891 (2 : ZMod 167315665732025891)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (2347, 1), (7128916307287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (2347, 1), (7128916307287, 1)] : List FactorBlock).map factorBlockValue).prod) = 167315665732025891 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_5
      · exact prime_oneHundredFiftyFourEV_2347
      · exact prime_oneHundredFiftyFourEV_7128916307287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 167315665732025891) ^ 83657832866012945 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 167315665732025891) ^ 33463133146405178 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 167315665732025891) ^ 71289163072870 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 167315665732025891) ^ 23470 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_192294350320855543 : Nat.Prime 192294350320855543 := by
  apply lucas_primality 192294350320855543 (3 : ZMod 192294350320855543)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 1), (37, 1), (29868647145209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 1), (37, 1), (29868647145209, 1)] : List FactorBlock).map factorBlockValue).prod) = 192294350320855543 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_29
      · exact prime_oneHundredFiftyFourEV_37
      · exact prime_oneHundredFiftyFourEV_29868647145209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 192294350320855543) ^ 96147175160427771 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 192294350320855543) ^ 64098116773618514 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 192294350320855543) ^ 6630839666236398 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 192294350320855543) ^ 5197144603266366 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 192294350320855543) ^ 6438 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_257138647306974463 : Nat.Prime 257138647306974463 := by
  apply lucas_primality 257138647306974463 (5 : ZMod 257138647306974463)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (229841, 1), (186461254597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (229841, 1), (186461254597, 1)] : List FactorBlock).map factorBlockValue).prod) = 257138647306974463 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_229841
      · exact prime_oneHundredFiftyFourEV_186461254597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 257138647306974463) ^ 128569323653487231 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 257138647306974463) ^ 85712882435658154 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 257138647306974463) ^ 1118767527582 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 257138647306974463) ^ 1379046 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_282912714780561631 : Nat.Prime 282912714780561631 := by
  apply lucas_primality 282912714780561631 (6 : ZMod 282912714780561631)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (59, 1), (1885943, 1), (28250711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (59, 1), (1885943, 1), (28250711, 1)] : List FactorBlock).map factorBlockValue).prod) = 282912714780561631 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_5
      · exact prime_oneHundredFiftyFourEV_59
      · exact prime_oneHundredFiftyFourEV_1885943
      · exact prime_oneHundredFiftyFourEV_28250711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 282912714780561631) ^ 141456357390280815 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (6 : ZMod 282912714780561631) ^ 94304238260187210 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (6 : ZMod 282912714780561631) ^ 56582542956112326 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (6 : ZMod 282912714780561631) ^ 4795130758992570 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (6 : ZMod 282912714780561631) ^ 150011275410 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (6 : ZMod 282912714780561631) ^ 10014357330 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_415354498080135349 : Nat.Prime 415354498080135349 := by
  apply lucas_primality 415354498080135349 (2 : ZMod 415354498080135349)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (29, 1), (170506772610893, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (29, 1), (170506772610893, 1)] : List FactorBlock).map factorBlockValue).prod) = 415354498080135349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_7
      · exact prime_oneHundredFiftyFourEV_29
      · exact prime_oneHundredFiftyFourEV_170506772610893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 415354498080135349) ^ 207677249040067674 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 415354498080135349) ^ 138451499360045116 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 415354498080135349) ^ 59336356868590764 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 415354498080135349) ^ 14322568899315012 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 415354498080135349) ^ 2436 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_1033877690178787141 : Nat.Prime 1033877690178787141 := by
  apply lucas_primality 1033877690178787141 (10 : ZMod 1033877690178787141)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (17231294836313119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (17231294836313119, 1)] : List FactorBlock).map factorBlockValue).prod) = 1033877690178787141 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_5
      · exact prime_oneHundredFiftyFourEV_17231294836313119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 1033877690178787141) ^ 516938845089393570 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (10 : ZMod 1033877690178787141) ^ 344625896726262380 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (10 : ZMod 1033877690178787141) ^ 206775538035757428 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (10 : ZMod 1033877690178787141) ^ 60 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_1109188763774599357 : Nat.Prime 1109188763774599357 := by
  apply lucas_primality 1109188763774599357 (5 : ZMod 1109188763774599357)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (59, 1), (89, 1), (199, 1), (29485457179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (59, 1), (89, 1), (199, 1), (29485457179, 1)] : List FactorBlock).map factorBlockValue).prod) = 1109188763774599357 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_59
      · exact prime_oneHundredFiftyFourEV_89
      · exact prime_oneHundredFiftyFourEV_199
      · exact prime_oneHundredFiftyFourEV_29485457179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1109188763774599357) ^ 554594381887299678 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 1109188763774599357) ^ 369729587924866452 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 1109188763774599357) ^ 18799809555501684 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 1109188763774599357) ^ 12462795098591004 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 1109188763774599357) ^ 5573812883289444 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 1109188763774599357) ^ 37618164 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_1145182462382728073 : Nat.Prime 1145182462382728073 := by
  apply lucas_primality 1145182462382728073 (3 : ZMod 1145182462382728073)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (103549, 1), (1382416129541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (103549, 1), (1382416129541, 1)] : List FactorBlock).map factorBlockValue).prod) = 1145182462382728073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_103549
      · exact prime_oneHundredFiftyFourEV_1382416129541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1145182462382728073) ^ 572591231191364036 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1145182462382728073) ^ 11059329036328 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1145182462382728073) ^ 828392 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_1480853278075581127 : Nat.Prime 1480853278075581127 := by
  apply lucas_primality 1480853278075581127 (3 : ZMod 1480853278075581127)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (389, 1), (797, 1), (265357644379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (389, 1), (797, 1), (265357644379, 1)] : List FactorBlock).map factorBlockValue).prod) = 1480853278075581127 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_389
      · exact prime_oneHundredFiftyFourEV_797
      · exact prime_oneHundredFiftyFourEV_265357644379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1480853278075581127) ^ 740426639037790563 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1480853278075581127) ^ 493617759358527042 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1480853278075581127) ^ 3806820766261134 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1480853278075581127) ^ 1858034225941758 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1480853278075581127) ^ 5580594 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_1803256681820524691 : Nat.Prime 1803256681820524691 := by
  apply lucas_primality 1803256681820524691 (2 : ZMod 1803256681820524691)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (2819, 1), (6829, 1), (15569, 1), (601651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (2819, 1), (6829, 1), (15569, 1), (601651, 1)] : List FactorBlock).map factorBlockValue).prod) = 1803256681820524691 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_5
      · exact prime_oneHundredFiftyFourEV_2819
      · exact prime_oneHundredFiftyFourEV_6829
      · exact prime_oneHundredFiftyFourEV_15569
      · exact prime_oneHundredFiftyFourEV_601651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1803256681820524691) ^ 901628340910262345 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1803256681820524691) ^ 360651336364104938 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1803256681820524691) ^ 639679560773510 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1803256681820524691) ^ 264058673571610 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1803256681820524691) ^ 115823539201010 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1803256681820524691) ^ 2997180561190 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_2220502305087140441 : Nat.Prime 2220502305087140441 := by
  apply lucas_primality 2220502305087140441 (3 : ZMod 2220502305087140441)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (101, 1), (191, 1), (48017, 1), (59929613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (101, 1), (191, 1), (48017, 1), (59929613, 1)] : List FactorBlock).map factorBlockValue).prod) = 2220502305087140441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_5
      · exact prime_oneHundredFiftyFourEV_101
      · exact prime_oneHundredFiftyFourEV_191
      · exact prime_oneHundredFiftyFourEV_48017
      · exact prime_oneHundredFiftyFourEV_59929613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2220502305087140441) ^ 1110251152543570220 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 444100461017428088 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 21985171337496440 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 11625666518780840 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 46244086575320 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 37051837880 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_2998253676898342043 : Nat.Prime 2998253676898342043 := by
  apply lucas_primality 2998253676898342043 (2 : ZMod 2998253676898342043)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3229, 1), (4703, 1), (7213, 1), (13686091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3229, 1), (4703, 1), (7213, 1), (13686091, 1)] : List FactorBlock).map factorBlockValue).prod) = 2998253676898342043 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3229
      · exact prime_oneHundredFiftyFourEV_4703
      · exact prime_oneHundredFiftyFourEV_7213
      · exact prime_oneHundredFiftyFourEV_13686091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2998253676898342043) ^ 1499126838449171021 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2998253676898342043) ^ 928539385846498 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2998253676898342043) ^ 637519386965414 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2998253676898342043) ^ 415673600013634 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2998253676898342043) ^ 219073048462 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_3155426499202294903 : Nat.Prime 3155426499202294903 := by
  apply lucas_primality 3155426499202294903 (10 : ZMod 3155426499202294903)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (53, 1), (1367, 1), (220217, 1), (2535527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (53, 1), (1367, 1), (220217, 1), (2535527, 1)] : List FactorBlock).map factorBlockValue).prod) = 3155426499202294903 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_13
      · exact prime_oneHundredFiftyFourEV_53
      · exact prime_oneHundredFiftyFourEV_1367
      · exact prime_oneHundredFiftyFourEV_220217
      · exact prime_oneHundredFiftyFourEV_2535527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 3155426499202294903) ^ 1577713249601147451 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (10 : ZMod 3155426499202294903) ^ 1051808833067431634 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (10 : ZMod 3155426499202294903) ^ 242725115323253454 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (10 : ZMod 3155426499202294903) ^ 59536349041552734 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (10 : ZMod 3155426499202294903) ^ 2308285661450106 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (10 : ZMod 3155426499202294903) ^ 14328714400806 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (10 : ZMod 3155426499202294903) ^ 1244485465626 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_3873419681044591673 : Nat.Prime 3873419681044591673 := by
  apply lucas_primality 3873419681044591673 (3 : ZMod 3873419681044591673)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (29, 1), (16695774487261171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (29, 1), (16695774487261171, 1)] : List FactorBlock).map factorBlockValue).prod) = 3873419681044591673 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_29
      · exact prime_oneHundredFiftyFourEV_16695774487261171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 3873419681044591673) ^ 1936709840522295836 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 3873419681044591673) ^ 133566195898089368 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 3873419681044591673) ^ 232 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_5226452675632017703 : Nat.Prime 5226452675632017703 := by
  apply lucas_primality 5226452675632017703 (6 : ZMod 5226452675632017703)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (19, 1), (43, 1), (6501791, 1), (54661237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (19, 1), (43, 1), (6501791, 1), (54661237, 1)] : List FactorBlock).map factorBlockValue).prod) = 5226452675632017703 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_19
      · exact prime_oneHundredFiftyFourEV_43
      · exact prime_oneHundredFiftyFourEV_6501791
      · exact prime_oneHundredFiftyFourEV_54661237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 5226452675632017703) ^ 2613226337816008851 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (6 : ZMod 5226452675632017703) ^ 1742150891877339234 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (6 : ZMod 5226452675632017703) ^ 275076456612211458 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (6 : ZMod 5226452675632017703) ^ 121545411061209714 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (6 : ZMod 5226452675632017703) ^ 803848151322 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (6 : ZMod 5226452675632017703) ^ 95615338446 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_7235835567010375067 : Nat.Prime 7235835567010375067 := by
  apply lucas_primality 7235835567010375067 (2 : ZMod 7235835567010375067)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (1161233, 1), (63583326349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (1161233, 1), (63583326349, 1)] : List FactorBlock).map factorBlockValue).prod) = 7235835567010375067 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_7
      · exact prime_oneHundredFiftyFourEV_1161233
      · exact prime_oneHundredFiftyFourEV_63583326349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7235835567010375067) ^ 3617917783505187533 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 7235835567010375067) ^ 1033690795287196438 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 7235835567010375067) ^ 6231165982202 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 7235835567010375067) ^ 113800834 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_12416585925872501761 : Nat.Prime 12416585925872501761 := by
  apply lucas_primality 12416585925872501761 (7 : ZMod 12416585925872501761)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 10), (3, 1), (5, 1), (808371479548991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 10), (3, 1), (5, 1), (808371479548991, 1)] : List FactorBlock).map factorBlockValue).prod) = 12416585925872501761 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_5
      · exact prime_oneHundredFiftyFourEV_808371479548991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 12416585925872501761) ^ 6208292962936250880 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (7 : ZMod 12416585925872501761) ^ 4138861975290833920 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (7 : ZMod 12416585925872501761) ^ 2483317185174500352 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (7 : ZMod 12416585925872501761) ^ 15360 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_14808532780755811271 : Nat.Prime 14808532780755811271 := by
  apply lucas_primality 14808532780755811271 (11 : ZMod 14808532780755811271)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1480853278075581127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1480853278075581127, 1)] : List FactorBlock).map factorBlockValue).prod) = 14808532780755811271 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_5
      · exact prime_oneHundredFiftyFourEV_1480853278075581127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 14808532780755811271) ^ 7404266390377905635 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (11 : ZMod 14808532780755811271) ^ 2961706556151162254 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (11 : ZMod 14808532780755811271) ^ 10 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_15555579548064620611 : Nat.Prime 15555579548064620611 := by
  apply lucas_primality 15555579548064620611 (3 : ZMod 15555579548064620611)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (13, 1), (277, 1), (907, 1), (13859, 1), (1636457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (13, 1), (277, 1), (907, 1), (13859, 1), (1636457, 1)] : List FactorBlock).map factorBlockValue).prod) = 15555579548064620611 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_5
      · exact prime_oneHundredFiftyFourEV_7
      · exact prime_oneHundredFiftyFourEV_13
      · exact prime_oneHundredFiftyFourEV_277
      · exact prime_oneHundredFiftyFourEV_907
      · exact prime_oneHundredFiftyFourEV_13859
      · exact prime_oneHundredFiftyFourEV_1636457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 15555579548064620611) ^ 7777789774032310305 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 15555579548064620611) ^ 5185193182688206870 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 15555579548064620611) ^ 3111115909612924122 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 15555579548064620611) ^ 2222225649723517230 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 15555579548064620611) ^ 1196583042158816970 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 15555579548064620611) ^ 56157326888319930 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 15555579548064620611) ^ 17150583845716230 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 15555579548064620611) ^ 1122417169208790 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 15555579548064620611) ^ 9505645151730 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_24491996416947912211 : Nat.Prime 24491996416947912211 := by
  apply lucas_primality 24491996416947912211 (22 : ZMod 24491996416947912211)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (5, 1), (37, 1), (43, 1), (19005048782851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (5, 1), (37, 1), (43, 1), (19005048782851, 1)] : List FactorBlock).map factorBlockValue).prod) = 24491996416947912211 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_5
      · exact prime_oneHundredFiftyFourEV_37
      · exact prime_oneHundredFiftyFourEV_43
      · exact prime_oneHundredFiftyFourEV_19005048782851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (22 : ZMod 24491996416947912211) ^ 12245998208473956105 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (22 : ZMod 24491996416947912211) ^ 8163998805649304070 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (22 : ZMod 24491996416947912211) ^ 4898399283389582442 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (22 : ZMod 24491996416947912211) ^ 661945849106700330 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (22 : ZMod 24491996416947912211) ^ 569581312022044470 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (22 : ZMod 24491996416947912211) ^ 1288710 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_30964703946074612927 : Nat.Prime 30964703946074612927 := by
  apply lucas_primality 30964703946074612927 (5 : ZMod 30964703946074612927)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (19417, 1), (1024669, 1), (21031463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (19417, 1), (1024669, 1), (21031463, 1)] : List FactorBlock).map factorBlockValue).prod) = 30964703946074612927 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_37
      · exact prime_oneHundredFiftyFourEV_19417
      · exact prime_oneHundredFiftyFourEV_1024669
      · exact prime_oneHundredFiftyFourEV_21031463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 30964703946074612927) ^ 15482351973037306463 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 30964703946074612927) ^ 836883890434448998 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 30964703946074612927) ^ 1594721323895278 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 30964703946074612927) ^ 30219225863254 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 30964703946074612927) ^ 1472303850002 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_31016330705363614231 : Nat.Prime 31016330705363614231 := by
  apply lucas_primality 31016330705363614231 (3 : ZMod 31016330705363614231)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (1033877690178787141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (1033877690178787141, 1)] : List FactorBlock).map factorBlockValue).prod) = 31016330705363614231 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_5
      · exact prime_oneHundredFiftyFourEV_1033877690178787141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 31016330705363614231) ^ 15508165352681807115 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 31016330705363614231) ^ 10338776901787871410 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 31016330705363614231) ^ 6203266141072722846 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 31016330705363614231) ^ 30 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_37054182226033811591 : Nat.Prime 37054182226033811591 := by
  apply lucas_primality 37054182226033811591 (7 : ZMod 37054182226033811591)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (59, 1), (433, 1), (145043184037397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (59, 1), (433, 1), (145043184037397, 1)] : List FactorBlock).map factorBlockValue).prod) = 37054182226033811591 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_5
      · exact prime_oneHundredFiftyFourEV_59
      · exact prime_oneHundredFiftyFourEV_433
      · exact prime_oneHundredFiftyFourEV_145043184037397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 37054182226033811591) ^ 18527091113016905795 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (7 : ZMod 37054182226033811591) ^ 7410836445206762318 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (7 : ZMod 37054182226033811591) ^ 628036986881929010 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (7 : ZMod 37054182226033811591) ^ 85575478582064230 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (7 : ZMod 37054182226033811591) ^ 255470 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_76147770580265129653 : Nat.Prime 76147770580265129653 := by
  apply lucas_primality 76147770580265129653 (2 : ZMod 76147770580265129653)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (138739, 1), (5082002535821, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (138739, 1), (5082002535821, 1)] : List FactorBlock).map factorBlockValue).prod) = 76147770580265129653 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_138739
      · exact prime_oneHundredFiftyFourEV_5082002535821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 76147770580265129653) ^ 38073885290132564826 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 76147770580265129653) ^ 25382590193421709884 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 76147770580265129653) ^ 548856273868668 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 76147770580265129653) ^ 14983812 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_94268036096709849533 : Nat.Prime 94268036096709849533 := by
  apply lucas_primality 94268036096709849533 (2 : ZMod 94268036096709849533)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (23, 1), (263, 1), (16339, 1), (14026408709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (23, 1), (263, 1), (16339, 1), (14026408709, 1)] : List FactorBlock).map factorBlockValue).prod) = 94268036096709849533 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_17
      · exact prime_oneHundredFiftyFourEV_23
      · exact prime_oneHundredFiftyFourEV_263
      · exact prime_oneHundredFiftyFourEV_16339
      · exact prime_oneHundredFiftyFourEV_14026408709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 94268036096709849533) ^ 47134018048354924766 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 94268036096709849533) ^ 5545178593924108796 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 94268036096709849533) ^ 4098610265074341284 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 94268036096709849533) ^ 358433597325892964 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 94268036096709849533) ^ 5769510747090388 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 94268036096709849533) ^ 6720753548 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_107441512121809144421 : Nat.Prime 107441512121809144421 := by
  apply lucas_primality 107441512121809144421 (3 : ZMod 107441512121809144421)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (19, 1), (1233899, 1), (229144217941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (19, 1), (1233899, 1), (229144217941, 1)] : List FactorBlock).map factorBlockValue).prod) = 107441512121809144421 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_5
      · exact prime_oneHundredFiftyFourEV_19
      · exact prime_oneHundredFiftyFourEV_1233899
      · exact prime_oneHundredFiftyFourEV_229144217941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 107441512121809144421) ^ 53720756060904572210 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 107441512121809144421) ^ 21488302424361828884 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 107441512121809144421) ^ 5654816427463639180 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 107441512121809144421) ^ 87074802817580 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 107441512121809144421) ^ 468881620 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_110061440872466385569 : Nat.Prime 110061440872466385569 := by
  apply lucas_primality 110061440872466385569 (6 : ZMod 110061440872466385569)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (7, 1), (739, 1), (4547, 1), (146223704779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (7, 1), (739, 1), (4547, 1), (146223704779, 1)] : List FactorBlock).map factorBlockValue).prod) = 110061440872466385569 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_7
      · exact prime_oneHundredFiftyFourEV_739
      · exact prime_oneHundredFiftyFourEV_4547
      · exact prime_oneHundredFiftyFourEV_146223704779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 110061440872466385569) ^ 55030720436233192784 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (6 : ZMod 110061440872466385569) ^ 15723062981780912224 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (6 : ZMod 110061440872466385569) ^ 148932937581145312 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (6 : ZMod 110061440872466385569) ^ 24205287194296544 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (6 : ZMod 110061440872466385569) ^ 752692192 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_166088134405654531219 : Nat.Prime 166088134405654531219 := by
  apply lucas_primality 166088134405654531219 (2 : ZMod 166088134405654531219)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (157, 1), (587, 1), (100121730683839, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (157, 1), (587, 1), (100121730683839, 1)] : List FactorBlock).map factorBlockValue).prod) = 166088134405654531219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_157
      · exact prime_oneHundredFiftyFourEV_587
      · exact prime_oneHundredFiftyFourEV_100121730683839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 166088134405654531219) ^ 83044067202827265609 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 166088134405654531219) ^ 55362711468551510406 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 166088134405654531219) ^ 1057886206405442874 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 166088134405654531219) ^ 282944010912529014 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 166088134405654531219) ^ 1658862 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_206879940390097086379 : Nat.Prime 206879940390097086379 := by
  apply lucas_primality 206879940390097086379 (3 : ZMod 206879940390097086379)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (23, 1), (53, 1), (1387849, 1), (415934677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (23, 1), (53, 1), (1387849, 1), (415934677, 1)] : List FactorBlock).map factorBlockValue).prod) = 206879940390097086379 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_7
      · exact prime_oneHundredFiftyFourEV_23
      · exact prime_oneHundredFiftyFourEV_53
      · exact prime_oneHundredFiftyFourEV_1387849
      · exact prime_oneHundredFiftyFourEV_415934677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 206879940390097086379) ^ 103439970195048543189 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 206879940390097086379) ^ 68959980130032362126 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 206879940390097086379) ^ 29554277198585298054 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 206879940390097086379) ^ 8994780016960742886 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 206879940390097086379) ^ 3903395101699945026 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 206879940390097086379) ^ 149065165151322 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 206879940390097086379) ^ 497385651714 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_215759507024281950941 : Nat.Prime 215759507024281950941 := by
  apply lucas_primality 215759507024281950941 (2 : ZMod 215759507024281950941)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (233, 1), (983, 1), (6728720156339, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (233, 1), (983, 1), (6728720156339, 1)] : List FactorBlock).map factorBlockValue).prod) = 215759507024281950941 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_5
      · exact prime_oneHundredFiftyFourEV_7
      · exact prime_oneHundredFiftyFourEV_233
      · exact prime_oneHundredFiftyFourEV_983
      · exact prime_oneHundredFiftyFourEV_6728720156339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 215759507024281950941) ^ 107879753512140975470 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 215759507024281950941) ^ 43151901404856390188 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 215759507024281950941) ^ 30822786717754564420 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 215759507024281950941) ^ 926006467915373180 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 215759507024281950941) ^ 219490851499778180 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 215759507024281950941) ^ 32065460 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_237411658455564283589 : Nat.Prime 237411658455564283589 := by
  apply lucas_primality 237411658455564283589 (2 : ZMod 237411658455564283589)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (73, 1), (79, 1), (605401060944023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (73, 1), (79, 1), (605401060944023, 1)] : List FactorBlock).map factorBlockValue).prod) = 237411658455564283589 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_17
      · exact prime_oneHundredFiftyFourEV_73
      · exact prime_oneHundredFiftyFourEV_79
      · exact prime_oneHundredFiftyFourEV_605401060944023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 237411658455564283589) ^ 118705829227782141794 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 237411658455564283589) ^ 13965391673856722564 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 237411658455564283589) ^ 3252214499391291556 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 237411658455564283589) ^ 3005210866526130172 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 237411658455564283589) ^ 392156 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_377942286057032472047 : Nat.Prime 377942286057032472047 := by
  apply lucas_primality 377942286057032472047 (5 : ZMod 377942286057032472047)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (113, 1), (199, 1), (1592737, 1), (5276183617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (113, 1), (199, 1), (1592737, 1), (5276183617, 1)] : List FactorBlock).map factorBlockValue).prod) = 377942286057032472047 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_113
      · exact prime_oneHundredFiftyFourEV_199
      · exact prime_oneHundredFiftyFourEV_1592737
      · exact prime_oneHundredFiftyFourEV_5276183617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 377942286057032472047) ^ 188971143028516236023 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 377942286057032472047) ^ 3344622000504712142 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 377942286057032472047) ^ 1899207467623278754 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 377942286057032472047) ^ 237291081990958 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 377942286057032472047) ^ 71631753838 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_409057769026532877619 : Nat.Prime 409057769026532877619 := by
  apply lucas_primality 409057769026532877619 (2 : ZMod 409057769026532877619)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (307863041, 1), (221450079283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (307863041, 1), (221450079283, 1)] : List FactorBlock).map factorBlockValue).prod) = 409057769026532877619 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_307863041
      · exact prime_oneHundredFiftyFourEV_221450079283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 409057769026532877619) ^ 204528884513266438809 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 409057769026532877619) ^ 136352589675510959206 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 409057769026532877619) ^ 1328700475698 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 409057769026532877619) ^ 1847178246 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_566792975919543197273 : Nat.Prime 566792975919543197273 := by
  apply lucas_primality 566792975919543197273 (3 : ZMod 566792975919543197273)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 2), (54287, 1), (805873, 1), (33050341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 2), (54287, 1), (805873, 1), (33050341, 1)] : List FactorBlock).map factorBlockValue).prod) = 566792975919543197273 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_7
      · exact prime_oneHundredFiftyFourEV_54287
      · exact prime_oneHundredFiftyFourEV_805873
      · exact prime_oneHundredFiftyFourEV_33050341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 566792975919543197273) ^ 283396487959771598636 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 566792975919543197273) ^ 80970425131363313896 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 566792975919543197273) ^ 10440675961455656 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 566792975919543197273) ^ 703327913851864 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 566792975919543197273) ^ 17149383599992 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_1550411355806685423811 : Nat.Prime 1550411355806685423811 := by
  apply lucas_primality 1550411355806685423811 (2 : ZMod 1550411355806685423811)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (11, 1), (3283807, 1), (476907466417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (11, 1), (3283807, 1), (476907466417, 1)] : List FactorBlock).map factorBlockValue).prod) = 1550411355806685423811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_5
      · exact prime_oneHundredFiftyFourEV_11
      · exact prime_oneHundredFiftyFourEV_3283807
      · exact prime_oneHundredFiftyFourEV_476907466417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1550411355806685423811) ^ 775205677903342711905 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1550411355806685423811) ^ 516803785268895141270 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1550411355806685423811) ^ 310082271161337084762 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1550411355806685423811) ^ 140946486891516856710 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1550411355806685423811) ^ 472138391752830 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1550411355806685423811) ^ 3250968930 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_2612391577778882735663 : Nat.Prime 2612391577778882735663 := by
  apply lucas_primality 2612391577778882735663 (5 : ZMod 2612391577778882735663)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (541, 1), (659, 1), (3663748043973649, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (541, 1), (659, 1), (3663748043973649, 1)] : List FactorBlock).map factorBlockValue).prod) = 2612391577778882735663 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_541
      · exact prime_oneHundredFiftyFourEV_659
      · exact prime_oneHundredFiftyFourEV_3663748043973649
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2612391577778882735663) ^ 1306195788889441367831 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 2612391577778882735663) ^ 4828819921957269382 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 2612391577778882735663) ^ 3964175383579488218 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 2612391577778882735663) ^ 713038 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_9803875754057824351433 : Nat.Prime 9803875754057824351433 := by
  apply lucas_primality 9803875754057824351433 (3 : ZMod 9803875754057824351433)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (94268036096709849533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (94268036096709849533, 1)] : List FactorBlock).map factorBlockValue).prod) = 9803875754057824351433 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_13
      · exact prime_oneHundredFiftyFourEV_94268036096709849533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 9803875754057824351433) ^ 4901937877028912175716 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 9803875754057824351433) ^ 754144288773678796264 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 9803875754057824351433) ^ 104 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_21135774620255879590933 : Nat.Prime 21135774620255879590933 := by
  apply lucas_primality 21135774620255879590933 (2 : ZMod 21135774620255879590933)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (337, 1), (5226452675632017703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (337, 1), (5226452675632017703, 1)] : List FactorBlock).map factorBlockValue).prod) = 21135774620255879590933 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_337
      · exact prime_oneHundredFiftyFourEV_5226452675632017703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 21135774620255879590933) ^ 10567887310127939795466 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 21135774620255879590933) ^ 7045258206751959863644 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 21135774620255879590933) ^ 62717432107584212436 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 21135774620255879590933) ^ 4044 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_26322659856962398014803 : Nat.Prime 26322659856962398014803 := by
  apply lucas_primality 26322659856962398014803 (2 : ZMod 26322659856962398014803)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (61, 1), (215759507024281950941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (61, 1), (215759507024281950941, 1)] : List FactorBlock).map factorBlockValue).prod) = 26322659856962398014803 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_61
      · exact prime_oneHundredFiftyFourEV_215759507024281950941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 26322659856962398014803) ^ 13161329928481199007401 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 26322659856962398014803) ^ 431519014048563901882 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 26322659856962398014803) ^ 122 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_32572552001813826887981 : Nat.Prime 32572552001813826887981 := by
  apply lucas_primality 32572552001813826887981 (2 : ZMod 32572552001813826887981)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (67, 1), (141707, 1), (171536160021871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (67, 1), (141707, 1), (171536160021871, 1)] : List FactorBlock).map factorBlockValue).prod) = 32572552001813826887981 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_5
      · exact prime_oneHundredFiftyFourEV_67
      · exact prime_oneHundredFiftyFourEV_141707
      · exact prime_oneHundredFiftyFourEV_171536160021871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 32572552001813826887981) ^ 16286276000906913443990 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 32572552001813826887981) ^ 6514510400362765377596 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 32572552001813826887981) ^ 486157492564385475940 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 32572552001813826887981) ^ 229858454429307140 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 32572552001813826887981) ^ 189887380 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_35853529750253765128927 : Nat.Prime 35853529750253765128927 := by
  apply lucas_primality 35853529750253765128927 (3 : ZMod 35853529750253765128927)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (17, 1), (71, 1), (8317, 1), (66139999399751, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (17, 1), (71, 1), (8317, 1), (66139999399751, 1)] : List FactorBlock).map factorBlockValue).prod) = 35853529750253765128927 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_17
      · exact prime_oneHundredFiftyFourEV_71
      · exact prime_oneHundredFiftyFourEV_8317
      · exact prime_oneHundredFiftyFourEV_66139999399751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 35853529750253765128927) ^ 17926764875126882564463 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 35853529750253765128927) ^ 11951176583417921709642 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 35853529750253765128927) ^ 2109031161779633242878 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 35853529750253765128927) ^ 504979292257095283506 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 35853529750253765128927) ^ 4310872880876970678 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 35853529750253765128927) ^ 542085426 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_39915617120333816487827 : Nat.Prime 39915617120333816487827 := by
  apply lucas_primality 39915617120333816487827 (2 : ZMod 39915617120333816487827)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1283, 1), (15555579548064620611, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1283, 1), (15555579548064620611, 1)] : List FactorBlock).map factorBlockValue).prod) = 39915617120333816487827 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_1283
      · exact prime_oneHundredFiftyFourEV_15555579548064620611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 39915617120333816487827) ^ 19957808560166908243913 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 39915617120333816487827) ^ 31111159096129241222 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 39915617120333816487827) ^ 2566 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_42323383244774965465313 : Nat.Prime 42323383244774965465313 := by
  apply lucas_primality 42323383244774965465313 (3 : ZMod 42323383244774965465313)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (29, 1), (607, 1), (29501, 1), (2546871139697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (29, 1), (607, 1), (29501, 1), (2546871139697, 1)] : List FactorBlock).map factorBlockValue).prod) = 42323383244774965465313 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_29
      · exact prime_oneHundredFiftyFourEV_607
      · exact prime_oneHundredFiftyFourEV_29501
      · exact prime_oneHundredFiftyFourEV_2546871139697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 42323383244774965465313) ^ 21161691622387482732656 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 42323383244774965465313) ^ 1459427008440516050528 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 42323383244774965465313) ^ 69725507816762710816 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 42323383244774965465313) ^ 1434642325506761312 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 42323383244774965465313) ^ 16617795296 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_50779631750837658563161 : Nat.Prime 50779631750837658563161 := by
  apply lucas_primality 50779631750837658563161 (23 : ZMod 50779631750837658563161)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (5, 1), (7, 1), (17, 1), (1397761, 1), (282674030603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (5, 1), (7, 1), (17, 1), (1397761, 1), (282674030603, 1)] : List FactorBlock).map factorBlockValue).prod) = 50779631750837658563161 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_5
      · exact prime_oneHundredFiftyFourEV_7
      · exact prime_oneHundredFiftyFourEV_17
      · exact prime_oneHundredFiftyFourEV_1397761
      · exact prime_oneHundredFiftyFourEV_282674030603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 50779631750837658563161) ^ 25389815875418829281580 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (23 : ZMod 50779631750837658563161) ^ 16926543916945886187720 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (23 : ZMod 50779631750837658563161) ^ 10155926350167531712632 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (23 : ZMod 50779631750837658563161) ^ 7254233107262522651880 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (23 : ZMod 50779631750837658563161) ^ 2987037161813979915480 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (23 : ZMod 50779631750837658563161) ^ 36329266413097560 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (23 : ZMod 50779631750837658563161) ^ 179640243720 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_72516717383281304613041 : Nat.Prime 72516717383281304613041 := by
  apply lucas_primality 72516717383281304613041 (3 : ZMod 72516717383281304613041)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (11, 1), (29, 1), (769, 1), (3695141951608433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (11, 1), (29, 1), (769, 1), (3695141951608433, 1)] : List FactorBlock).map factorBlockValue).prod) = 72516717383281304613041 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_5
      · exact prime_oneHundredFiftyFourEV_11
      · exact prime_oneHundredFiftyFourEV_29
      · exact prime_oneHundredFiftyFourEV_769
      · exact prime_oneHundredFiftyFourEV_3695141951608433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 72516717383281304613041) ^ 36258358691640652306520 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 72516717383281304613041) ^ 14503343476656260922608 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 72516717383281304613041) ^ 6592428853025573146640 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 72516717383281304613041) ^ 2500576461492458779760 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 72516717383281304613041) ^ 94300022605047210160 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 72516717383281304613041) ^ 19624880 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_75170959412697771711827 : Nat.Prime 75170959412697771711827 := by
  apply lucas_primality 75170959412697771711827 (2 : ZMod 75170959412697771711827)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (486388121, 1), (77274666225553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (486388121, 1), (77274666225553, 1)] : List FactorBlock).map factorBlockValue).prod) = 75170959412697771711827 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_486388121
      · exact prime_oneHundredFiftyFourEV_77274666225553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 75170959412697771711827) ^ 37585479706348885855913 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 75170959412697771711827) ^ 154549332451106 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 75170959412697771711827) ^ 972776242 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_215121178501522590773563 : Nat.Prime 215121178501522590773563 := by
  apply lucas_primality 215121178501522590773563 (2 : ZMod 215121178501522590773563)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (35853529750253765128927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (35853529750253765128927, 1)] : List FactorBlock).map factorBlockValue).prod) = 215121178501522590773563 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_35853529750253765128927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 215121178501522590773563) ^ 107560589250761295386781 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 215121178501522590773563) ^ 71707059500507530257854 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 215121178501522590773563) ^ 6 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_390870624021765922655773 : Nat.Prime 390870624021765922655773 := by
  apply lucas_primality 390870624021765922655773 (2 : ZMod 390870624021765922655773)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (32572552001813826887981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (32572552001813826887981, 1)] : List FactorBlock).map factorBlockValue).prod) = 390870624021765922655773 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_32572552001813826887981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 390870624021765922655773) ^ 195435312010882961327886 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 390870624021765922655773) ^ 130290208007255307551924 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 390870624021765922655773) ^ 12 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_1100407964364149102098139 : Nat.Prime 1100407964364149102098139 := by
  apply lucas_primality 1100407964364149102098139 (2 : ZMod 1100407964364149102098139)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (42323383244774965465313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (42323383244774965465313, 1)] : List FactorBlock).map factorBlockValue).prod) = 1100407964364149102098139 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_13
      · exact prime_oneHundredFiftyFourEV_42323383244774965465313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1100407964364149102098139) ^ 550203982182074551049069 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1100407964364149102098139) ^ 84646766489549930930626 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1100407964364149102098139) ^ 26 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_1923847716053114540002427 : Nat.Prime 1923847716053114540002427 := by
  apply lucas_primality 1923847716053114540002427 (2 : ZMod 1923847716053114540002427)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (1279, 1), (107441512121809144421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (1279, 1), (107441512121809144421, 1)] : List FactorBlock).map factorBlockValue).prod) = 1923847716053114540002427 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_7
      · exact prime_oneHundredFiftyFourEV_1279
      · exact prime_oneHundredFiftyFourEV_107441512121809144421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1923847716053114540002427) ^ 961923858026557270001213 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1923847716053114540002427) ^ 274835388007587791428918 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1923847716053114540002427) ^ 1504181169705328021894 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1923847716053114540002427) ^ 17906 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_2091017780134080460271381 : Nat.Prime 2091017780134080460271381 := by
  apply lucas_primality 2091017780134080460271381 (3 : ZMod 2091017780134080460271381)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (1373, 1), (76147770580265129653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (1373, 1), (76147770580265129653, 1)] : List FactorBlock).map factorBlockValue).prod) = 2091017780134080460271381 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_5
      · exact prime_oneHundredFiftyFourEV_1373
      · exact prime_oneHundredFiftyFourEV_76147770580265129653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2091017780134080460271381) ^ 1045508890067040230135690 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 2091017780134080460271381) ^ 418203556026816092054276 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 2091017780134080460271381) ^ 1522955411605302593060 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 2091017780134080460271381) ^ 27460 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_2200257406758204375119333 : Nat.Prime 2200257406758204375119333 := by
  apply lucas_primality 2200257406758204375119333 (2 : ZMod 2200257406758204375119333)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5783, 1), (674173, 1), (141087634660187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5783, 1), (674173, 1), (141087634660187, 1)] : List FactorBlock).map factorBlockValue).prod) = 2200257406758204375119333 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_5783
      · exact prime_oneHundredFiftyFourEV_674173
      · exact prime_oneHundredFiftyFourEV_141087634660187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2200257406758204375119333) ^ 1100128703379102187559666 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2200257406758204375119333) ^ 380469895687049001404 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2200257406758204375119333) ^ 3263639164959445684 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2200257406758204375119333) ^ 15594969836 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_4613081487580689516488033 : Nat.Prime 4613081487580689516488033 := by
  apply lucas_primality 4613081487580689516488033 (5 : ZMod 4613081487580689516488033)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (7, 1), (97, 1), (719, 1), (17207, 1), (17160791887493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (7, 1), (97, 1), (719, 1), (17207, 1), (17160791887493, 1)] : List FactorBlock).map factorBlockValue).prod) = 4613081487580689516488033 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_7
      · exact prime_oneHundredFiftyFourEV_97
      · exact prime_oneHundredFiftyFourEV_719
      · exact prime_oneHundredFiftyFourEV_17207
      · exact prime_oneHundredFiftyFourEV_17160791887493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 4613081487580689516488033) ^ 2306540743790344758244016 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 4613081487580689516488033) ^ 659011641082955645212576 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 4613081487580689516488033) ^ 47557541109079273365856 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 4613081487580689516488033) ^ 6415968689263824084128 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 4613081487580689516488033) ^ 268093304328511042976 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (5 : ZMod 4613081487580689516488033) ^ 268815187424 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_9390813913339934693457277 : Nat.Prime 9390813913339934693457277 := by
  apply lucas_primality 9390813913339934693457277 (2 : ZMod 9390813913339934693457277)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (397, 1), (2141, 1), (3191, 1), (7922443, 1), (12139691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (397, 1), (2141, 1), (3191, 1), (7922443, 1), (12139691, 1)] : List FactorBlock).map factorBlockValue).prod) = 9390813913339934693457277 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_397
      · exact prime_oneHundredFiftyFourEV_2141
      · exact prime_oneHundredFiftyFourEV_3191
      · exact prime_oneHundredFiftyFourEV_7922443
      · exact prime_oneHundredFiftyFourEV_12139691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9390813913339934693457277) ^ 4695406956669967346728638 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 9390813913339934693457277) ^ 3130271304446644897819092 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 9390813913339934693457277) ^ 23654443106649709555308 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 9390813913339934693457277) ^ 4386181183250786872236 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 9390813913339934693457277) ^ 2942906271808190126436 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 9390813913339934693457277) ^ 1185343196958303732 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 9390813913339934693457277) ^ 773562845490872436 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_10954160408629724675816719 : Nat.Prime 10954160408629724675816719 := by
  apply lucas_primality 10954160408629724675816719 (3 : ZMod 10954160408629724675816719)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (17, 1), (16787, 1), (857453, 1), (2486991238073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (17, 1), (16787, 1), (857453, 1), (2486991238073, 1)] : List FactorBlock).map factorBlockValue).prod) = 10954160408629724675816719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_17
      · exact prime_oneHundredFiftyFourEV_16787
      · exact prime_oneHundredFiftyFourEV_857453
      · exact prime_oneHundredFiftyFourEV_2486991238073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 10954160408629724675816719) ^ 5477080204314862337908359 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 10954160408629724675816719) ^ 3651386802876574891938906 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 10954160408629724675816719) ^ 644362376978219098577454 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 10954160408629724675816719) ^ 652538298006178869114 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 10954160408629724675816719) ^ 12775231305540624006 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 10954160408629724675816719) ^ 4404583434366 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_15721362589744810796714419 : Nat.Prime 15721362589744810796714419 := by
  apply lucas_primality 15721362589744810796714419 (10 : ZMod 15721362589744810796714419)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (87094849, 1), (30084753901930547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (87094849, 1), (30084753901930547, 1)] : List FactorBlock).map factorBlockValue).prod) = 15721362589744810796714419 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_87094849
      · exact prime_oneHundredFiftyFourEV_30084753901930547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 15721362589744810796714419) ^ 7860681294872405398357209 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (10 : ZMod 15721362589744810796714419) ^ 5240454196581603598904806 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (10 : ZMod 15721362589744810796714419) ^ 180508523411583282 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (10 : ZMod 15721362589744810796714419) ^ 522569094 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_24471653246214335193111517 : Nat.Prime 24471653246214335193111517 := by
  apply lucas_primality 24471653246214335193111517 (2 : ZMod 24471653246214335193111517)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (29, 1), (757, 1), (30964703946074612927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (29, 1), (757, 1), (30964703946074612927, 1)] : List FactorBlock).map factorBlockValue).prod) = 24471653246214335193111517 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_29
      · exact prime_oneHundredFiftyFourEV_757
      · exact prime_oneHundredFiftyFourEV_30964703946074612927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 24471653246214335193111517) ^ 12235826623107167596555758 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 24471653246214335193111517) ^ 8157217748738111731037172 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 24471653246214335193111517) ^ 843850111938425351486604 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 24471653246214335193111517) ^ 32327150919701895895788 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 24471653246214335193111517) ^ 790308 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_27432439378007330697114613 : Nat.Prime 27432439378007330697114613 := by
  apply lucas_primality 27432439378007330697114613 (6 : ZMod 27432439378007330697114613)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (1188628943, 1), (174841368000787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (1188628943, 1), (174841368000787, 1)] : List FactorBlock).map factorBlockValue).prod) = 27432439378007330697114613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_11
      · exact prime_oneHundredFiftyFourEV_1188628943
      · exact prime_oneHundredFiftyFourEV_174841368000787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 27432439378007330697114613) ^ 13716219689003665348557306 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (6 : ZMod 27432439378007330697114613) ^ 9144146459335776899038204 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (6 : ZMod 27432439378007330697114613) ^ 2493858125273393699737692 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (6 : ZMod 27432439378007330697114613) ^ 23079060576103884 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (6 : ZMod 27432439378007330697114613) ^ 156899020476 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_57726410954925381685716451 : Nat.Prime 57726410954925381685716451 := by
  apply lucas_primality 57726410954925381685716451 (2 : ZMod 57726410954925381685716451)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (19, 1), (827, 1), (24491996416947912211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (19, 1), (827, 1), (24491996416947912211, 1)] : List FactorBlock).map factorBlockValue).prod) = 57726410954925381685716451 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_5
      · exact prime_oneHundredFiftyFourEV_19
      · exact prime_oneHundredFiftyFourEV_827
      · exact prime_oneHundredFiftyFourEV_24491996416947912211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 57726410954925381685716451) ^ 28863205477462690842858225 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 57726410954925381685716451) ^ 19242136984975127228572150 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 57726410954925381685716451) ^ 11545282190985076337143290 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 57726410954925381685716451) ^ 3038232155522388509774550 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 57726410954925381685716451) ^ 69802189788301549801350 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 57726410954925381685716451) ^ 2356950 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_225892183811209247936414003 : Nat.Prime 225892183811209247936414003 := by
  apply lucas_primality 225892183811209247936414003 (2 : ZMod 225892183811209247936414003)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (877, 1), (54902009, 1), (2345758929978757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (877, 1), (54902009, 1), (2345758929978757, 1)] : List FactorBlock).map factorBlockValue).prod) = 225892183811209247936414003 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_877
      · exact prime_oneHundredFiftyFourEV_54902009
      · exact prime_oneHundredFiftyFourEV_2345758929978757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 225892183811209247936414003) ^ 112946091905604623968207001 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 225892183811209247936414003) ^ 257573755771048173245626 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 225892183811209247936414003) ^ 4114461163182739778 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 225892183811209247936414003) ^ 96298123786 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_334685845867343113670495747 : Nat.Prime 334685845867343113670495747 := by
  apply lucas_primality 334685845867343113670495747 (2 : ZMod 334685845867343113670495747)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1669, 1), (1913, 1), (9787, 1), (25031, 1), (213948011897, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1669, 1), (1913, 1), (9787, 1), (25031, 1), (213948011897, 1)] : List FactorBlock).map factorBlockValue).prod) = 334685845867343113670495747 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_1669
      · exact prime_oneHundredFiftyFourEV_1913
      · exact prime_oneHundredFiftyFourEV_9787
      · exact prime_oneHundredFiftyFourEV_25031
      · exact prime_oneHundredFiftyFourEV_213948011897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 334685845867343113670495747) ^ 167342922933671556835247873 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 334685845867343113670495747) ^ 200530764450175622331034 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 334685845867343113670495747) ^ 174953395644193995645842 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 334685845867343113670495747) ^ 34196980266408819216358 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 334685845867343113670495747) ^ 13370853975763777462766 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 334685845867343113670495747) ^ 1564332582012818 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_1116988344489783152372697463 : Nat.Prime 1116988344489783152372697463 := by
  apply lucas_primality 1116988344489783152372697463 (3 : ZMod 1116988344489783152372697463)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (197, 1), (353, 1), (8707, 1), (245711, 1), (54404582207, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (197, 1), (353, 1), (8707, 1), (245711, 1), (54404582207, 1)] : List FactorBlock).map factorBlockValue).prod) = 1116988344489783152372697463 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_23
      · exact prime_oneHundredFiftyFourEV_197
      · exact prime_oneHundredFiftyFourEV_353
      · exact prime_oneHundredFiftyFourEV_8707
      · exact prime_oneHundredFiftyFourEV_245711
      · exact prime_oneHundredFiftyFourEV_54404582207
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1116988344489783152372697463) ^ 558494172244891576186348731 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1116988344489783152372697463) ^ 372329448163261050790899154 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1116988344489783152372697463) ^ 48564710629990571842291194 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1116988344489783152372697463) ^ 5669991596394838336917246 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1116988344489783152372697463) ^ 3164272930565957938732854 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1116988344489783152372697463) ^ 128286246065209963520466 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1116988344489783152372697463) ^ 4545943586122652841642 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1116988344489783152372697463) ^ 20531144605427466 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_1130863976098351887184780661 : Nat.Prime 1130863976098351887184780661 := by
  apply lucas_primality 1130863976098351887184780661 (2 : ZMod 1130863976098351887184780661)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (56645794981, 1), (998188812141893, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (56645794981, 1), (998188812141893, 1)] : List FactorBlock).map factorBlockValue).prod) = 1130863976098351887184780661 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_5
      · exact prime_oneHundredFiftyFourEV_56645794981
      · exact prime_oneHundredFiftyFourEV_998188812141893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1130863976098351887184780661) ^ 565431988049175943592390330 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1130863976098351887184780661) ^ 226172795219670377436956132 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1130863976098351887184780661) ^ 19963776242837860 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1130863976098351887184780661) ^ 1132915899620 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_2677486766938744909363965977 : Nat.Prime 2677486766938744909363965977 := by
  apply lucas_primality 2677486766938744909363965977 (3 : ZMod 2677486766938744909363965977)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (334685845867343113670495747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (334685845867343113670495747, 1)] : List FactorBlock).map factorBlockValue).prod) = 2677486766938744909363965977 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_334685845867343113670495747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 2677486766938744909363965977) ^ 1338743383469372454681982988 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 2677486766938744909363965977) ^ 8 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_3873810641528396890143610351 : Nat.Prime 3873810641528396890143610351 := by
  apply lucas_primality 3873810641528396890143610351 (6 : ZMod 3873810641528396890143610351)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (647, 1), (39915617120333816487827, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (647, 1), (39915617120333816487827, 1)] : List FactorBlock).map factorBlockValue).prod) = 3873810641528396890143610351 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_5
      · exact prime_oneHundredFiftyFourEV_647
      · exact prime_oneHundredFiftyFourEV_39915617120333816487827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 3873810641528396890143610351) ^ 1936905320764198445071805175 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (6 : ZMod 3873810641528396890143610351) ^ 1291270213842798963381203450 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (6 : ZMod 3873810641528396890143610351) ^ 774762128305679378028722070 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (6 : ZMod 3873810641528396890143610351) ^ 5987342568050072473174050 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (6 : ZMod 3873810641528396890143610351) ^ 97050 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_6502467862565523351312488803 : Nat.Prime 6502467862565523351312488803 := by
  apply lucas_primality 6502467862565523351312488803 (2 : ZMod 6502467862565523351312488803)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (107, 1), (43001837, 1), (78511797954027271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (107, 1), (43001837, 1), (78511797954027271, 1)] : List FactorBlock).map factorBlockValue).prod) = 6502467862565523351312488803 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_107
      · exact prime_oneHundredFiftyFourEV_43001837
      · exact prime_oneHundredFiftyFourEV_78511797954027271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6502467862565523351312488803) ^ 3251233931282761675656244401 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 6502467862565523351312488803) ^ 2167489287521841117104162934 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 6502467862565523351312488803) ^ 60770727687528255619742886 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 6502467862565523351312488803) ^ 151213722859456523946 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 6502467862565523351312488803) ^ 82821538062 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_7586212506326443909864570267 : Nat.Prime 7586212506326443909864570267 := by
  apply lucas_primality 7586212506326443909864570267 (3 : ZMod 7586212506326443909864570267)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (383, 1), (1100407964364149102098139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (383, 1), (1100407964364149102098139, 1)] : List FactorBlock).map factorBlockValue).prod) = 7586212506326443909864570267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_383
      · exact prime_oneHundredFiftyFourEV_1100407964364149102098139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 7586212506326443909864570267) ^ 3793106253163221954932285133 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 7586212506326443909864570267) ^ 2528737502108814636621523422 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 7586212506326443909864570267) ^ 19807343358554683837766502 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 7586212506326443909864570267) ^ 6894 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_9582584218517613359828930867 : Nat.Prime 9582584218517613359828930867 := by
  apply lucas_primality 9582584218517613359828930867 (2 : ZMod 9582584218517613359828930867)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (83, 1), (57726410954925381685716451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (83, 1), (57726410954925381685716451, 1)] : List FactorBlock).map factorBlockValue).prod) = 9582584218517613359828930867 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_83
      · exact prime_oneHundredFiftyFourEV_57726410954925381685716451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 9582584218517613359828930867) ^ 4791292109258806679914465433 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 9582584218517613359828930867) ^ 115452821909850763371432902 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 9582584218517613359828930867) ^ 166 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_18206910015183465383674968641 : Nat.Prime 18206910015183465383674968641 := by
  apply lucas_primality 18206910015183465383674968641 (3 : ZMod 18206910015183465383674968641)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (5, 1), (7, 1), (11, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (5, 1), (7, 1), (11, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 18206910015183465383674968641 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_5
      · exact prime_oneHundredFiftyFourEV_7
      · exact prime_oneHundredFiftyFourEV_11
      · exact prime_oneHundredFiftyFourEV_171401
      · exact prime_oneHundredFiftyFourEV_714027719
      · exact prime_oneHundredFiftyFourEV_6037638679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 18206910015183465383674968641) ^ 9103455007591732691837484320 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 18206910015183465383674968641) ^ 3641382003036693076734993728 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 18206910015183465383674968641) ^ 2600987145026209340524995520 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 18206910015183465383674968641) ^ 1655173637743951398515906240 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 18206910015183465383674968641) ^ 106224059458133064472640 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 18206910015183465383674968641) ^ 25498884049883034560 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 18206910015183465383674968641) ^ 3015568003184820160 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_20229900016870517092972187389 : Nat.Prime 20229900016870517092972187389 := by
  apply lucas_primality 20229900016870517092972187389 (2 : ZMod 20229900016870517092972187389)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (227, 1), (390870624021765922655773, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (227, 1), (390870624021765922655773, 1)] : List FactorBlock).map factorBlockValue).prod) = 20229900016870517092972187389 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_19
      · exact prime_oneHundredFiftyFourEV_227
      · exact prime_oneHundredFiftyFourEV_390870624021765922655773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 20229900016870517092972187389) ^ 10114950008435258546486093694 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 20229900016870517092972187389) ^ 6743300005623505697657395796 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 20229900016870517092972187389) ^ 1064731579835290373314325652 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 20229900016870517092972187389) ^ 89118502276962630365516244 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 20229900016870517092972187389) ^ 51756 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_45517275037958663459187421601 : Nat.Prime 45517275037958663459187421601 := by
  apply lucas_primality 45517275037958663459187421601 (3 : ZMod 45517275037958663459187421601)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 2), (7, 1), (11, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 2), (7, 1), (11, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 45517275037958663459187421601 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_5
      · exact prime_oneHundredFiftyFourEV_7
      · exact prime_oneHundredFiftyFourEV_11
      · exact prime_oneHundredFiftyFourEV_171401
      · exact prime_oneHundredFiftyFourEV_714027719
      · exact prime_oneHundredFiftyFourEV_6037638679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 45517275037958663459187421601) ^ 22758637518979331729593710800 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 45517275037958663459187421601) ^ 9103455007591732691837484320 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 45517275037958663459187421601) ^ 6502467862565523351312488800 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 45517275037958663459187421601) ^ 4137934094359878496289765600 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 45517275037958663459187421601) ^ 265560148645332661181600 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 45517275037958663459187421601) ^ 63747210124707586400 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 45517275037958663459187421601) ^ 7538920007962050400 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_45517275037958663459187421603 : Nat.Prime 45517275037958663459187421603 := by
  apply lucas_primality 45517275037958663459187421603 (3 : ZMod 45517275037958663459187421603)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7586212506326443909864570267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7586212506326443909864570267, 1)] : List FactorBlock).map factorBlockValue).prod) = 45517275037958663459187421603 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_3
      · exact prime_oneHundredFiftyFourEV_7586212506326443909864570267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 45517275037958663459187421603) ^ 22758637518979331729593710801 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 45517275037958663459187421603) ^ 15172425012652887819729140534 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (3 : ZMod 45517275037958663459187421603) ^ 6 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFourEV_45517275037958663459187421613 : Nat.Prime 45517275037958663459187421613 := by
  apply lucas_primality 45517275037958663459187421613 (2 : ZMod 45517275037958663459187421613)
  · rw [← oneHundredFiftyFourEVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (68513737, 1), (166088134405654531219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (68513737, 1), (166088134405654531219, 1)] : List FactorBlock).map factorBlockValue).prod) = 45517275037958663459187421613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFourEV_2
      · exact prime_oneHundredFiftyFourEV_68513737
      · exact prime_oneHundredFiftyFourEV_166088134405654531219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 45517275037958663459187421613) ^ 22758637518979331729593710806 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 45517275037958663459187421613) ^ 664352537622618124876 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide
    · change (2 : ZMod 45517275037958663459187421613) ^ 274054948 ≠ 1
      rw [← oneHundredFiftyFourEVFastPow_eq_pow]
      decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686400 : Nat.totient 182069100151834653836749686400 = 56748479260082249026990080000 := by
  rw [← show ((([(2, 7), (5, 2), (7, 1), (11, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686400 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_2, prime_oneHundredFiftyFourEV_5, prime_oneHundredFiftyFourEV_7, prime_oneHundredFiftyFourEV_11, prime_oneHundredFiftyFourEV_171401, prime_oneHundredFiftyFourEV_714027719, prime_oneHundredFiftyFourEV_6037638679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686401 : Nat.totient 182069100151834653836749686401 = 181154097483890857399900968768 := by
  rw [← show ((([(199, 1), (2195989, 1), (2502790933, 1), (166467108527, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686401 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_199, prime_oneHundredFiftyFourEV_2195989, prime_oneHundredFiftyFourEV_2502790933, prime_oneHundredFiftyFourEV_166467108527]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686402 : Nat.totient 182069100151834653836749686402 = 54101404116288235075728844800 := by
  rw [← show ((([(2, 1), (3, 2), (17, 1), (37, 1), (43, 1), (311, 1), (7187, 1), (167315665732025891, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686402 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_2, prime_oneHundredFiftyFourEV_3, prime_oneHundredFiftyFourEV_17, prime_oneHundredFiftyFourEV_37, prime_oneHundredFiftyFourEV_43, prime_oneHundredFiftyFourEV_311, prime_oneHundredFiftyFourEV_7187, prime_oneHundredFiftyFourEV_167315665732025891]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686403 : Nat.totient 182069100151834653836749686403 = 178195263437829364647304609344 := by
  rw [← show ((([(47, 1), (6834613, 1), (566792975919543197273, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686403 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_47, prime_oneHundredFiftyFourEV_6834613, prime_oneHundredFiftyFourEV_566792975919543197273]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686404 : Nat.totient 182069100151834653836749686404 = 91034550075917326918374843200 := by
  rw [← show ((([(2, 2), (45517275037958663459187421601, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686404 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_2, prime_oneHundredFiftyFourEV_45517275037958663459187421601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686405 : Nat.totient 182069100151834653836749686405 = 89115900874950799159728869376 := by
  rw [← show ((([(3, 1), (5, 1), (13, 1), (173, 1), (45764899, 1), (117929653649192977, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686405 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_3, prime_oneHundredFiftyFourEV_5, prime_oneHundredFiftyFourEV_13, prime_oneHundredFiftyFourEV_173, prime_oneHundredFiftyFourEV_45764899, prime_oneHundredFiftyFourEV_117929653649192977]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686406 : Nat.totient 182069100151834653836749686406 = 87090491969106110912968329600 := by
  rw [← show ((([(2, 1), (29, 1), (149, 1), (691, 1), (983, 1), (31016330705363614231, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686406 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_2, prime_oneHundredFiftyFourEV_29, prime_oneHundredFiftyFourEV_149, prime_oneHundredFiftyFourEV_691, prime_oneHundredFiftyFourEV_983, prime_oneHundredFiftyFourEV_31016330705363614231]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686407 : Nat.totient 182069100151834653836749686407 = 156059209475858574201374654112 := by
  rw [← show ((([(7, 1), (8146423, 1), (2267521189, 1), (1408055893883, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686407 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_7, prime_oneHundredFiftyFourEV_8146423, prime_oneHundredFiftyFourEV_2267521189, prime_oneHundredFiftyFourEV_1408055893883]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686408 : Nat.totient 182069100151834653836749686408 = 60689700050611551278916562128 := by
  rw [← show ((([(2, 3), (3, 1), (7586212506326443909864570267, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686408 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_2, prime_oneHundredFiftyFourEV_3, prime_oneHundredFiftyFourEV_7586212506326443909864570267]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686409 : Nat.totient 182069100151834653836749686409 = 179569590580403040229557338016 := by
  rw [← show ((([(73, 1), (33179, 1), (75170959412697771711827, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686409 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_73, prime_oneHundredFiftyFourEV_33179, prime_oneHundredFiftyFourEV_75170959412697771711827]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686410 : Nat.totient 182069100151834653836749686410 = 72827640060733861534699874560 := by
  rw [← show ((([(2, 1), (5, 1), (18206910015183465383674968641, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686410 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_2, prime_oneHundredFiftyFourEV_5, prime_oneHundredFiftyFourEV_18206910015183465383674968641]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686411 : Nat.totient 182069100151834653836749686411 = 110344908485714550617879524800 := by
  rw [← show ((([(3, 3), (11, 1), (158265131, 1), (3873419681044591673, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686411 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_3, prime_oneHundredFiftyFourEV_11, prime_oneHundredFiftyFourEV_158265131, prime_oneHundredFiftyFourEV_3873419681044591673]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686412 : Nat.totient 182069100151834653836749686412 = 91034550075917326918374843204 := by
  rw [← show ((([(2, 2), (45517275037958663459187421603, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686412 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_2, prime_oneHundredFiftyFourEV_45517275037958663459187421603]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686413 : Nat.totient 182069100151834653836749686413 = 180759250510433219114310428208 := by
  rw [← show ((([(139, 1), (8998596912829, 1), (145561541879123, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686413 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_139, prime_oneHundredFiftyFourEV_8998596912829, prime_oneHundredFiftyFourEV_145561541879123]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686414 : Nat.totient 182069100151834653836749686414 = 52014524712480375496695336960 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (18541, 1), (21617, 1), (8348687, 1), (1295508299753, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686414 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_2, prime_oneHundredFiftyFourEV_3, prime_oneHundredFiftyFourEV_7, prime_oneHundredFiftyFourEV_18541, prime_oneHundredFiftyFourEV_21617, prime_oneHundredFiftyFourEV_8348687, prime_oneHundredFiftyFourEV_1295508299753]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686415 : Nat.totient 182069100151834653836749686415 = 145496786785663004000796644352 := by
  rw [← show ((([(5, 1), (919, 1), (1400369249, 1), (28294900080643093, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686415 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_5, prime_oneHundredFiftyFourEV_919, prime_oneHundredFiftyFourEV_1400369249, prime_oneHundredFiftyFourEV_28294900080643093]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686416 : Nat.totient 182069100151834653836749686416 = 86243257962369147244535392896 := by
  rw [← show ((([(2, 4), (19, 1), (20106275743, 1), (29787292351536653, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686416 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_2, prime_oneHundredFiftyFourEV_19, prime_oneHundredFiftyFourEV_20106275743, prime_oneHundredFiftyFourEV_29787292351536653]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686417 : Nat.totient 182069100151834653836749686417 = 121374999586409586149082830448 := by
  rw [← show ((([(3, 1), (27583, 1), (2200257406758204375119333, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686417 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_3, prime_oneHundredFiftyFourEV_27583, prime_oneHundredFiftyFourEV_2200257406758204375119333]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686418 : Nat.totient 182069100151834653836749686418 = 81321186172035329257109040720 := by
  rw [← show ((([(2, 1), (13, 1), (31, 1), (225892183811209247936414003, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686418 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_2, prime_oneHundredFiftyFourEV_13, prime_oneHundredFiftyFourEV_31, prime_oneHundredFiftyFourEV_225892183811209247936414003]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686419 : Nat.totient 182069100151834653836749686419 = 169189912523805520116678365184 := by
  rw [← show ((([(17, 1), (79, 1), (1231757, 1), (110061440872466385569, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686419 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_17, prime_oneHundredFiftyFourEV_79, prime_oneHundredFiftyFourEV_1231757, prime_oneHundredFiftyFourEV_110061440872466385569]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686420 : Nat.totient 182069100151834653836749686420 = 48542817011960473756187212800 := by
  rw [← show ((([(2, 2), (3, 2), (5, 1), (5851, 1), (76387, 1), (5106029, 1), (443231799853, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686420 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_2, prime_oneHundredFiftyFourEV_3, prime_oneHundredFiftyFourEV_5, prime_oneHundredFiftyFourEV_5851, prime_oneHundredFiftyFourEV_76387, prime_oneHundredFiftyFourEV_5106029, prime_oneHundredFiftyFourEV_443231799853]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686421 : Nat.totient 182069100151834653836749686421 = 149274044844982449108391047120 := by
  rw [← show ((([(7, 1), (23, 1), (1130863976098351887184780661, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686421 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_7, prime_oneHundredFiftyFourEV_23, prime_oneHundredFiftyFourEV_1130863976098351887184780661]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686422 : Nat.totient 182069100151834653836749686422 = 82758681886665155628519745920 := by
  rw [← show ((([(2, 1), (11, 1), (155440836073, 1), (53241274286720537, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686422 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_2, prime_oneHundredFiftyFourEV_11, prime_oneHundredFiftyFourEV_155440836073, prime_oneHundredFiftyFourEV_53241274286720537]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686423 : Nat.totient 182069100151834653836749686423 = 121377557414756661031574346240 := by
  rw [← show ((([(3, 1), (65881, 1), (429295049, 1), (2145847865892989, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686423 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_3, prime_oneHundredFiftyFourEV_65881, prime_oneHundredFiftyFourEV_429295049, prime_oneHundredFiftyFourEV_2145847865892989]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686424 : Nat.totient 182069100151834653836749686424 = 91028451297242256855628677120 := by
  rw [← show ((([(2, 3), (17389, 1), (105407, 1), (12416585925872501761, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686424 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_2, prime_oneHundredFiftyFourEV_17389, prime_oneHundredFiftyFourEV_105407, prime_oneHundredFiftyFourEV_12416585925872501761]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686425 : Nat.totient 182069100151834653836749686425 = 145230395927602877945222400000 := by
  rw [← show ((([(5, 2), (421, 1), (2069, 1), (17609, 1), (337751, 1), (1405796033527, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686425 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_5, prime_oneHundredFiftyFourEV_421, prime_oneHundredFiftyFourEV_2069, prime_oneHundredFiftyFourEV_17609, prime_oneHundredFiftyFourEV_337751, prime_oneHundredFiftyFourEV_1405796033527]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686426 : Nat.totient 182069100151834653836749686426 = 60685852355179445049836525744 := by
  rw [← show ((([(2, 1), (3, 1), (15773, 1), (1923847716053114540002427, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686426 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_2, prime_oneHundredFiftyFourEV_3, prime_oneHundredFiftyFourEV_15773, prime_oneHundredFiftyFourEV_1923847716053114540002427]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686427 : Nat.totient 182069100151834653836749686427 = 182069100148679227279847077416 := by
  rw [← show ((([(57700314109, 1), (3155426499202294903, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686427 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_57700314109, prime_oneHundredFiftyFourEV_3155426499202294903]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686428 : Nat.totient 182069100151834653836749686428 = 77133849763505940147768390720 := by
  rw [← show ((([(2, 2), (7, 1), (167, 1), (181, 1), (215121178501522590773563, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686428 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_2, prime_oneHundredFiftyFourEV_7, prime_oneHundredFiftyFourEV_167, prime_oneHundredFiftyFourEV_181, prime_oneHundredFiftyFourEV_215121178501522590773563]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686429 : Nat.totient 182069100151834653836749686429 = 121379400101216459918786712192 := by
  rw [← show ((([(3, 2), (18584745588337, 1), (1088521762147013, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686429 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_3, prime_oneHundredFiftyFourEV_18584745588337, prime_oneHundredFiftyFourEV_1088521762147013]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686430 : Nat.totient 182069100151834653836749686430 = 71633744322012773684714929920 := by
  rw [← show ((([(2, 1), (5, 1), (61, 1), (3643964116889, 1), (81909131127767, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686430 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_2, prime_oneHundredFiftyFourEV_5, prime_oneHundredFiftyFourEV_61, prime_oneHundredFiftyFourEV_3643964116889, prime_oneHundredFiftyFourEV_81909131127767]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686431 : Nat.totient 182069100151834653836749686431 = 168063784741797490769342069952 := by
  rw [← show ((([(13, 1), (12229767619, 1), (1145182462382728073, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686431 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_13, prime_oneHundredFiftyFourEV_12229767619, prime_oneHundredFiftyFourEV_1145182462382728073]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686432 : Nat.totient 182069100151834653836749686432 = 60622787481647260704187848960 := by
  rw [← show ((([(2, 5), (3, 1), (907, 1), (2091017780134080460271381, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686432 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_2, prime_oneHundredFiftyFourEV_3, prime_oneHundredFiftyFourEV_907, prime_oneHundredFiftyFourEV_2091017780134080460271381]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686433 : Nat.totient 182069100151834653836749686433 = 163046705917943131167166612560 := by
  rw [← show ((([(11, 1), (67, 1), (653647, 1), (377942286057032472047, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686433 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_11, prime_oneHundredFiftyFourEV_67, prime_oneHundredFiftyFourEV_653647, prime_oneHundredFiftyFourEV_377942286057032472047]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686434 : Nat.totient 182069100151834653836749686434 = 89247083624800070850688766400 := by
  rw [← show ((([(2, 1), (53, 1), (1279, 1), (2786860621, 1), (481886308435871, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686434 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_2, prime_oneHundredFiftyFourEV_53, prime_oneHundredFiftyFourEV_1279, prime_oneHundredFiftyFourEV_2786860621, prime_oneHundredFiftyFourEV_481886308435871]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686435 : Nat.totient 182069100151834653836749686435 = 76119677074352996196692557824 := by
  rw [← show ((([(3, 1), (5, 1), (7, 1), (19, 1), (29, 1), (12893, 1), (13873, 1), (83639, 1), (210359508407, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686435 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_3, prime_oneHundredFiftyFourEV_5, prime_oneHundredFiftyFourEV_7, prime_oneHundredFiftyFourEV_19, prime_oneHundredFiftyFourEV_29, prime_oneHundredFiftyFourEV_12893, prime_oneHundredFiftyFourEV_13873, prime_oneHundredFiftyFourEV_83639, prime_oneHundredFiftyFourEV_210359508407]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686436 : Nat.totient 182069100151834653836749686436 = 85679576542039837099646911232 := by
  rw [← show ((([(2, 2), (17, 1), (2677486766938744909363965977, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686436 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_2, prime_oneHundredFiftyFourEV_17, prime_oneHundredFiftyFourEV_2677486766938744909363965977]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686437 : Nat.totient 182069100151834653836749686437 = 176229667013784232902224976000 := by
  rw [← show ((([(41, 1), (127, 1), (2361221, 1), (14808532780755811271, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686437 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_41, prime_oneHundredFiftyFourEV_127, prime_oneHundredFiftyFourEV_2361221, prime_oneHundredFiftyFourEV_14808532780755811271]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686438 : Nat.totient 182069100151834653836749686438 = 60689700048219228108018144000 := by
  rw [← show ((([(2, 1), (3, 7), (25368913001, 1), (1640799851181937, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686438 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_2, prime_oneHundredFiftyFourEV_3, prime_oneHundredFiftyFourEV_25368913001, prime_oneHundredFiftyFourEV_1640799851181937]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686439 : Nat.totient 182069100151834653836749686439 = 176582344608013714868696342976 := by
  rw [← show ((([(37, 1), (313, 1), (15721362589744810796714419, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686439 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_37, prime_oneHundredFiftyFourEV_313, prime_oneHundredFiftyFourEV_15721362589744810796714419]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686440 : Nat.totient 182069100151834653836749686440 = 72827640060463700098122336000 := by
  rw [← show ((([(2, 3), (5, 1), (269575124101, 1), (16884820210972061, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686440 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_2, prime_oneHundredFiftyFourEV_5, prime_oneHundredFiftyFourEV_269575124101, prime_oneHundredFiftyFourEV_16884820210972061]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686441 : Nat.totient 182069100151834653836749686441 = 121368234615461513286720804864 := by
  rw [← show ((([(3, 1), (15817, 1), (35879, 1), (1116593, 1), (95775768498253, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686441 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_3, prime_oneHundredFiftyFourEV_15817, prime_oneHundredFiftyFourEV_35879, prime_oneHundredFiftyFourEV_1116593, prime_oneHundredFiftyFourEV_95775768498253]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686442 : Nat.totient 182069100151834653836749686442 = 78029614336415626060102338552 := by
  rw [← show ((([(2, 1), (7, 4), (5429792839, 1), (6982819718723939, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686442 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_2, prime_oneHundredFiftyFourEV_7, prime_oneHundredFiftyFourEV_5429792839, prime_oneHundredFiftyFourEV_6982819718723939]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686443 : Nat.totient 182069100151834653836749686443 = 181906099840249046731207314720 := by
  rw [← show ((([(1117, 1), (90391069, 1), (1803256681820524691, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686443 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_1117, prime_oneHundredFiftyFourEV_90391069, prime_oneHundredFiftyFourEV_1803256681820524691]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686444 : Nat.totient 182069100151834653836749686444 = 48714140508852081294113617920 := by
  rw [← show ((([(2, 2), (3, 1), (11, 1), (13, 1), (23, 1), (4613081487580689516488033, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686444 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_2, prime_oneHundredFiftyFourEV_3, prime_oneHundredFiftyFourEV_11, prime_oneHundredFiftyFourEV_13, prime_oneHundredFiftyFourEV_23, prime_oneHundredFiftyFourEV_4613081487580689516488033]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686445 : Nat.totient 182069100151834653836749686445 = 142267948023284227419046531200 := by
  rw [← show ((([(5, 1), (43, 1), (60918052201, 1), (13901183530423523, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686445 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_5, prime_oneHundredFiftyFourEV_43, prime_oneHundredFiftyFourEV_60918052201, prime_oneHundredFiftyFourEV_13901183530423523]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686446 : Nat.totient 182069100151834653836749686446 = 91034528940142706662490945160 := by
  rw [← show ((([(2, 1), (4307131, 1), (21135774620255879590933, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686446 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_2, prime_oneHundredFiftyFourEV_4307131, prime_oneHundredFiftyFourEV_21135774620255879590933]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686447 : Nat.totient 182069100151834653836749686447 = 120265827498623490423962459328 := by
  rw [← show ((([(3, 2), (109, 1), (965163109, 1), (192294350320855543, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686447 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_3, prime_oneHundredFiftyFourEV_109, prime_oneHundredFiftyFourEV_965163109, prime_oneHundredFiftyFourEV_192294350320855543]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686448 : Nat.totient 182069100151834653836749686448 = 91034548747212251672590483584 := by
  rw [← show ((([(2, 4), (68513737, 1), (166088134405654531219, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686448 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_2, prime_oneHundredFiftyFourEV_68513737, prime_oneHundredFiftyFourEV_166088134405654531219]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686449 : Nat.totient 182069100151834653836749686449 = 151025059987494940089189236880 := by
  rw [← show ((([(7, 1), (31, 1), (3262940519, 1), (257138647306974463, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686449 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_7, prime_oneHundredFiftyFourEV_31, prime_oneHundredFiftyFourEV_3262940519, prime_oneHundredFiftyFourEV_257138647306974463]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686450 : Nat.totient 182069100151834653836749686450 = 47445299133913587630089496640 := by
  rw [← show ((([(2, 1), (3, 1), (5, 2), (47, 1), (647, 1), (39915617120333816487827, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686450 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_2, prime_oneHundredFiftyFourEV_3, prime_oneHundredFiftyFourEV_5, prime_oneHundredFiftyFourEV_47, prime_oneHundredFiftyFourEV_647, prime_oneHundredFiftyFourEV_39915617120333816487827]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686451 : Nat.totient 182069100151834653836749686451 = 181186522232481908349043200000 := by
  rw [← show ((([(251, 1), (1213, 1), (23531, 1), (69758081, 1), (364306411607, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686451 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_251, prime_oneHundredFiftyFourEV_1213, prime_oneHundredFiftyFourEV_23531, prime_oneHundredFiftyFourEV_69758081, prime_oneHundredFiftyFourEV_364306411607]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686452 : Nat.totient 182069100151834653836749686452 = 91034550075917326918374843224 := by
  rw [← show ((([(2, 2), (45517275037958663459187421613, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686452 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_2, prime_oneHundredFiftyFourEV_45517275037958663459187421613]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686453 : Nat.totient 182069100151834653836749686453 = 114239435376095105252590745856 := by
  rw [← show ((([(3, 1), (17, 1), (8595025147, 1), (415354498080135349, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686453 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_3, prime_oneHundredFiftyFourEV_17, prime_oneHundredFiftyFourEV_8595025147, prime_oneHundredFiftyFourEV_415354498080135349]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686454 : Nat.totient 182069100151834653836749686454 = 85204182569469863368117480200 := by
  rw [← show ((([(2, 1), (19, 1), (83, 1), (57726410954925381685716451, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686454 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_2, prime_oneHundredFiftyFourEV_19, prime_oneHundredFiftyFourEV_83, prime_oneHundredFiftyFourEV_57726410954925381685716451]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686455 : Nat.totient 182069100151834653836749686455 = 128827633268681759733505167360 := by
  rw [← show ((([(5, 1), (11, 1), (59, 2), (97, 1), (9803875754057824351433, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686455 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_5, prime_oneHundredFiftyFourEV_11, prime_oneHundredFiftyFourEV_59, prime_oneHundredFiftyFourEV_97, prime_oneHundredFiftyFourEV_9803875754057824351433]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686456 : Nat.totient 182069100151834653836749686456 = 51533575880619876138889678080 := by
  rw [← show ((([(2, 3), (3, 2), (7, 1), (107, 1), (43001837, 1), (78511797954027271, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686456 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_2, prime_oneHundredFiftyFourEV_3, prime_oneHundredFiftyFourEV_7, prime_oneHundredFiftyFourEV_107, prime_oneHundredFiftyFourEV_43001837, prime_oneHundredFiftyFourEV_78511797954027271]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686457 : Nat.totient 182069100151834653836749686457 = 167667540092931713436961388544 := by
  rw [← show ((([(13, 1), (593, 1), (1487, 1), (400915547, 1), (39616338480857, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686457 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_13, prime_oneHundredFiftyFourEV_593, prime_oneHundredFiftyFourEV_1487, prime_oneHundredFiftyFourEV_400915547, prime_oneHundredFiftyFourEV_39616338480857]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686458 : Nat.totient 182069100151834653836749686458 = 91020156857566961225956608000 := by
  rw [← show ((([(2, 1), (9011, 1), (24151, 1), (184409, 1), (3258569, 1), (696128009, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686458 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_2, prime_oneHundredFiftyFourEV_9011, prime_oneHundredFiftyFourEV_24151, prime_oneHundredFiftyFourEV_184409, prime_oneHundredFiftyFourEV_3258569, prime_oneHundredFiftyFourEV_696128009]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686459 : Nat.totient 182069100151834653836749686459 = 121259563738121704544299055328 := by
  rw [← show ((([(3, 1), (1013, 1), (8279743, 1), (7235835567010375067, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686459 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_3, prime_oneHundredFiftyFourEV_1013, prime_oneHundredFiftyFourEV_8279743, prime_oneHundredFiftyFourEV_7235835567010375067]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686460 : Nat.totient 182069100151834653836749686460 = 71787157961907851865968014400 := by
  rw [← show ((([(2, 2), (5, 1), (71, 1), (4871, 1), (26322659856962398014803, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686460 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_2, prime_oneHundredFiftyFourEV_5, prime_oneHundredFiftyFourEV_71, prime_oneHundredFiftyFourEV_4871, prime_oneHundredFiftyFourEV_26322659856962398014803]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686461 : Nat.totient 182069100151834653836749686461 = 182069100151786779264494170812 := by
  rw [← show ((([(3803346056467, 1), (47870768909459183, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686461 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_3803346056467, prime_oneHundredFiftyFourEV_47870768909459183]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686462 : Nat.totient 182069100151834653836749686462 = 60689699892413487021417868320 := by
  rw [← show ((([(2, 1), (3, 1), (430899863, 1), (4505031589, 1), (15631865111, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686462 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_2, prime_oneHundredFiftyFourEV_3, prime_oneHundredFiftyFourEV_430899863, prime_oneHundredFiftyFourEV_4505031589, prime_oneHundredFiftyFourEV_15631865111]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686463 : Nat.totient 182069100151834653836749686463 = 156020417652165737559139756800 := by
  rw [← show ((([(7, 1), (4021, 1), (700722673081, 1), (9231195796909, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686463 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_7, prime_oneHundredFiftyFourEV_4021, prime_oneHundredFiftyFourEV_700722673081, prime_oneHundredFiftyFourEV_9231195796909]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686464 : Nat.totient 182069100151834653836749686464 = 87038687537087233561232962560 := by
  rw [← show ((([(2, 6), (29, 1), (103, 1), (25703, 1), (37054182226033811591, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686464 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_2, prime_oneHundredFiftyFourEV_29, prime_oneHundredFiftyFourEV_103, prime_oneHundredFiftyFourEV_25703, prime_oneHundredFiftyFourEV_37054182226033811591]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686465 : Nat.totient 182069100151834653836749686465 = 95287217077132366126579200000 := by
  rw [← show ((([(3, 3), (5, 1), (101, 1), (113, 1), (23431, 1), (1758386051, 1), (2868121903, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686465 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_3, prime_oneHundredFiftyFourEV_5, prime_oneHundredFiftyFourEV_101, prime_oneHundredFiftyFourEV_113, prime_oneHundredFiftyFourEV_23431, prime_oneHundredFiftyFourEV_1758386051, prime_oneHundredFiftyFourEV_2868121903]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686466 : Nat.totient 182069100151834653836749686466 = 82758679513080985369803888880 := by
  rw [← show ((([(2, 1), (11, 1), (34858727, 1), (237411658455564283589, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686466 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_2, prime_oneHundredFiftyFourEV_11, prime_oneHundredFiftyFourEV_34858727, prime_oneHundredFiftyFourEV_237411658455564283589]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686467 : Nat.totient 182069100151834653836749686467 = 174153052253184609676607867848 := by
  rw [← show ((([(23, 1), (2640219503, 1), (2998253676898342043, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686467 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_23, prime_oneHundredFiftyFourEV_2640219503, prime_oneHundredFiftyFourEV_2998253676898342043]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686468 : Nat.totient 182069100151834653836749686468 = 60371745494067852547182480000 := by
  rw [← show ((([(2, 2), (3, 1), (191, 1), (291751, 1), (119285167, 1), (2282563331837, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686468 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_2, prime_oneHundredFiftyFourEV_3, prime_oneHundredFiftyFourEV_191, prime_oneHundredFiftyFourEV_291751, prime_oneHundredFiftyFourEV_119285167, prime_oneHundredFiftyFourEV_2282563331837]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686469 : Nat.totient 182069100151834653836749686469 = 180952111807344870684376988844 := by
  rw [← show ((([(163, 1), (1116988344489783152372697463, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686469 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_163, prime_oneHundredFiftyFourEV_1116988344489783152372697463]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686470 : Nat.totient 182069100151834653836749686470 = 54225203054159196825836083200 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (13, 1), (17, 1), (7591, 1), (1550411355806685423811, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686470 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_2, prime_oneHundredFiftyFourEV_5, prime_oneHundredFiftyFourEV_7, prime_oneHundredFiftyFourEV_13, prime_oneHundredFiftyFourEV_17, prime_oneHundredFiftyFourEV_7591, prime_oneHundredFiftyFourEV_1550411355806685423811]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686471 : Nat.totient 182069100151834653836749686471 = 121024035852353665422619130880 := by
  rw [← show ((([(3, 1), (373, 1), (4073, 1), (527981, 1), (75661240059006293, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686471 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_3, prime_oneHundredFiftyFourEV_373, prime_oneHundredFiftyFourEV_4073, prime_oneHundredFiftyFourEV_527981, prime_oneHundredFiftyFourEV_75661240059006293]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686472 : Nat.totient 182069100151834653836749686472 = 90996444361721070547404208128 := by
  rw [← show ((([(2, 3), (2389, 1), (191606627809, 1), (49718679039509, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686472 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_2, prime_oneHundredFiftyFourEV_2389, prime_oneHundredFiftyFourEV_191606627809, prime_oneHundredFiftyFourEV_49718679039509]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686473 : Nat.totient 182069100151834653836749686473 = 172486515933317040476920755588 := by
  rw [← show ((([(19, 1), (9582584218517613359828930867, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686473 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_19, prime_oneHundredFiftyFourEV_9582584218517613359828930867]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686474 : Nat.totient 182069100151834653836749686474 = 60667939456768262763293988960 := by
  rw [← show ((([(2, 1), (3, 2), (2789, 1), (283812547, 1), (12778610572777171, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686474 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_2, prime_oneHundredFiftyFourEV_3, prime_oneHundredFiftyFourEV_2789, prime_oneHundredFiftyFourEV_283812547, prime_oneHundredFiftyFourEV_12778610572777171]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686475 : Nat.totient 182069100151834653836749686475 = 145654264528832706316225617600 := by
  rw [← show ((([(5, 2), (143419, 1), (50779631750837658563161, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686475 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_5, prime_oneHundredFiftyFourEV_143419, prime_oneHundredFiftyFourEV_50779631750837658563161]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686476 : Nat.totient 182069100151834653836749686476 = 87898018228861788730760103360 := by
  rw [← show ((([(2, 2), (37, 1), (131, 1), (9390813913339934693457277, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686476 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_2, prime_oneHundredFiftyFourEV_37, prime_oneHundredFiftyFourEV_131, prime_oneHundredFiftyFourEV_9390813913339934693457277]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686477 : Nat.totient 182069100151834653836749686477 = 94374836819425221615059328000 := by
  rw [← show ((([(3, 1), (7, 1), (11, 2), (461, 1), (69997, 1), (2220502305087140441, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686477 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_3, prime_oneHundredFiftyFourEV_7, prime_oneHundredFiftyFourEV_11, prime_oneHundredFiftyFourEV_461, prime_oneHundredFiftyFourEV_69997, prime_oneHundredFiftyFourEV_2220502305087140441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686478 : Nat.totient 182069100151834653836749686478 = 88814085204957423438809149440 := by
  rw [← show ((([(2, 1), (41, 1), (807523, 1), (12382161317, 1), (222060357569, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686478 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_2, prime_oneHundredFiftyFourEV_41, prime_oneHundredFiftyFourEV_807523, prime_oneHundredFiftyFourEV_12382161317, prime_oneHundredFiftyFourEV_222060357569]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686479 : Nat.totient 182069100151834653836749686479 = 181838859574142735694600773760 := by
  rw [← show ((([(1483, 1), (1693, 1), (72516717383281304613041, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686479 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_1483, prime_oneHundredFiftyFourEV_1693, prime_oneHundredFiftyFourEV_72516717383281304613041]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686480 : Nat.totient 182069100151834653836749686480 = 46985574232731523570774110720 := by
  rw [← show ((([(2, 4), (3, 1), (5, 1), (31, 1), (24471653246214335193111517, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686480 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_2, prime_oneHundredFiftyFourEV_3, prime_oneHundredFiftyFourEV_5, prime_oneHundredFiftyFourEV_31, prime_oneHundredFiftyFourEV_24471653246214335193111517]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686481 : Nat.totient 182069100151834653836749686481 = 182041667712456646506052565232 := by
  rw [← show ((([(6637, 1), (27432439378007330697114613, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686481 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_6637, prime_oneHundredFiftyFourEV_27432439378007330697114613]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686482 : Nat.totient 182069100151834653836749686482 = 89787313352546777154970151712 := by
  rw [← show ((([(2, 1), (73, 1), (477359, 1), (2612391577778882735663, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686482 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_2, prime_oneHundredFiftyFourEV_73, prime_oneHundredFiftyFourEV_477359, prime_oneHundredFiftyFourEV_2612391577778882735663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686483 : Nat.totient 182069100151834653836749686483 = 112042493718200417065820253120 := by
  rw [← show ((([(3, 2), (13, 1), (3804221, 1), (409057769026532877619, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686483 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_3, prime_oneHundredFiftyFourEV_13, prime_oneHundredFiftyFourEV_3804221, prime_oneHundredFiftyFourEV_409057769026532877619]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686484 : Nat.totient 182069100151834653836749686484 = 78029614350786280215749865624 := by
  rw [← show ((([(2, 2), (7, 1), (6502467862565523351312488803, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686484 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_2, prime_oneHundredFiftyFourEV_7, prime_oneHundredFiftyFourEV_6502467862565523351312488803]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686485 : Nat.totient 182069100151834653836749686485 = 144563149040832787525958369280 := by
  rw [← show ((([(5, 1), (257, 1), (317, 1), (2137, 1), (20303441, 1), (10301481476189, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686485 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_5, prime_oneHundredFiftyFourEV_257, prime_oneHundredFiftyFourEV_317, prime_oneHundredFiftyFourEV_2137, prime_oneHundredFiftyFourEV_20303441, prime_oneHundredFiftyFourEV_10301481476189]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686486 : Nat.totient 182069100151834653836749686486 = 59882506417059856371269843712 := by
  rw [← show ((([(2, 1), (3, 1), (89, 1), (479, 1), (6198299, 1), (114838352397056749, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686486 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_2, prime_oneHundredFiftyFourEV_3, prime_oneHundredFiftyFourEV_89, prime_oneHundredFiftyFourEV_479, prime_oneHundredFiftyFourEV_6198299, prime_oneHundredFiftyFourEV_114838352397056749]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686487 : Nat.totient 182069100151834653836749686487 = 168125961516408244012477911552 := by
  rw [← show ((([(17, 1), (53, 1), (3811123921159, 1), (53022278245693, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686487 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_17, prime_oneHundredFiftyFourEV_53, prime_oneHundredFiftyFourEV_3811123921159, prime_oneHundredFiftyFourEV_53022278245693]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686488 : Nat.totient 182069100151834653836749686488 = 80834040029667401939356876800 := by
  rw [← show ((([(2, 3), (11, 1), (43, 1), (4282273, 1), (32701811, 1), (343588771969, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686488 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_2, prime_oneHundredFiftyFourEV_11, prime_oneHundredFiftyFourEV_43, prime_oneHundredFiftyFourEV_4282273, prime_oneHundredFiftyFourEV_32701811, prime_oneHundredFiftyFourEV_343588771969]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686489 : Nat.totient 182069100151834653836749686489 = 120666291165046140832833076800 := by
  rw [← show ((([(3, 1), (211, 1), (877, 1), (1159259, 1), (282912714780561631, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686489 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_3, prime_oneHundredFiftyFourEV_211, prime_oneHundredFiftyFourEV_877, prime_oneHundredFiftyFourEV_1159259, prime_oneHundredFiftyFourEV_282912714780561631]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686490 : Nat.totient 182069100151834653836749686490 = 69559325109338499391709491200 := by
  rw [← show ((([(2, 1), (5, 1), (23, 1), (797, 1), (4801, 1), (206879940390097086379, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686490 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_2, prime_oneHundredFiftyFourEV_5, prime_oneHundredFiftyFourEV_23, prime_oneHundredFiftyFourEV_797, prime_oneHundredFiftyFourEV_4801, prime_oneHundredFiftyFourEV_206879940390097086379]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686491 : Nat.totient 182069100151834653836749686491 = 153500463245892100396138053120 := by
  rw [← show ((([(7, 2), (61, 1), (368873, 1), (117238469, 1), (1408520993987, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686491 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_7, prime_oneHundredFiftyFourEV_61, prime_oneHundredFiftyFourEV_368873, prime_oneHundredFiftyFourEV_117238469, prime_oneHundredFiftyFourEV_1408520993987]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686492 : Nat.totient 182069100151834653836749686492 = 57242221146739575841092497856 := by
  rw [← show ((([(2, 2), (3, 3), (19, 1), (227, 1), (390870624021765922655773, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686492 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_2, prime_oneHundredFiftyFourEV_3, prime_oneHundredFiftyFourEV_19, prime_oneHundredFiftyFourEV_227, prime_oneHundredFiftyFourEV_390870624021765922655773]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686493 : Nat.totient 182069100151834653836749686493 = 175790134986562065450841069696 := by
  rw [← show ((([(29, 1), (244043, 1), (36476141627, 1), (705282323897, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686493 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_29, prime_oneHundredFiftyFourEV_244043, prime_oneHundredFiftyFourEV_36476141627, prime_oneHundredFiftyFourEV_705282323897]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686494 : Nat.totient 182069100151834653836749686494 = 91032862961148699887226866520 := by
  rw [← show ((([(2, 1), (53959, 1), (10326046771, 1), (163383528046723, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686494 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_2, prime_oneHundredFiftyFourEV_53959, prime_oneHundredFiftyFourEV_10326046771, prime_oneHundredFiftyFourEV_163383528046723]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686495 : Nat.totient 182069100151834653836749686495 = 97103520080975875328355432960 := by
  rw [← show ((([(3, 1), (5, 1), (42899271839561, 1), (282940467043753, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686495 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_3, prime_oneHundredFiftyFourEV_5, prime_oneHundredFiftyFourEV_42899271839561, prime_oneHundredFiftyFourEV_282940467043753]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686496 : Nat.totient 182069100151834653836749686496 = 84029972828526347023578562560 := by
  rw [← show ((([(2, 5), (13, 1), (43777, 1), (17655048491, 1), (566275802233, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686496 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_2, prime_oneHundredFiftyFourEV_13, prime_oneHundredFiftyFourEV_43777, prime_oneHundredFiftyFourEV_17655048491, prime_oneHundredFiftyFourEV_566275802233]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686497 : Nat.totient 182069100151834653836749686497 = 178195289510306256946606076100 := by
  rw [← show ((([(47, 1), (3873810641528396890143610351, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686497 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_47, prime_oneHundredFiftyFourEV_3873810641528396890143610351]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686498 : Nat.totient 182069100151834653836749686498 = 51361264104089020493821561152 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (79, 1), (49471423, 1), (1109188763774599357, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686498 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_2, prime_oneHundredFiftyFourEV_3, prime_oneHundredFiftyFourEV_7, prime_oneHundredFiftyFourEV_79, prime_oneHundredFiftyFourEV_49471423, prime_oneHundredFiftyFourEV_1109188763774599357]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686499 : Nat.totient 182069100151834653836749686499 = 165407822170308842604832441800 := by
  rw [← show ((([(11, 1), (1511, 1), (10954160408629724675816719, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686499 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_11, prime_oneHundredFiftyFourEV_1511, prime_oneHundredFiftyFourEV_10954160408629724675816719]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686500 : Nat.totient 182069100151834653836749686500 = 71245042874575539718945996800 := by
  rw [← show ((([(2, 2), (5, 3), (67, 1), (157, 1), (1889, 1), (76249, 1), (240339789298547, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686500 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_2, prime_oneHundredFiftyFourEV_5, prime_oneHundredFiftyFourEV_67, prime_oneHundredFiftyFourEV_157, prime_oneHundredFiftyFourEV_1889, prime_oneHundredFiftyFourEV_76249, prime_oneHundredFiftyFourEV_240339789298547]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFourEV_182069100151834653836749686501 : Nat.totient 182069100151834653836749686501 = 121379400101223102557833124328 := by
  rw [← show ((([(3, 2), (20229900016870517092972187389, 1)] : List FactorBlock).map factorBlockValue).prod) = 182069100151834653836749686501 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFourEV_3, prime_oneHundredFiftyFourEV_20229900016870517092972187389]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64OneHundredFiftyFourEV : certifiedKill 1 182069100151834653836749686399 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_oneHundredFiftyFourEV_182069100151834653836749686400, phi_oneHundredFiftyFourEV_182069100151834653836749686401, phi_oneHundredFiftyFourEV_182069100151834653836749686402,
    phi_oneHundredFiftyFourEV_182069100151834653836749686403, phi_oneHundredFiftyFourEV_182069100151834653836749686404, phi_oneHundredFiftyFourEV_182069100151834653836749686405,
    phi_oneHundredFiftyFourEV_182069100151834653836749686406, phi_oneHundredFiftyFourEV_182069100151834653836749686407, phi_oneHundredFiftyFourEV_182069100151834653836749686408,
    phi_oneHundredFiftyFourEV_182069100151834653836749686409, phi_oneHundredFiftyFourEV_182069100151834653836749686410, phi_oneHundredFiftyFourEV_182069100151834653836749686411,
    phi_oneHundredFiftyFourEV_182069100151834653836749686412, phi_oneHundredFiftyFourEV_182069100151834653836749686413, phi_oneHundredFiftyFourEV_182069100151834653836749686414,
    phi_oneHundredFiftyFourEV_182069100151834653836749686415, phi_oneHundredFiftyFourEV_182069100151834653836749686416, phi_oneHundredFiftyFourEV_182069100151834653836749686417,
    phi_oneHundredFiftyFourEV_182069100151834653836749686418, phi_oneHundredFiftyFourEV_182069100151834653836749686419, phi_oneHundredFiftyFourEV_182069100151834653836749686420,
    phi_oneHundredFiftyFourEV_182069100151834653836749686421, phi_oneHundredFiftyFourEV_182069100151834653836749686422, phi_oneHundredFiftyFourEV_182069100151834653836749686423,
    phi_oneHundredFiftyFourEV_182069100151834653836749686424, phi_oneHundredFiftyFourEV_182069100151834653836749686425, phi_oneHundredFiftyFourEV_182069100151834653836749686426,
    phi_oneHundredFiftyFourEV_182069100151834653836749686427, phi_oneHundredFiftyFourEV_182069100151834653836749686428, phi_oneHundredFiftyFourEV_182069100151834653836749686429,
    phi_oneHundredFiftyFourEV_182069100151834653836749686430, phi_oneHundredFiftyFourEV_182069100151834653836749686431, phi_oneHundredFiftyFourEV_182069100151834653836749686432,
    phi_oneHundredFiftyFourEV_182069100151834653836749686433, phi_oneHundredFiftyFourEV_182069100151834653836749686434, phi_oneHundredFiftyFourEV_182069100151834653836749686435,
    phi_oneHundredFiftyFourEV_182069100151834653836749686436, phi_oneHundredFiftyFourEV_182069100151834653836749686437, phi_oneHundredFiftyFourEV_182069100151834653836749686438,
    phi_oneHundredFiftyFourEV_182069100151834653836749686439, phi_oneHundredFiftyFourEV_182069100151834653836749686440, phi_oneHundredFiftyFourEV_182069100151834653836749686441,
    phi_oneHundredFiftyFourEV_182069100151834653836749686442, phi_oneHundredFiftyFourEV_182069100151834653836749686443, phi_oneHundredFiftyFourEV_182069100151834653836749686444,
    phi_oneHundredFiftyFourEV_182069100151834653836749686445, phi_oneHundredFiftyFourEV_182069100151834653836749686446, phi_oneHundredFiftyFourEV_182069100151834653836749686447,
    phi_oneHundredFiftyFourEV_182069100151834653836749686448, phi_oneHundredFiftyFourEV_182069100151834653836749686449, phi_oneHundredFiftyFourEV_182069100151834653836749686450,
    phi_oneHundredFiftyFourEV_182069100151834653836749686451, phi_oneHundredFiftyFourEV_182069100151834653836749686452, phi_oneHundredFiftyFourEV_182069100151834653836749686453,
    phi_oneHundredFiftyFourEV_182069100151834653836749686454, phi_oneHundredFiftyFourEV_182069100151834653836749686455, phi_oneHundredFiftyFourEV_182069100151834653836749686456,
    phi_oneHundredFiftyFourEV_182069100151834653836749686457, phi_oneHundredFiftyFourEV_182069100151834653836749686458, phi_oneHundredFiftyFourEV_182069100151834653836749686459,
    phi_oneHundredFiftyFourEV_182069100151834653836749686460, phi_oneHundredFiftyFourEV_182069100151834653836749686461, phi_oneHundredFiftyFourEV_182069100151834653836749686462,
    phi_oneHundredFiftyFourEV_182069100151834653836749686463, phi_oneHundredFiftyFourEV_182069100151834653836749686464, phi_oneHundredFiftyFourEV_182069100151834653836749686465,
    phi_oneHundredFiftyFourEV_182069100151834653836749686466, phi_oneHundredFiftyFourEV_182069100151834653836749686467, phi_oneHundredFiftyFourEV_182069100151834653836749686468,
    phi_oneHundredFiftyFourEV_182069100151834653836749686469, phi_oneHundredFiftyFourEV_182069100151834653836749686470, phi_oneHundredFiftyFourEV_182069100151834653836749686471,
    phi_oneHundredFiftyFourEV_182069100151834653836749686472, phi_oneHundredFiftyFourEV_182069100151834653836749686473, phi_oneHundredFiftyFourEV_182069100151834653836749686474,
    phi_oneHundredFiftyFourEV_182069100151834653836749686475, phi_oneHundredFiftyFourEV_182069100151834653836749686476, phi_oneHundredFiftyFourEV_182069100151834653836749686477,
    phi_oneHundredFiftyFourEV_182069100151834653836749686478, phi_oneHundredFiftyFourEV_182069100151834653836749686479, phi_oneHundredFiftyFourEV_182069100151834653836749686480,
    phi_oneHundredFiftyFourEV_182069100151834653836749686481, phi_oneHundredFiftyFourEV_182069100151834653836749686482, phi_oneHundredFiftyFourEV_182069100151834653836749686483,
    phi_oneHundredFiftyFourEV_182069100151834653836749686484, phi_oneHundredFiftyFourEV_182069100151834653836749686485, phi_oneHundredFiftyFourEV_182069100151834653836749686486,
    phi_oneHundredFiftyFourEV_182069100151834653836749686487, phi_oneHundredFiftyFourEV_182069100151834653836749686488, phi_oneHundredFiftyFourEV_182069100151834653836749686489,
    phi_oneHundredFiftyFourEV_182069100151834653836749686490, phi_oneHundredFiftyFourEV_182069100151834653836749686491, phi_oneHundredFiftyFourEV_182069100151834653836749686492,
    phi_oneHundredFiftyFourEV_182069100151834653836749686493, phi_oneHundredFiftyFourEV_182069100151834653836749686494, phi_oneHundredFiftyFourEV_182069100151834653836749686495,
    phi_oneHundredFiftyFourEV_182069100151834653836749686496, phi_oneHundredFiftyFourEV_182069100151834653836749686497, phi_oneHundredFiftyFourEV_182069100151834653836749686498,
    phi_oneHundredFiftyFourEV_182069100151834653836749686499, phi_oneHundredFiftyFourEV_182069100151834653836749686500, phi_oneHundredFiftyFourEV_182069100151834653836749686501
    ]

end TotientTailPeriodKiller
end Erdos249257
