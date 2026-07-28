import Erdos249257.DiagonalPincerCertificatesT64

/- Kernel-checked off-diagonal certificate at a freely chosen position. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def oneHundredFortyFourELFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem oneHundredFortyFourELFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : oneHundredFortyFourELFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [oneHundredFortyFourELFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [oneHundredFortyFourELFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then oneHundredFortyFourELFastPow a n * oneHundredFortyFourELFastPow a n * a else oneHundredFortyFourELFastPow a n * oneHundredFortyFourELFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_oneHundredFortyFourEL_2 : Nat.Prime 2 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_3 : Nat.Prime 3 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_5 : Nat.Prime 5 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_7 : Nat.Prime 7 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_11 : Nat.Prime 11 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_13 : Nat.Prime 13 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_17 : Nat.Prime 17 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_19 : Nat.Prime 19 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_23 : Nat.Prime 23 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_29 : Nat.Prime 29 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_31 : Nat.Prime 31 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_37 : Nat.Prime 37 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_41 : Nat.Prime 41 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_43 : Nat.Prime 43 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_47 : Nat.Prime 47 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_53 : Nat.Prime 53 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_59 : Nat.Prime 59 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_61 : Nat.Prime 61 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_67 : Nat.Prime 67 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_71 : Nat.Prime 71 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_73 : Nat.Prime 73 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_79 : Nat.Prime 79 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_83 : Nat.Prime 83 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_89 : Nat.Prime 89 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_97 : Nat.Prime 97 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_101 : Nat.Prime 101 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_103 : Nat.Prime 103 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_107 : Nat.Prime 107 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_109 : Nat.Prime 109 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_113 : Nat.Prime 113 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_127 : Nat.Prime 127 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_131 : Nat.Prime 131 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_137 : Nat.Prime 137 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_139 : Nat.Prime 139 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_149 : Nat.Prime 149 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_151 : Nat.Prime 151 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_157 : Nat.Prime 157 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_163 : Nat.Prime 163 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_167 : Nat.Prime 167 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_173 : Nat.Prime 173 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_179 : Nat.Prime 179 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_181 : Nat.Prime 181 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_191 : Nat.Prime 191 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_193 : Nat.Prime 193 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_197 : Nat.Prime 197 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_199 : Nat.Prime 199 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_211 : Nat.Prime 211 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_223 : Nat.Prime 223 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_227 : Nat.Prime 227 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_229 : Nat.Prime 229 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_233 : Nat.Prime 233 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_239 : Nat.Prime 239 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_241 : Nat.Prime 241 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_251 : Nat.Prime 251 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_263 : Nat.Prime 263 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_269 : Nat.Prime 269 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_271 : Nat.Prime 271 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_283 : Nat.Prime 283 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_293 : Nat.Prime 293 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_311 : Nat.Prime 311 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_317 : Nat.Prime 317 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_331 : Nat.Prime 331 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_347 : Nat.Prime 347 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_349 : Nat.Prime 349 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_359 : Nat.Prime 359 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_409 : Nat.Prime 409 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_449 : Nat.Prime 449 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_457 : Nat.Prime 457 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_461 : Nat.Prime 461 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_463 : Nat.Prime 463 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_467 : Nat.Prime 467 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_479 : Nat.Prime 479 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_503 : Nat.Prime 503 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_509 : Nat.Prime 509 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_541 : Nat.Prime 541 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_547 : Nat.Prime 547 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_557 : Nat.Prime 557 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_563 : Nat.Prime 563 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_593 : Nat.Prime 593 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_599 : Nat.Prime 599 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_601 : Nat.Prime 601 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_607 : Nat.Prime 607 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_619 : Nat.Prime 619 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_647 : Nat.Prime 647 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_659 : Nat.Prime 659 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_661 : Nat.Prime 661 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_683 : Nat.Prime 683 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_691 : Nat.Prime 691 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_733 : Nat.Prime 733 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_739 : Nat.Prime 739 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_751 : Nat.Prime 751 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_797 : Nat.Prime 797 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_809 : Nat.Prime 809 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_811 : Nat.Prime 811 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_821 : Nat.Prime 821 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_829 : Nat.Prime 829 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_857 : Nat.Prime 857 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_859 : Nat.Prime 859 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_877 : Nat.Prime 877 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_937 : Nat.Prime 937 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_941 : Nat.Prime 941 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_947 : Nat.Prime 947 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_953 : Nat.Prime 953 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_971 : Nat.Prime 971 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_983 : Nat.Prime 983 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_997 : Nat.Prime 997 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_1009 : Nat.Prime 1009 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_1019 : Nat.Prime 1019 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_1051 : Nat.Prime 1051 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_1063 : Nat.Prime 1063 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_1123 : Nat.Prime 1123 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_1151 : Nat.Prime 1151 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_1153 : Nat.Prime 1153 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_1163 : Nat.Prime 1163 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_1171 : Nat.Prime 1171 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_1201 : Nat.Prime 1201 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_1217 : Nat.Prime 1217 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_1249 : Nat.Prime 1249 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_1277 : Nat.Prime 1277 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_1289 : Nat.Prime 1289 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_1301 : Nat.Prime 1301 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_1319 : Nat.Prime 1319 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_1321 : Nat.Prime 1321 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_1381 : Nat.Prime 1381 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_1453 : Nat.Prime 1453 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_1487 : Nat.Prime 1487 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_1489 : Nat.Prime 1489 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_1549 : Nat.Prime 1549 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_1559 : Nat.Prime 1559 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_1583 : Nat.Prime 1583 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_1667 : Nat.Prime 1667 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_1777 : Nat.Prime 1777 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_1811 : Nat.Prime 1811 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_1889 : Nat.Prime 1889 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_1907 : Nat.Prime 1907 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_1993 : Nat.Prime 1993 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_2003 : Nat.Prime 2003 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_2143 : Nat.Prime 2143 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_2179 : Nat.Prime 2179 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_2287 : Nat.Prime 2287 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_2351 : Nat.Prime 2351 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_2377 : Nat.Prime 2377 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_2411 : Nat.Prime 2411 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_2467 : Nat.Prime 2467 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_2503 : Nat.Prime 2503 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_2659 : Nat.Prime 2659 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_2689 : Nat.Prime 2689 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_2791 : Nat.Prime 2791 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_2803 : Nat.Prime 2803 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_2819 : Nat.Prime 2819 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_2903 : Nat.Prime 2903 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_2971 : Nat.Prime 2971 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_3011 : Nat.Prime 3011 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_3067 : Nat.Prime 3067 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_3121 : Nat.Prime 3121 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_3167 : Nat.Prime 3167 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_3347 : Nat.Prime 3347 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_3361 : Nat.Prime 3361 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_3391 : Nat.Prime 3391 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_3413 : Nat.Prime 3413 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_3677 : Nat.Prime 3677 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_3821 : Nat.Prime 3821 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_4051 : Nat.Prime 4051 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_4073 : Nat.Prime 4073 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_4091 : Nat.Prime 4091 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_4177 : Nat.Prime 4177 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_4253 : Nat.Prime 4253 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_4273 : Nat.Prime 4273 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_4391 : Nat.Prime 4391 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_4463 : Nat.Prime 4463 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_4751 : Nat.Prime 4751 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_4861 : Nat.Prime 4861 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_4871 : Nat.Prime 4871 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_4951 : Nat.Prime 4951 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_4993 : Nat.Prime 4993 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_5051 : Nat.Prime 5051 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_5101 : Nat.Prime 5101 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_5179 : Nat.Prime 5179 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_5227 : Nat.Prime 5227 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_5641 : Nat.Prime 5641 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_5651 : Nat.Prime 5651 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_5779 : Nat.Prime 5779 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_5923 : Nat.Prime 5923 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_6011 : Nat.Prime 6011 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_6067 : Nat.Prime 6067 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_6133 : Nat.Prime 6133 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_6323 : Nat.Prime 6323 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_6427 : Nat.Prime 6427 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_6569 : Nat.Prime 6569 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_6863 : Nat.Prime 6863 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_7039 : Nat.Prime 7039 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_7211 : Nat.Prime 7211 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_7411 : Nat.Prime 7411 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_7561 : Nat.Prime 7561 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_7573 : Nat.Prime 7573 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_7877 : Nat.Prime 7877 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_8087 : Nat.Prime 8087 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_8273 : Nat.Prime 8273 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_8677 : Nat.Prime 8677 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_8737 : Nat.Prime 8737 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_8761 : Nat.Prime 8761 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_8819 : Nat.Prime 8819 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_9467 : Nat.Prime 9467 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_10079 : Nat.Prime 10079 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_10337 : Nat.Prime 10337 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_10477 : Nat.Prime 10477 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_10667 : Nat.Prime 10667 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_10789 : Nat.Prime 10789 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_11483 : Nat.Prime 11483 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_12301 : Nat.Prime 12301 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_12919 : Nat.Prime 12919 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_13003 : Nat.Prime 13003 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_13523 : Nat.Prime 13523 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_13627 : Nat.Prime 13627 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_13829 : Nat.Prime 13829 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_13907 : Nat.Prime 13907 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_14033 : Nat.Prime 14033 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_14627 : Nat.Prime 14627 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_15791 : Nat.Prime 15791 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_16249 : Nat.Prime 16249 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_17203 : Nat.Prime 17203 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_17393 : Nat.Prime 17393 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_17539 : Nat.Prime 17539 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_18061 : Nat.Prime 18061 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_18427 : Nat.Prime 18427 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_18691 : Nat.Prime 18691 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_19379 : Nat.Prime 19379 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_19507 : Nat.Prime 19507 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_19751 : Nat.Prime 19751 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_19759 : Nat.Prime 19759 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_20707 : Nat.Prime 20707 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_20753 : Nat.Prime 20753 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_20887 : Nat.Prime 20887 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_21467 : Nat.Prime 21467 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_21617 : Nat.Prime 21617 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_22307 : Nat.Prime 22307 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_22481 : Nat.Prime 22481 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_23417 : Nat.Prime 23417 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_23929 : Nat.Prime 23929 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_24623 : Nat.Prime 24623 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_24841 : Nat.Prime 24841 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_25117 : Nat.Prime 25117 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_25247 : Nat.Prime 25247 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_25343 : Nat.Prime 25343 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_27697 : Nat.Prime 27697 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_28001 : Nat.Prime 28001 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_28163 : Nat.Prime 28163 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_28403 : Nat.Prime 28403 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_29251 : Nat.Prime 29251 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_29437 : Nat.Prime 29437 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_29669 : Nat.Prime 29669 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_29873 : Nat.Prime 29873 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_31177 : Nat.Prime 31177 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_31393 : Nat.Prime 31393 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_31531 : Nat.Prime 31531 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_31573 : Nat.Prime 31573 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_32971 : Nat.Prime 32971 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_33617 : Nat.Prime 33617 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_34757 : Nat.Prime 34757 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_34841 : Nat.Prime 34841 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_38153 : Nat.Prime 38153 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_40213 : Nat.Prime 40213 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_40993 : Nat.Prime 40993 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_41687 : Nat.Prime 41687 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_43133 : Nat.Prime 43133 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_45233 : Nat.Prime 45233 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_45377 : Nat.Prime 45377 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_47713 : Nat.Prime 47713 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_47981 : Nat.Prime 47981 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_48017 : Nat.Prime 48017 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_50593 : Nat.Prime 50593 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_52361 : Nat.Prime 52361 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_53939 : Nat.Prime 53939 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_56923 : Nat.Prime 56923 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_58393 : Nat.Prime 58393 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_60133 : Nat.Prime 60133 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_61027 : Nat.Prime 61027 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_63197 : Nat.Prime 63197 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_63353 : Nat.Prime 63353 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_64817 : Nat.Prime 64817 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_65609 : Nat.Prime 65609 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_66373 : Nat.Prime 66373 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_67933 : Nat.Prime 67933 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_68449 : Nat.Prime 68449 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_69997 : Nat.Prime 69997 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_70583 : Nat.Prime 70583 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_71983 : Nat.Prime 71983 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_74887 : Nat.Prime 74887 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_76487 : Nat.Prime 76487 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_78167 : Nat.Prime 78167 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_79847 : Nat.Prime 79847 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_80489 : Nat.Prime 80489 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_82153 : Nat.Prime 82153 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_84389 : Nat.Prime 84389 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_85621 : Nat.Prime 85621 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_87539 : Nat.Prime 87539 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_87853 : Nat.Prime 87853 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_88873 : Nat.Prime 88873 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_90887 : Nat.Prime 90887 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_91541 : Nat.Prime 91541 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_94823 : Nat.Prime 94823 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_100069 : Nat.Prime 100069 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_101863 : Nat.Prime 101863 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_103573 : Nat.Prime 103573 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_111577 : Nat.Prime 111577 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_113381 : Nat.Prime 113381 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_121661 : Nat.Prime 121661 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_125287 : Nat.Prime 125287 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_130073 : Nat.Prime 130073 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_138799 : Nat.Prime 138799 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_141853 : Nat.Prime 141853 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_150107 : Nat.Prime 150107 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_170603 : Nat.Prime 170603 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_171401 : Nat.Prime 171401 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_182627 : Nat.Prime 182627 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_182653 : Nat.Prime 182653 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_188911 : Nat.Prime 188911 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_191123 : Nat.Prime 191123 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_193381 : Nat.Prime 193381 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_212903 : Nat.Prime 212903 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_221069 : Nat.Prime 221069 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_223283 : Nat.Prime 223283 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_226691 : Nat.Prime 226691 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_230551 : Nat.Prime 230551 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_244261 : Nat.Prime 244261 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_245299 : Nat.Prime 245299 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_246817 : Nat.Prime 246817 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_256643 : Nat.Prime 256643 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_260417 : Nat.Prime 260417 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_272737 : Nat.Prime 272737 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_284833 : Nat.Prime 284833 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_292367 : Nat.Prime 292367 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_314077 : Nat.Prime 314077 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_319427 : Nat.Prime 319427 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_341461 : Nat.Prime 341461 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_361967 : Nat.Prime 361967 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_362027 : Nat.Prime 362027 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_387161 : Nat.Prime 387161 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_400721 : Nat.Prime 400721 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_405373 : Nat.Prime 405373 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_438401 : Nat.Prime 438401 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_460711 : Nat.Prime 460711 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_467371 : Nat.Prime 467371 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_519119 : Nat.Prime 519119 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_555589 : Nat.Prime 555589 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_560969 : Nat.Prime 560969 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_581311 : Nat.Prime 581311 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_590077 : Nat.Prime 590077 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_628921 : Nat.Prime 628921 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_683483 : Nat.Prime 683483 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_776117 : Nat.Prime 776117 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_822011 : Nat.Prime 822011 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_840277 : Nat.Prime 840277 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_923171 : Nat.Prime 923171 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_1068257 : Nat.Prime 1068257 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_1126649 : Nat.Prime 1126649 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_1152937 : Nat.Prime 1152937 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_1154401 : Nat.Prime 1154401 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_1223203 : Nat.Prime 1223203 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_1233371 : Nat.Prime 1233371 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_1245779 : Nat.Prime 1245779 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_1295761 : Nat.Prime 1295761 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_1326859 : Nat.Prime 1326859 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_1536649 : Nat.Prime 1536649 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_1545121 : Nat.Prime 1545121 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_1639493 : Nat.Prime 1639493 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_1743487 : Nat.Prime 1743487 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_1804687 : Nat.Prime 1804687 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_1901651 : Nat.Prime 1901651 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_1910471 : Nat.Prime 1910471 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_2009731 : Nat.Prime 2009731 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_2126771 : Nat.Prime 2126771 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_2155273 : Nat.Prime 2155273 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_2312027 : Nat.Prime 2312027 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_2398259 : Nat.Prime 2398259 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_2487047 : Nat.Prime 2487047 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_2588671 : Nat.Prime 2588671 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_2623979 : Nat.Prime 2623979 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_2755243 : Nat.Prime 2755243 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_3061133 : Nat.Prime 3061133 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_3114833 : Nat.Prime 3114833 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_3165577 : Nat.Prime 3165577 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_3215083 : Nat.Prime 3215083 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_3345961 : Nat.Prime 3345961 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_3594403 : Nat.Prime 3594403 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_3921217 : Nat.Prime 3921217 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_4185953 : Nat.Prime 4185953 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_4438201 : Nat.Prime 4438201 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_4440187 : Nat.Prime 4440187 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_4509047 : Nat.Prime 4509047 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_4517543 : Nat.Prime 4517543 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_4542301 : Nat.Prime 4542301 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_4631477 : Nat.Prime 4631477 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_4830151 : Nat.Prime 4830151 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_4952209 : Nat.Prime 4952209 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_5251819 : Nat.Prime 5251819 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_5281853 : Nat.Prime 5281853 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_5517433 : Nat.Prime 5517433 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_5816549 : Nat.Prime 5816549 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_6062809 : Nat.Prime 6062809 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_6336347 : Nat.Prime 6336347 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_7170469 : Nat.Prime 7170469 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_7524107 : Nat.Prime 7524107 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_7545367 : Nat.Prime 7545367 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_7860731 : Nat.Prime 7860731 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_8761303 : Nat.Prime 8761303 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_9927493 : Nat.Prime 9927493 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_10820141 : Nat.Prime 10820141 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_10895267 : Nat.Prime 10895267 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_10985101 : Nat.Prime 10985101 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_11846617 : Nat.Prime 11846617 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_12255071 : Nat.Prime 12255071 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_12463799 : Nat.Prime 12463799 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_12939811 : Nat.Prime 12939811 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_13048621 : Nat.Prime 13048621 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_13158487 : Nat.Prime 13158487 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_13203719 : Nat.Prime 13203719 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_13511921 : Nat.Prime 13511921 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_14201963 : Nat.Prime 14201963 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_14446457 : Nat.Prime 14446457 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_14600507 : Nat.Prime 14600507 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_14668343 : Nat.Prime 14668343 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_16318037 : Nat.Prime 16318037 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_16591039 : Nat.Prime 16591039 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_19471061 : Nat.Prime 19471061 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_20291147 : Nat.Prime 20291147 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_20386907 : Nat.Prime 20386907 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_21106291 : Nat.Prime 21106291 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_21727217 : Nat.Prime 21727217 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_23303261 : Nat.Prime 23303261 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_25512737 : Nat.Prime 25512737 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_25868083 : Nat.Prime 25868083 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_26655217 : Nat.Prime 26655217 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_26867557 : Nat.Prime 26867557 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_27052327 : Nat.Prime 27052327 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_28738181 : Nat.Prime 28738181 := by
  norm_num

private theorem prime_oneHundredFortyFourEL_35017039 : Nat.Prime 35017039 := by
  apply lucas_primality 35017039 (14 : ZMod 35017039)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (19, 1), (14627, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (19, 1), (14627, 1)] : List FactorBlock).map factorBlockValue).prod) = 35017039 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_7
      · exact prime_oneHundredFortyFourEL_19
      · exact prime_oneHundredFortyFourEL_14627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 35017039) ^ 17508519 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (14 : ZMod 35017039) ^ 11672346 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (14 : ZMod 35017039) ^ 5002434 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (14 : ZMod 35017039) ^ 1843002 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (14 : ZMod 35017039) ^ 2394 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_36908083 : Nat.Prime 36908083 := by
  apply lucas_primality 36908083 (2 : ZMod 36908083)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (683483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (683483, 1)] : List FactorBlock).map factorBlockValue).prod) = 36908083 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_683483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 36908083) ^ 18454041 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 36908083) ^ 12302694 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 36908083) ^ 54 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_37097537 : Nat.Prime 37097537 := by
  apply lucas_primality 37097537 (3 : ZMod 37097537)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (7, 1), (17, 1), (4871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (7, 1), (17, 1), (4871, 1)] : List FactorBlock).map factorBlockValue).prod) = 37097537 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_7
      · exact prime_oneHundredFortyFourEL_17
      · exact prime_oneHundredFortyFourEL_4871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 37097537) ^ 18548768 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 37097537) ^ 5299648 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 37097537) ^ 2182208 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 37097537) ^ 7616 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_37253617 : Nat.Prime 37253617 := by
  apply lucas_primality 37253617 (13 : ZMod 37253617)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (776117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (776117, 1)] : List FactorBlock).map factorBlockValue).prod) = 37253617 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_776117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 37253617) ^ 18626808 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (13 : ZMod 37253617) ^ 12417872 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (13 : ZMod 37253617) ^ 48 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_37721171 : Nat.Prime 37721171 := by
  apply lucas_primality 37721171 (2 : ZMod 37721171)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (29, 1), (130073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (29, 1), (130073, 1)] : List FactorBlock).map factorBlockValue).prod) = 37721171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_5
      · exact prime_oneHundredFortyFourEL_29
      · exact prime_oneHundredFortyFourEL_130073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 37721171) ^ 18860585 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 37721171) ^ 7544234 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 37721171) ^ 1300730 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 37721171) ^ 290 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_37958111 : Nat.Prime 37958111 := by
  apply lucas_primality 37958111 (7 : ZMod 37958111)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (223283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (223283, 1)] : List FactorBlock).map factorBlockValue).prod) = 37958111 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_5
      · exact prime_oneHundredFortyFourEL_17
      · exact prime_oneHundredFortyFourEL_223283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 37958111) ^ 18979055 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (7 : ZMod 37958111) ^ 7591622 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (7 : ZMod 37958111) ^ 2232830 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (7 : ZMod 37958111) ^ 170 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_38879033 : Nat.Prime 38879033 := by
  apply lucas_primality 38879033 (3 : ZMod 38879033)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (71, 1), (68449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (71, 1), (68449, 1)] : List FactorBlock).map factorBlockValue).prod) = 38879033 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_71
      · exact prime_oneHundredFortyFourEL_68449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 38879033) ^ 19439516 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 38879033) ^ 547592 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 38879033) ^ 568 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_39709973 : Nat.Prime 39709973 := by
  apply lucas_primality 39709973 (2 : ZMod 39709973)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (9927493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (9927493, 1)] : List FactorBlock).map factorBlockValue).prod) = 39709973 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_9927493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 39709973) ^ 19854986 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 39709973) ^ 4 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_45994279 : Nat.Prime 45994279 := by
  apply lucas_primality 45994279 (3 : ZMod 45994279)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 2), (63353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 2), (63353, 1)] : List FactorBlock).map factorBlockValue).prod) = 45994279 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_11
      · exact prime_oneHundredFortyFourEL_63353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 45994279) ^ 22997139 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 45994279) ^ 15331426 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 45994279) ^ 4181298 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 45994279) ^ 726 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_46501019 : Nat.Prime 46501019 := by
  apply lucas_primality 46501019 (2 : ZMod 46501019)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (19, 1), (71983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (19, 1), (71983, 1)] : List FactorBlock).map factorBlockValue).prod) = 46501019 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_17
      · exact prime_oneHundredFortyFourEL_19
      · exact prime_oneHundredFortyFourEL_71983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 46501019) ^ 23250509 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 46501019) ^ 2735354 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 46501019) ^ 2447422 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 46501019) ^ 646 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_49344241 : Nat.Prime 49344241 := by
  apply lucas_primality 49344241 (13 : ZMod 49344241)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (11, 1), (18691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (11, 1), (18691, 1)] : List FactorBlock).map factorBlockValue).prod) = 49344241 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_5
      · exact prime_oneHundredFortyFourEL_11
      · exact prime_oneHundredFortyFourEL_18691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 49344241) ^ 24672120 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (13 : ZMod 49344241) ^ 16448080 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (13 : ZMod 49344241) ^ 9868848 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (13 : ZMod 49344241) ^ 4485840 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (13 : ZMod 49344241) ^ 2640 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_51292289 : Nat.Prime 51292289 := by
  apply lucas_primality 51292289 (3 : ZMod 51292289)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (400721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (400721, 1)] : List FactorBlock).map factorBlockValue).prod) = 51292289 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_400721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 51292289) ^ 25646144 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 51292289) ^ 128 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_59929613 : Nat.Prime 59929613 := by
  apply lucas_primality 59929613 (2 : ZMod 59929613)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1811, 1), (8273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1811, 1), (8273, 1)] : List FactorBlock).map factorBlockValue).prod) = 59929613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_1811
      · exact prime_oneHundredFortyFourEL_8273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 59929613) ^ 29964806 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 59929613) ^ 33092 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 59929613) ^ 7244 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_61405583 : Nat.Prime 61405583 := by
  apply lucas_primality 61405583 (5 : ZMod 61405583)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (149, 1), (29437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (149, 1), (29437, 1)] : List FactorBlock).map factorBlockValue).prod) = 61405583 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_7
      · exact prime_oneHundredFortyFourEL_149
      · exact prime_oneHundredFortyFourEL_29437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 61405583) ^ 30702791 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 61405583) ^ 8772226 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 61405583) ^ 412118 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 61405583) ^ 2086 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_62739473 : Nat.Prime 62739473 := by
  apply lucas_primality 62739473 (3 : ZMod 62739473)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3921217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3921217, 1)] : List FactorBlock).map factorBlockValue).prod) = 62739473 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3921217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 62739473) ^ 31369736 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 62739473) ^ 16 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_67305671 : Nat.Prime 67305671 := by
  apply lucas_primality 67305671 (11 : ZMod 67305671)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (2503, 1), (2689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (2503, 1), (2689, 1)] : List FactorBlock).map factorBlockValue).prod) = 67305671 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_5
      · exact prime_oneHundredFortyFourEL_2503
      · exact prime_oneHundredFortyFourEL_2689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 67305671) ^ 33652835 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (11 : ZMod 67305671) ^ 13461134 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (11 : ZMod 67305671) ^ 26890 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (11 : ZMod 67305671) ^ 25030 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_70496453 : Nat.Prime 70496453 := by
  apply lucas_primality 70496453 (2 : ZMod 70496453)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (467, 1), (2903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (467, 1), (2903, 1)] : List FactorBlock).map factorBlockValue).prod) = 70496453 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_13
      · exact prime_oneHundredFortyFourEL_467
      · exact prime_oneHundredFortyFourEL_2903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 70496453) ^ 35248226 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 70496453) ^ 5422804 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 70496453) ^ 150956 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 70496453) ^ 24284 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_92103133 : Nat.Prime 92103133 := by
  apply lucas_primality 92103133 (5 : ZMod 92103133)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (23, 2), (1319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (23, 2), (1319, 1)] : List FactorBlock).map factorBlockValue).prod) = 92103133 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_11
      · exact prime_oneHundredFortyFourEL_23
      · exact prime_oneHundredFortyFourEL_1319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 92103133) ^ 46051566 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 92103133) ^ 30701044 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 92103133) ^ 8373012 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 92103133) ^ 4004484 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 92103133) ^ 69828 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_98506729 : Nat.Prime 98506729 := by
  apply lucas_primality 98506729 (7 : ZMod 98506729)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (37, 1), (103, 1), (359, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (37, 1), (103, 1), (359, 1)] : List FactorBlock).map factorBlockValue).prod) = 98506729 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_37
      · exact prime_oneHundredFortyFourEL_103
      · exact prime_oneHundredFortyFourEL_359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 98506729) ^ 49253364 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (7 : ZMod 98506729) ^ 32835576 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (7 : ZMod 98506729) ^ 2662344 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (7 : ZMod 98506729) ^ 956376 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (7 : ZMod 98506729) ^ 274392 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_102534983 : Nat.Prime 102534983 := by
  apply lucas_primality 102534983 (5 : ZMod 102534983)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (19, 1), (245299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (19, 1), (245299, 1)] : List FactorBlock).map factorBlockValue).prod) = 102534983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_11
      · exact prime_oneHundredFortyFourEL_19
      · exact prime_oneHundredFortyFourEL_245299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 102534983) ^ 51267491 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 102534983) ^ 9321362 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 102534983) ^ 5396578 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 102534983) ^ 418 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_106178993 : Nat.Prime 106178993 := by
  apply lucas_primality 106178993 (3 : ZMod 106178993)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (19, 1), (103, 1), (3391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (19, 1), (103, 1), (3391, 1)] : List FactorBlock).map factorBlockValue).prod) = 106178993 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_19
      · exact prime_oneHundredFortyFourEL_103
      · exact prime_oneHundredFortyFourEL_3391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 106178993) ^ 53089496 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 106178993) ^ 5588368 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 106178993) ^ 1030864 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 106178993) ^ 31312 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_109286249 : Nat.Prime 109286249 := by
  apply lucas_primality 109286249 (3 : ZMod 109286249)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (23, 1), (139, 1), (4273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (23, 1), (139, 1), (4273, 1)] : List FactorBlock).map factorBlockValue).prod) = 109286249 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_23
      · exact prime_oneHundredFortyFourEL_139
      · exact prime_oneHundredFortyFourEL_4273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 109286249) ^ 54643124 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 109286249) ^ 4751576 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 109286249) ^ 786232 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 109286249) ^ 25576 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_124596973 : Nat.Prime 124596973 := by
  apply lucas_primality 124596973 (2 : ZMod 124596973)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (43, 1), (80489, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (43, 1), (80489, 1)] : List FactorBlock).map factorBlockValue).prod) = 124596973 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_43
      · exact prime_oneHundredFortyFourEL_80489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 124596973) ^ 62298486 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 124596973) ^ 41532324 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 124596973) ^ 2897604 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 124596973) ^ 1548 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_131433079 : Nat.Prime 131433079 := by
  apply lucas_primality 131433079 (17 : ZMod 131433079)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (223, 1), (14033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (223, 1), (14033, 1)] : List FactorBlock).map factorBlockValue).prod) = 131433079 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_7
      · exact prime_oneHundredFortyFourEL_223
      · exact prime_oneHundredFortyFourEL_14033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 131433079) ^ 65716539 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (17 : ZMod 131433079) ^ 43811026 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (17 : ZMod 131433079) ^ 18776154 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (17 : ZMod 131433079) ^ 589386 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (17 : ZMod 131433079) ^ 9366 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_132178273 : Nat.Prime 132178273 := by
  apply lucas_primality 132178273 (7 : ZMod 132178273)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (997, 1), (1381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (997, 1), (1381, 1)] : List FactorBlock).map factorBlockValue).prod) = 132178273 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_997
      · exact prime_oneHundredFortyFourEL_1381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 132178273) ^ 66089136 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (7 : ZMod 132178273) ^ 44059424 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (7 : ZMod 132178273) ^ 132576 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (7 : ZMod 132178273) ^ 95712 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_139568171 : Nat.Prime 139568171 := by
  apply lucas_primality 139568171 (2 : ZMod 139568171)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 2), (284833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 2), (284833, 1)] : List FactorBlock).map factorBlockValue).prod) = 139568171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_5
      · exact prime_oneHundredFortyFourEL_7
      · exact prime_oneHundredFortyFourEL_284833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 139568171) ^ 69784085 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 139568171) ^ 27913634 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 139568171) ^ 19938310 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 139568171) ^ 490 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_152517311 : Nat.Prime 152517311 := by
  apply lucas_primality 152517311 (11 : ZMod 152517311)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (647, 1), (2143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (647, 1), (2143, 1)] : List FactorBlock).map factorBlockValue).prod) = 152517311 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_5
      · exact prime_oneHundredFortyFourEL_11
      · exact prime_oneHundredFortyFourEL_647
      · exact prime_oneHundredFortyFourEL_2143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 152517311) ^ 76258655 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (11 : ZMod 152517311) ^ 30503462 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (11 : ZMod 152517311) ^ 13865210 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (11 : ZMod 152517311) ^ 235730 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (11 : ZMod 152517311) ^ 71170 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_160368193 : Nat.Prime 160368193 := by
  apply lucas_primality 160368193 (7 : ZMod 160368193)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (139, 1), (2003, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (139, 1), (2003, 1)] : List FactorBlock).map factorBlockValue).prod) = 160368193 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_139
      · exact prime_oneHundredFortyFourEL_2003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 160368193) ^ 80184096 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (7 : ZMod 160368193) ^ 53456064 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (7 : ZMod 160368193) ^ 1153728 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (7 : ZMod 160368193) ^ 80064 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_202034779 : Nat.Prime 202034779 := by
  apply lucas_primality 202034779 (7 : ZMod 202034779)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (3061133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (3061133, 1)] : List FactorBlock).map factorBlockValue).prod) = 202034779 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_11
      · exact prime_oneHundredFortyFourEL_3061133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 202034779) ^ 101017389 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (7 : ZMod 202034779) ^ 67344926 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (7 : ZMod 202034779) ^ 18366798 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (7 : ZMod 202034779) ^ 66 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_210271273 : Nat.Prime 210271273 := by
  apply lucas_primality 210271273 (5 : ZMod 210271273)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (8761303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (8761303, 1)] : List FactorBlock).map factorBlockValue).prod) = 210271273 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_8761303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 210271273) ^ 105135636 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 210271273) ^ 70090424 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 210271273) ^ 24 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_212357987 : Nat.Prime 212357987 := by
  apply lucas_primality 212357987 (2 : ZMod 212357987)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (106178993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (106178993, 1)] : List FactorBlock).map factorBlockValue).prod) = 212357987 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_106178993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 212357987) ^ 106178993 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 212357987) ^ 2 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_213150073 : Nat.Prime 213150073 := by
  apply lucas_primality 213150073 (5 : ZMod 213150073)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (73, 1), (121661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (73, 1), (121661, 1)] : List FactorBlock).map factorBlockValue).prod) = 213150073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_73
      · exact prime_oneHundredFortyFourEL_121661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 213150073) ^ 106575036 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 213150073) ^ 71050024 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 213150073) ^ 2919864 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 213150073) ^ 1752 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_224466569 : Nat.Prime 224466569 := by
  apply lucas_primality 224466569 (3 : ZMod 224466569)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (23, 1), (37, 1), (32971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (23, 1), (37, 1), (32971, 1)] : List FactorBlock).map factorBlockValue).prod) = 224466569 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_23
      · exact prime_oneHundredFortyFourEL_37
      · exact prime_oneHundredFortyFourEL_32971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 224466569) ^ 112233284 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 224466569) ^ 9759416 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 224466569) ^ 6066664 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 224466569) ^ 6808 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_233952713 : Nat.Prime 233952713 := by
  apply lucas_primality 233952713 (3 : ZMod 233952713)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (1777, 1), (2351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (1777, 1), (2351, 1)] : List FactorBlock).map factorBlockValue).prod) = 233952713 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_7
      · exact prime_oneHundredFortyFourEL_1777
      · exact prime_oneHundredFortyFourEL_2351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 233952713) ^ 116976356 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 233952713) ^ 33421816 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 233952713) ^ 131656 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 233952713) ^ 99512 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_240217849 : Nat.Prime 240217849 := by
  apply lucas_primality 240217849 (19 : ZMod 240217849)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (13, 1), (256643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (13, 1), (256643, 1)] : List FactorBlock).map factorBlockValue).prod) = 240217849 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_13
      · exact prime_oneHundredFortyFourEL_256643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 240217849) ^ 120108924 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (19 : ZMod 240217849) ^ 80072616 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (19 : ZMod 240217849) ^ 18478296 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (19 : ZMod 240217849) ^ 936 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_248129153 : Nat.Prime 248129153 := by
  apply lucas_primality 248129153 (3 : ZMod 248129153)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (23, 1), (89, 1), (947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (23, 1), (89, 1), (947, 1)] : List FactorBlock).map factorBlockValue).prod) = 248129153 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_23
      · exact prime_oneHundredFortyFourEL_89
      · exact prime_oneHundredFortyFourEL_947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 248129153) ^ 124064576 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 248129153) ^ 10788224 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 248129153) ^ 2787968 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 248129153) ^ 262016 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_261788987 : Nat.Prime 261788987 := by
  apply lucas_primality 261788987 (2 : ZMod 261788987)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (37, 1), (139, 1), (821, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (37, 1), (139, 1), (821, 1)] : List FactorBlock).map factorBlockValue).prod) = 261788987 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_31
      · exact prime_oneHundredFortyFourEL_37
      · exact prime_oneHundredFortyFourEL_139
      · exact prime_oneHundredFortyFourEL_821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 261788987) ^ 130894493 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 261788987) ^ 8444806 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 261788987) ^ 7075378 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 261788987) ^ 1883374 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 261788987) ^ 318866 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_266552171 : Nat.Prime 266552171 := by
  apply lucas_primality 266552171 (2 : ZMod 266552171)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (26655217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (26655217, 1)] : List FactorBlock).map factorBlockValue).prod) = 266552171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_5
      · exact prime_oneHundredFortyFourEL_26655217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 266552171) ^ 133276085 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 266552171) ^ 53310434 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 266552171) ^ 10 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_285902891 : Nat.Prime 285902891 := by
  apply lucas_primality 285902891 (10 : ZMod 285902891)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (13, 1), (211, 1), (1489, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (13, 1), (211, 1), (1489, 1)] : List FactorBlock).map factorBlockValue).prod) = 285902891 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_5
      · exact prime_oneHundredFortyFourEL_7
      · exact prime_oneHundredFortyFourEL_13
      · exact prime_oneHundredFortyFourEL_211
      · exact prime_oneHundredFortyFourEL_1489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 285902891) ^ 142951445 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (10 : ZMod 285902891) ^ 57180578 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (10 : ZMod 285902891) ^ 40843270 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (10 : ZMod 285902891) ^ 21992530 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (10 : ZMod 285902891) ^ 1354990 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (10 : ZMod 285902891) ^ 192010 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_305677483 : Nat.Prime 305677483 := by
  apply lucas_primality 305677483 (2 : ZMod 305677483)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (4631477, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (4631477, 1)] : List FactorBlock).map factorBlockValue).prod) = 305677483 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_11
      · exact prime_oneHundredFortyFourEL_4631477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 305677483) ^ 152838741 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 305677483) ^ 101892494 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 305677483) ^ 27788862 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 305677483) ^ 66 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_316797919 : Nat.Prime 316797919 := by
  apply lucas_primality 316797919 (3 : ZMod 316797919)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (601, 1), (87853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (601, 1), (87853, 1)] : List FactorBlock).map factorBlockValue).prod) = 316797919 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_601
      · exact prime_oneHundredFortyFourEL_87853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 316797919) ^ 158398959 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 316797919) ^ 105599306 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 316797919) ^ 527118 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 316797919) ^ 3606 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_320845783 : Nat.Prime 320845783 := by
  apply lucas_primality 320845783 (5 : ZMod 320845783)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (47, 1), (53, 1), (21467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (47, 1), (53, 1), (21467, 1)] : List FactorBlock).map factorBlockValue).prod) = 320845783 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_47
      · exact prime_oneHundredFortyFourEL_53
      · exact prime_oneHundredFortyFourEL_21467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 320845783) ^ 160422891 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 320845783) ^ 106948594 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 320845783) ^ 6826506 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 320845783) ^ 6053694 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 320845783) ^ 14946 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_337303277 : Nat.Prime 337303277 := by
  apply lucas_primality 337303277 (2 : ZMod 337303277)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (4438201, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (4438201, 1)] : List FactorBlock).map factorBlockValue).prod) = 337303277 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_19
      · exact prime_oneHundredFortyFourEL_4438201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 337303277) ^ 168651638 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 337303277) ^ 17752804 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 337303277) ^ 76 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_353497423 : Nat.Prime 353497423 := by
  apply lucas_primality 353497423 (5 : ZMod 353497423)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (1151, 1), (3011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (1151, 1), (3011, 1)] : List FactorBlock).map factorBlockValue).prod) = 353497423 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_17
      · exact prime_oneHundredFortyFourEL_1151
      · exact prime_oneHundredFortyFourEL_3011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 353497423) ^ 176748711 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 353497423) ^ 117832474 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 353497423) ^ 20793966 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 353497423) ^ 307122 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 353497423) ^ 117402 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_452722021 : Nat.Prime 452722021 := by
  apply lucas_primality 452722021 (7 : ZMod 452722021)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7545367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7545367, 1)] : List FactorBlock).map factorBlockValue).prod) = 452722021 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_5
      · exact prime_oneHundredFortyFourEL_7545367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 452722021) ^ 226361010 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (7 : ZMod 452722021) ^ 150907340 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (7 : ZMod 452722021) ^ 90544404 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (7 : ZMod 452722021) ^ 60 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_457396609 : Nat.Prime 457396609 := by
  apply lucas_primality 457396609 (7 : ZMod 457396609)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (349, 1), (3413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (349, 1), (3413, 1)] : List FactorBlock).map factorBlockValue).prod) = 457396609 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_349
      · exact prime_oneHundredFortyFourEL_3413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 457396609) ^ 228698304 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (7 : ZMod 457396609) ^ 152465536 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (7 : ZMod 457396609) ^ 1310592 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (7 : ZMod 457396609) ^ 134016 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_463251577 : Nat.Prime 463251577 := by
  apply lucas_primality 463251577 (5 : ZMod 463251577)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (73, 1), (79, 1), (3347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (73, 1), (79, 1), (3347, 1)] : List FactorBlock).map factorBlockValue).prod) = 463251577 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_73
      · exact prime_oneHundredFortyFourEL_79
      · exact prime_oneHundredFortyFourEL_3347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 463251577) ^ 231625788 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 463251577) ^ 154417192 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 463251577) ^ 6345912 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 463251577) ^ 5863944 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 463251577) ^ 138408 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_499514461 : Nat.Prime 499514461 := by
  apply lucas_primality 499514461 (2 : ZMod 499514461)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (23, 1), (361967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (23, 1), (361967, 1)] : List FactorBlock).map factorBlockValue).prod) = 499514461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_5
      · exact prime_oneHundredFortyFourEL_23
      · exact prime_oneHundredFortyFourEL_361967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 499514461) ^ 249757230 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 499514461) ^ 166504820 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 499514461) ^ 99902892 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 499514461) ^ 21718020 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 499514461) ^ 1380 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_551220613 : Nat.Prime 551220613 := by
  apply lucas_primality 551220613 (2 : ZMod 551220613)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (43, 1), (1068257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (43, 1), (1068257, 1)] : List FactorBlock).map factorBlockValue).prod) = 551220613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_43
      · exact prime_oneHundredFortyFourEL_1068257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 551220613) ^ 275610306 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 551220613) ^ 183740204 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 551220613) ^ 12819084 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 551220613) ^ 516 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_559319647 : Nat.Prime 559319647 := by
  apply lucas_primality 559319647 (3 : ZMod 559319647)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (47, 1), (59, 1), (33617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (47, 1), (59, 1), (33617, 1)] : List FactorBlock).map factorBlockValue).prod) = 559319647 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_47
      · exact prime_oneHundredFortyFourEL_59
      · exact prime_oneHundredFortyFourEL_33617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 559319647) ^ 279659823 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 559319647) ^ 186439882 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 559319647) ^ 11900418 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 559319647) ^ 9479994 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 559319647) ^ 16638 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_637514413 : Nat.Prime 637514413 := by
  apply lucas_primality 637514413 (2 : ZMod 637514413)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (41, 1), (1295761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (41, 1), (1295761, 1)] : List FactorBlock).map factorBlockValue).prod) = 637514413 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_41
      · exact prime_oneHundredFortyFourEL_1295761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 637514413) ^ 318757206 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 637514413) ^ 212504804 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 637514413) ^ 15549132 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 637514413) ^ 492 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_640433267 : Nat.Prime 640433267 := by
  apply lucas_primality 640433267 (2 : ZMod 640433267)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (19, 1), (61, 1), (25117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (19, 1), (61, 1), (25117, 1)] : List FactorBlock).map factorBlockValue).prod) = 640433267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_11
      · exact prime_oneHundredFortyFourEL_19
      · exact prime_oneHundredFortyFourEL_61
      · exact prime_oneHundredFortyFourEL_25117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 640433267) ^ 320216633 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 58221206 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 33707014 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 10498906 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 25498 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_653404021 : Nat.Prime 653404021 := by
  apply lucas_primality 653404021 (6 : ZMod 653404021)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (73, 1), (241, 1), (619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (73, 1), (241, 1), (619, 1)] : List FactorBlock).map factorBlockValue).prod) = 653404021 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_5
      · exact prime_oneHundredFortyFourEL_73
      · exact prime_oneHundredFortyFourEL_241
      · exact prime_oneHundredFortyFourEL_619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 653404021) ^ 326702010 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (6 : ZMod 653404021) ^ 217801340 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (6 : ZMod 653404021) ^ 130680804 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (6 : ZMod 653404021) ^ 8950740 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (6 : ZMod 653404021) ^ 2711220 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (6 : ZMod 653404021) ^ 1055580 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_714027719 : Nat.Prime 714027719 := by
  apply lucas_primality 714027719 (11 : ZMod 714027719)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) = 714027719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_17203
      · exact prime_oneHundredFortyFourEL_20753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 714027719) ^ 357013859 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 41506 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 34406 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_722305219 : Nat.Prime 722305219 := by
  apply lucas_primality 722305219 (2 : ZMod 722305219)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2791, 1), (43133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2791, 1), (43133, 1)] : List FactorBlock).map factorBlockValue).prod) = 722305219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_2791
      · exact prime_oneHundredFortyFourEL_43133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 722305219) ^ 361152609 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 722305219) ^ 240768406 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 722305219) ^ 258798 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 722305219) ^ 16746 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_764417231 : Nat.Prime 764417231 := by
  apply lucas_primality 764417231 (7 : ZMod 764417231)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (61, 1), (97, 1), (12919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (61, 1), (97, 1), (12919, 1)] : List FactorBlock).map factorBlockValue).prod) = 764417231 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_5
      · exact prime_oneHundredFortyFourEL_61
      · exact prime_oneHundredFortyFourEL_97
      · exact prime_oneHundredFortyFourEL_12919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 764417231) ^ 382208615 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (7 : ZMod 764417231) ^ 152883446 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (7 : ZMod 764417231) ^ 12531430 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (7 : ZMod 764417231) ^ 7880590 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (7 : ZMod 764417231) ^ 59170 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_878651999 : Nat.Prime 878651999 := by
  apply lucas_primality 878651999 (11 : ZMod 878651999)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (19, 1), (811, 1), (4073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (19, 1), (811, 1), (4073, 1)] : List FactorBlock).map factorBlockValue).prod) = 878651999 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_7
      · exact prime_oneHundredFortyFourEL_19
      · exact prime_oneHundredFortyFourEL_811
      · exact prime_oneHundredFortyFourEL_4073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 878651999) ^ 439325999 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (11 : ZMod 878651999) ^ 125521714 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (11 : ZMod 878651999) ^ 46244842 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (11 : ZMod 878651999) ^ 1083418 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (11 : ZMod 878651999) ^ 215726 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_886981163 : Nat.Prime 886981163 := by
  apply lucas_primality 886981163 (2 : ZMod 886981163)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (223, 1), (227, 1), (8761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (223, 1), (227, 1), (8761, 1)] : List FactorBlock).map factorBlockValue).prod) = 886981163 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_223
      · exact prime_oneHundredFortyFourEL_227
      · exact prime_oneHundredFortyFourEL_8761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 886981163) ^ 443490581 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 886981163) ^ 3977494 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 886981163) ^ 3907406 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 886981163) ^ 101242 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_906208483 : Nat.Prime 906208483 := by
  apply lucas_primality 906208483 (2 : ZMod 906208483)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (131, 1), (1152937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (131, 1), (1152937, 1)] : List FactorBlock).map factorBlockValue).prod) = 906208483 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_131
      · exact prime_oneHundredFortyFourEL_1152937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 906208483) ^ 453104241 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 906208483) ^ 302069494 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 906208483) ^ 6917622 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 906208483) ^ 786 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_927006557 : Nat.Prime 927006557 := by
  apply lucas_primality 927006557 (2 : ZMod 927006557)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (41, 1), (43, 1), (89, 1), (211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (41, 1), (43, 1), (89, 1), (211, 1)] : List FactorBlock).map factorBlockValue).prod) = 927006557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_7
      · exact prime_oneHundredFortyFourEL_41
      · exact prime_oneHundredFortyFourEL_43
      · exact prime_oneHundredFortyFourEL_89
      · exact prime_oneHundredFortyFourEL_211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 927006557) ^ 463503278 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 927006557) ^ 132429508 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 927006557) ^ 22609916 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 927006557) ^ 21558292 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 927006557) ^ 10415804 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 927006557) ^ 4393396 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_989186707 : Nat.Prime 989186707 := by
  apply lucas_primality 989186707 (2 : ZMod 989186707)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (43, 1), (269, 1), (4751, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (43, 1), (269, 1), (4751, 1)] : List FactorBlock).map factorBlockValue).prod) = 989186707 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_43
      · exact prime_oneHundredFortyFourEL_269
      · exact prime_oneHundredFortyFourEL_4751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 989186707) ^ 494593353 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 989186707) ^ 329728902 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 989186707) ^ 23004342 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 989186707) ^ 3677274 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 989186707) ^ 208206 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_990452107 : Nat.Prime 990452107 := by
  apply lucas_primality 990452107 (2 : ZMod 990452107)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (7860731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (7860731, 1)] : List FactorBlock).map factorBlockValue).prod) = 990452107 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_7
      · exact prime_oneHundredFortyFourEL_7860731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 990452107) ^ 495226053 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 990452107) ^ 330150702 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 990452107) ^ 141493158 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 990452107) ^ 126 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_1164258779 : Nat.Prime 1164258779 := by
  apply lucas_primality 1164258779 (2 : ZMod 1164258779)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (607, 1), (751, 1), (1277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (607, 1), (751, 1), (1277, 1)] : List FactorBlock).map factorBlockValue).prod) = 1164258779 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_607
      · exact prime_oneHundredFortyFourEL_751
      · exact prime_oneHundredFortyFourEL_1277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1164258779) ^ 582129389 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 1164258779) ^ 1918054 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 1164258779) ^ 1550278 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 1164258779) ^ 911714 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_1266377461 : Nat.Prime 1266377461 := by
  apply lucas_primality 1266377461 (7 : ZMod 1266377461)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (21106291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (21106291, 1)] : List FactorBlock).map factorBlockValue).prod) = 1266377461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_5
      · exact prime_oneHundredFortyFourEL_21106291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 1266377461) ^ 633188730 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (7 : ZMod 1266377461) ^ 422125820 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (7 : ZMod 1266377461) ^ 253275492 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (7 : ZMod 1266377461) ^ 60 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_1299989947 : Nat.Prime 1299989947 := by
  apply lucas_primality 1299989947 (2 : ZMod 1299989947)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (1667, 1), (5651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (1667, 1), (5651, 1)] : List FactorBlock).map factorBlockValue).prod) = 1299989947 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_23
      · exact prime_oneHundredFortyFourEL_1667
      · exact prime_oneHundredFortyFourEL_5651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1299989947) ^ 649994973 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 1299989947) ^ 433329982 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 1299989947) ^ 56521302 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 1299989947) ^ 779838 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 1299989947) ^ 230046 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_1311434989 : Nat.Prime 1311434989 := by
  apply lucas_primality 1311434989 (6 : ZMod 1311434989)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (109286249, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (109286249, 1)] : List FactorBlock).map factorBlockValue).prod) = 1311434989 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_109286249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 1311434989) ^ 655717494 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (6 : ZMod 1311434989) ^ 437144996 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (6 : ZMod 1311434989) ^ 12 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_1431512219 : Nat.Prime 1431512219 := by
  apply lucas_primality 1431512219 (2 : ZMod 1431512219)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (67, 1), (1321, 1), (8087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (67, 1), (1321, 1), (8087, 1)] : List FactorBlock).map factorBlockValue).prod) = 1431512219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_67
      · exact prime_oneHundredFortyFourEL_1321
      · exact prime_oneHundredFortyFourEL_8087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1431512219) ^ 715756109 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 1431512219) ^ 21365854 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 1431512219) ^ 1083658 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 1431512219) ^ 177014 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_1439052847 : Nat.Prime 1439052847 := by
  apply lucas_primality 1439052847 (3 : ZMod 1439052847)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (11, 1), (3114833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (11, 1), (3114833, 1)] : List FactorBlock).map factorBlockValue).prod) = 1439052847 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_7
      · exact prime_oneHundredFortyFourEL_11
      · exact prime_oneHundredFortyFourEL_3114833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1439052847) ^ 719526423 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 1439052847) ^ 479684282 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 1439052847) ^ 205578978 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 1439052847) ^ 130822986 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 1439052847) ^ 462 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_1456256521 : Nat.Prime 1456256521 := by
  apply lucas_primality 1456256521 (7 : ZMod 1456256521)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (19, 1), (212903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (19, 1), (212903, 1)] : List FactorBlock).map factorBlockValue).prod) = 1456256521 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_5
      · exact prime_oneHundredFortyFourEL_19
      · exact prime_oneHundredFortyFourEL_212903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1456256521) ^ 728128260 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (7 : ZMod 1456256521) ^ 485418840 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (7 : ZMod 1456256521) ^ 291251304 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (7 : ZMod 1456256521) ^ 76645080 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (7 : ZMod 1456256521) ^ 6840 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_1469390833 : Nat.Prime 1469390833 := by
  apply lucas_primality 1469390833 (5 : ZMod 1469390833)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (7, 2), (13, 1), (83, 1), (193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (7, 2), (13, 1), (83, 1), (193, 1)] : List FactorBlock).map factorBlockValue).prod) = 1469390833 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_7
      · exact prime_oneHundredFortyFourEL_13
      · exact prime_oneHundredFortyFourEL_83
      · exact prime_oneHundredFortyFourEL_193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1469390833) ^ 734695416 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 1469390833) ^ 489796944 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 1469390833) ^ 209912976 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 1469390833) ^ 113030064 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 1469390833) ^ 17703504 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 1469390833) ^ 7613424 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_1518742759 : Nat.Prime 1518742759 := by
  apply lucas_primality 1518742759 (6 : ZMod 1518742759)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (19471061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (19471061, 1)] : List FactorBlock).map factorBlockValue).prod) = 1518742759 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_13
      · exact prime_oneHundredFortyFourEL_19471061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 1518742759) ^ 759371379 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (6 : ZMod 1518742759) ^ 506247586 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (6 : ZMod 1518742759) ^ 116826366 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (6 : ZMod 1518742759) ^ 78 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_1953042799 : Nat.Prime 1953042799 := by
  apply lucas_primality 1953042799 (3 : ZMod 1953042799)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (46501019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (46501019, 1)] : List FactorBlock).map factorBlockValue).prod) = 1953042799 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_7
      · exact prime_oneHundredFortyFourEL_46501019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1953042799) ^ 976521399 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 1953042799) ^ 651014266 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 1953042799) ^ 279006114 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 1953042799) ^ 42 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_1965344783 : Nat.Prime 1965344783 := by
  apply lucas_primality 1965344783 (5 : ZMod 1965344783)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (359, 1), (971, 1), (2819, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (359, 1), (971, 1), (2819, 1)] : List FactorBlock).map factorBlockValue).prod) = 1965344783 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_359
      · exact prime_oneHundredFortyFourEL_971
      · exact prime_oneHundredFortyFourEL_2819
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1965344783) ^ 982672391 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 1965344783) ^ 5474498 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 1965344783) ^ 2024042 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 1965344783) ^ 697178 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_2072458123 : Nat.Prime 2072458123 := by
  apply lucas_primality 2072458123 (2 : ZMod 2072458123)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (49344241, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (49344241, 1)] : List FactorBlock).map factorBlockValue).prod) = 2072458123 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_7
      · exact prime_oneHundredFortyFourEL_49344241
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2072458123) ^ 1036229061 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 2072458123) ^ 690819374 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 2072458123) ^ 296065446 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 2072458123) ^ 42 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_2204882453 : Nat.Prime 2204882453 := by
  apply lucas_primality 2204882453 (2 : ZMod 2204882453)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (551220613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (551220613, 1)] : List FactorBlock).map factorBlockValue).prod) = 2204882453 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_551220613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 2204882453) ^ 1102441226 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 2204882453) ^ 4 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_2325976321 : Nat.Prime 2325976321 := by
  apply lucas_primality 2325976321 (39 : ZMod 2325976321)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 1), (5, 1), (29, 1), (20887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 1), (5, 1), (29, 1), (20887, 1)] : List FactorBlock).map factorBlockValue).prod) = 2325976321 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_5
      · exact prime_oneHundredFortyFourEL_29
      · exact prime_oneHundredFortyFourEL_20887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (39 : ZMod 2325976321) ^ 1162988160 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (39 : ZMod 2325976321) ^ 775325440 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (39 : ZMod 2325976321) ^ 465195264 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (39 : ZMod 2325976321) ^ 80206080 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (39 : ZMod 2325976321) ^ 111360 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_2338623893 : Nat.Prime 2338623893 := by
  apply lucas_primality 2338623893 (3 : ZMod 2338623893)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (19, 1), (101, 1), (27697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (19, 1), (101, 1), (27697, 1)] : List FactorBlock).map factorBlockValue).prod) = 2338623893 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_11
      · exact prime_oneHundredFortyFourEL_19
      · exact prime_oneHundredFortyFourEL_101
      · exact prime_oneHundredFortyFourEL_27697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2338623893) ^ 1169311946 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 2338623893) ^ 212602172 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 2338623893) ^ 123085468 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 2338623893) ^ 23154692 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 2338623893) ^ 84436 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_2416168199 : Nat.Prime 2416168199 := by
  apply lucas_primality 2416168199 (7 : ZMod 2416168199)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (71, 1), (362027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (71, 1), (362027, 1)] : List FactorBlock).map factorBlockValue).prod) = 2416168199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_47
      · exact prime_oneHundredFortyFourEL_71
      · exact prime_oneHundredFortyFourEL_362027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 2416168199) ^ 1208084099 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (7 : ZMod 2416168199) ^ 51407834 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (7 : ZMod 2416168199) ^ 34030538 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (7 : ZMod 2416168199) ^ 6674 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_2619477239 : Nat.Prime 2619477239 := by
  apply lucas_primality 2619477239 (7 : ZMod 2619477239)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (7411, 1), (25247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (7411, 1), (25247, 1)] : List FactorBlock).map factorBlockValue).prod) = 2619477239 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_7
      · exact prime_oneHundredFortyFourEL_7411
      · exact prime_oneHundredFortyFourEL_25247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 2619477239) ^ 1309738619 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (7 : ZMod 2619477239) ^ 374211034 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (7 : ZMod 2619477239) ^ 353458 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (7 : ZMod 2619477239) ^ 103754 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_2752927673 : Nat.Prime 2752927673 := by
  apply lucas_primality 2752927673 (3 : ZMod 2752927673)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (107, 1), (292367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (107, 1), (292367, 1)] : List FactorBlock).map factorBlockValue).prod) = 2752927673 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_11
      · exact prime_oneHundredFortyFourEL_107
      · exact prime_oneHundredFortyFourEL_292367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2752927673) ^ 1376463836 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 2752927673) ^ 250266152 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 2752927673) ^ 25728296 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 2752927673) ^ 9416 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_2977549837 : Nat.Prime 2977549837 := by
  apply lucas_primality 2977549837 (2 : ZMod 2977549837)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (248129153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (248129153, 1)] : List FactorBlock).map factorBlockValue).prod) = 2977549837 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_248129153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2977549837) ^ 1488774918 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 2977549837) ^ 992516612 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 2977549837) ^ 12 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_3063309401 : Nat.Prime 3063309401 := by
  apply lucas_primality 3063309401 (3 : ZMod 3063309401)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (547, 1), (28001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (547, 1), (28001, 1)] : List FactorBlock).map factorBlockValue).prod) = 3063309401 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_5
      · exact prime_oneHundredFortyFourEL_547
      · exact prime_oneHundredFortyFourEL_28001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3063309401) ^ 1531654700 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 3063309401) ^ 612661880 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 3063309401) ^ 5600200 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 3063309401) ^ 109400 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_3501703901 : Nat.Prime 3501703901 := by
  apply lucas_primality 3501703901 (2 : ZMod 3501703901)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (35017039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (35017039, 1)] : List FactorBlock).map factorBlockValue).prod) = 3501703901 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_5
      · exact prime_oneHundredFortyFourEL_35017039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3501703901) ^ 1750851950 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 3501703901) ^ 700340780 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 3501703901) ^ 100 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_4128772399 : Nat.Prime 4128772399 := by
  apply lucas_primality 4128772399 (3 : ZMod 4128772399)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 1), (53, 1), (73, 1), (6133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 1), (53, 1), (73, 1), (6133, 1)] : List FactorBlock).map factorBlockValue).prod) = 4128772399 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_29
      · exact prime_oneHundredFortyFourEL_53
      · exact prime_oneHundredFortyFourEL_73
      · exact prime_oneHundredFortyFourEL_6133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4128772399) ^ 2064386199 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 4128772399) ^ 1376257466 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 4128772399) ^ 142371462 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 4128772399) ^ 77901366 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 4128772399) ^ 56558526 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 4128772399) ^ 673206 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_4853859953 : Nat.Prime 4853859953 := by
  apply lucas_primality 4853859953 (3 : ZMod 4853859953)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (43, 1), (47, 1), (150107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (43, 1), (47, 1), (150107, 1)] : List FactorBlock).map factorBlockValue).prod) = 4853859953 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_43
      · exact prime_oneHundredFortyFourEL_47
      · exact prime_oneHundredFortyFourEL_150107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4853859953) ^ 2426929976 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 4853859953) ^ 112880464 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 4853859953) ^ 103273616 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 4853859953) ^ 32336 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_4980897683 : Nat.Prime 4980897683 := by
  apply lucas_primality 4980897683 (2 : ZMod 4980897683)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1171, 1), (2126771, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1171, 1), (2126771, 1)] : List FactorBlock).map factorBlockValue).prod) = 4980897683 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_1171
      · exact prime_oneHundredFortyFourEL_2126771
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4980897683) ^ 2490448841 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 4980897683) ^ 4253542 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 4980897683) ^ 2342 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_5982940531 : Nat.Prime 5982940531 := by
  apply lucas_primality 5982940531 (3 : ZMod 5982940531)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (7, 1), (3165577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (7, 1), (3165577, 1)] : List FactorBlock).map factorBlockValue).prod) = 5982940531 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_5
      · exact prime_oneHundredFortyFourEL_7
      · exact prime_oneHundredFortyFourEL_3165577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 5982940531) ^ 2991470265 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 5982940531) ^ 1994313510 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 5982940531) ^ 1196588106 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 5982940531) ^ 854705790 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 5982940531) ^ 1890 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_6037638679 : Nat.Prime 6037638679 := by
  apply lucas_primality 6037638679 (3 : ZMod 6037638679)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) = 6037638679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_31
      · exact prime_oneHundredFortyFourEL_10820141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6037638679) ^ 3018819339 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 2012546226 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 194762538 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 558 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_6265973617 : Nat.Prime 6265973617 := by
  apply lucas_primality 6265973617 (5 : ZMod 6265973617)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (7, 1), (227, 1), (82153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (7, 1), (227, 1), (82153, 1)] : List FactorBlock).map factorBlockValue).prod) = 6265973617 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_7
      · exact prime_oneHundredFortyFourEL_227
      · exact prime_oneHundredFortyFourEL_82153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 6265973617) ^ 3132986808 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 6265973617) ^ 2088657872 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 6265973617) ^ 895139088 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 6265973617) ^ 27603408 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 6265973617) ^ 76272 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_7406287297 : Nat.Prime 7406287297 := by
  apply lucas_primality 7406287297 (5 : ZMod 7406287297)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (941, 1), (40993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (941, 1), (40993, 1)] : List FactorBlock).map factorBlockValue).prod) = 7406287297 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_941
      · exact prime_oneHundredFortyFourEL_40993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 7406287297) ^ 3703143648 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 7406287297) ^ 2468762432 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 7406287297) ^ 7870656 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 7406287297) ^ 180672 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_7992231833 : Nat.Prime 7992231833 := by
  apply lucas_primality 7992231833 (3 : ZMod 7992231833)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (3121, 1), (24623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (3121, 1), (24623, 1)] : List FactorBlock).map factorBlockValue).prod) = 7992231833 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_13
      · exact prime_oneHundredFortyFourEL_3121
      · exact prime_oneHundredFortyFourEL_24623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 7992231833) ^ 3996115916 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 7992231833) ^ 614787064 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 7992231833) ^ 2560792 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 7992231833) ^ 324584 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_10014130171 : Nat.Prime 10014130171 := by
  apply lucas_primality 10014130171 (11 : ZMod 10014130171)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (11, 1), (661, 1), (5101, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (11, 1), (661, 1), (5101, 1)] : List FactorBlock).map factorBlockValue).prod) = 10014130171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_5
      · exact prime_oneHundredFortyFourEL_11
      · exact prime_oneHundredFortyFourEL_661
      · exact prime_oneHundredFortyFourEL_5101
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 10014130171) ^ 5007065085 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (11 : ZMod 10014130171) ^ 3338043390 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (11 : ZMod 10014130171) ^ 2002826034 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (11 : ZMod 10014130171) ^ 910375470 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (11 : ZMod 10014130171) ^ 15149970 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (11 : ZMod 10014130171) ^ 1963170 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_10089149659 : Nat.Prime 10089149659 := by
  apply lucas_primality 10089149659 (3 : ZMod 10089149659)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (240217849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (240217849, 1)] : List FactorBlock).map factorBlockValue).prod) = 10089149659 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_7
      · exact prime_oneHundredFortyFourEL_240217849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 10089149659) ^ 5044574829 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 10089149659) ^ 3363049886 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 10089149659) ^ 1441307094 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 10089149659) ^ 42 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_10421853289 : Nat.Prime 10421853289 := by
  apply lucas_primality 10421853289 (19 : ZMod 10421853289)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (11, 1), (23, 1), (359, 1), (683, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (11, 1), (23, 1), (359, 1), (683, 1)] : List FactorBlock).map factorBlockValue).prod) = 10421853289 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_7
      · exact prime_oneHundredFortyFourEL_11
      · exact prime_oneHundredFortyFourEL_23
      · exact prime_oneHundredFortyFourEL_359
      · exact prime_oneHundredFortyFourEL_683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 10421853289) ^ 5210926644 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (19 : ZMod 10421853289) ^ 3473951096 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (19 : ZMod 10421853289) ^ 1488836184 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (19 : ZMod 10421853289) ^ 947441208 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (19 : ZMod 10421853289) ^ 453124056 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (19 : ZMod 10421853289) ^ 29030232 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (19 : ZMod 10421853289) ^ 15258936 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_10543823989 : Nat.Prime 10543823989 := by
  apply lucas_primality 10543823989 (2 : ZMod 10543823989)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (878651999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (878651999, 1)] : List FactorBlock).map factorBlockValue).prod) = 10543823989 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_878651999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 10543823989) ^ 5271911994 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 10543823989) ^ 3514607996 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 10543823989) ^ 12 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_10938038801 : Nat.Prime 10938038801 := by
  apply lucas_primality 10938038801 (6 : ZMod 10938038801)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 2), (13, 1), (83, 1), (25343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 2), (13, 1), (83, 1), (25343, 1)] : List FactorBlock).map factorBlockValue).prod) = 10938038801 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_5
      · exact prime_oneHundredFortyFourEL_13
      · exact prime_oneHundredFortyFourEL_83
      · exact prime_oneHundredFortyFourEL_25343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 10938038801) ^ 5469019400 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (6 : ZMod 10938038801) ^ 2187607760 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (6 : ZMod 10938038801) ^ 841387600 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (6 : ZMod 10938038801) ^ 131783600 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (6 : ZMod 10938038801) ^ 431600 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_11819515781 : Nat.Prime 11819515781 := by
  apply lucas_primality 11819515781 (2 : ZMod 11819515781)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (43, 1), (157, 1), (87539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (43, 1), (157, 1), (87539, 1)] : List FactorBlock).map factorBlockValue).prod) = 11819515781 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_5
      · exact prime_oneHundredFortyFourEL_43
      · exact prime_oneHundredFortyFourEL_157
      · exact prime_oneHundredFortyFourEL_87539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 11819515781) ^ 5909757890 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 11819515781) ^ 2363903156 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 11819515781) ^ 274872460 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 11819515781) ^ 75283540 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 11819515781) ^ 135020 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_14757462491 : Nat.Prime 14757462491 := by
  apply lucas_primality 14757462491 (2 : ZMod 14757462491)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (101, 1), (809, 1), (18061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (101, 1), (809, 1), (18061, 1)] : List FactorBlock).map factorBlockValue).prod) = 14757462491 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_5
      · exact prime_oneHundredFortyFourEL_101
      · exact prime_oneHundredFortyFourEL_809
      · exact prime_oneHundredFortyFourEL_18061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 14757462491) ^ 7378731245 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 14757462491) ^ 2951492498 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 14757462491) ^ 146113490 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 14757462491) ^ 18241610 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 14757462491) ^ 817090 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_18976229401 : Nat.Prime 18976229401 := by
  apply lucas_primality 18976229401 (7 : ZMod 18976229401)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 2), (1123, 1), (28163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 2), (1123, 1), (28163, 1)] : List FactorBlock).map factorBlockValue).prod) = 18976229401 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_5
      · exact prime_oneHundredFortyFourEL_1123
      · exact prime_oneHundredFortyFourEL_28163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 18976229401) ^ 9488114700 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (7 : ZMod 18976229401) ^ 6325409800 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (7 : ZMod 18976229401) ^ 3795245880 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (7 : ZMod 18976229401) ^ 16897800 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (7 : ZMod 18976229401) ^ 673800 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_21532419833 : Nat.Prime 21532419833 := by
  apply lucas_primality 21532419833 (3 : ZMod 21532419833)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (11, 1), (1993, 1), (17539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (11, 1), (1993, 1), (17539, 1)] : List FactorBlock).map factorBlockValue).prod) = 21532419833 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_7
      · exact prime_oneHundredFortyFourEL_11
      · exact prime_oneHundredFortyFourEL_1993
      · exact prime_oneHundredFortyFourEL_17539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 21532419833) ^ 10766209916 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 21532419833) ^ 3076059976 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 21532419833) ^ 1957492712 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 21532419833) ^ 10804024 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 21532419833) ^ 1227688 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_23046330287 : Nat.Prime 23046330287 := by
  apply lucas_primality 23046330287 (7 : ZMod 23046330287)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (173, 1), (1583, 1), (6011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (173, 1), (1583, 1), (6011, 1)] : List FactorBlock).map factorBlockValue).prod) = 23046330287 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_7
      · exact prime_oneHundredFortyFourEL_173
      · exact prime_oneHundredFortyFourEL_1583
      · exact prime_oneHundredFortyFourEL_6011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 23046330287) ^ 11523165143 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (7 : ZMod 23046330287) ^ 3292332898 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (7 : ZMod 23046330287) ^ 133215782 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (7 : ZMod 23046330287) ^ 14558642 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (7 : ZMod 23046330287) ^ 3834026 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_23605829803 : Nat.Prime 23605829803 := by
  apply lucas_primality 23605829803 (2 : ZMod 23605829803)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (1311434989, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (1311434989, 1)] : List FactorBlock).map factorBlockValue).prod) = 23605829803 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_1311434989
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 23605829803) ^ 11802914901 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 23605829803) ^ 7868609934 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 23605829803) ^ 18 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_25734798431 : Nat.Prime 25734798431 := by
  apply lucas_primality 25734798431 (17 : ZMod 25734798431)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (233952713, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (233952713, 1)] : List FactorBlock).map factorBlockValue).prod) = 25734798431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_5
      · exact prime_oneHundredFortyFourEL_11
      · exact prime_oneHundredFortyFourEL_233952713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 25734798431) ^ 12867399215 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (17 : ZMod 25734798431) ^ 5146959686 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (17 : ZMod 25734798431) ^ 2339527130 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (17 : ZMod 25734798431) ^ 110 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_25790344861 : Nat.Prime 25790344861 := by
  apply lucas_primality 25790344861 (2 : ZMod 25790344861)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (61405583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (61405583, 1)] : List FactorBlock).map factorBlockValue).prod) = 25790344861 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_5
      · exact prime_oneHundredFortyFourEL_7
      · exact prime_oneHundredFortyFourEL_61405583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 25790344861) ^ 12895172430 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 25790344861) ^ 8596781620 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 25790344861) ^ 5158068972 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 25790344861) ^ 3684334980 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 25790344861) ^ 420 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_26049742289 : Nat.Prime 26049742289 := by
  apply lucas_primality 26049742289 (3 : ZMod 26049742289)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (41, 1), (39709973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (41, 1), (39709973, 1)] : List FactorBlock).map factorBlockValue).prod) = 26049742289 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_41
      · exact prime_oneHundredFortyFourEL_39709973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 26049742289) ^ 13024871144 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 26049742289) ^ 635359568 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 26049742289) ^ 656 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_26303065973 : Nat.Prime 26303065973 := by
  apply lucas_primality 26303065973 (2 : ZMod 26303065973)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (285902891, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (285902891, 1)] : List FactorBlock).map factorBlockValue).prod) = 26303065973 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_23
      · exact prime_oneHundredFortyFourEL_285902891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 26303065973) ^ 13151532986 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 26303065973) ^ 1143611564 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 26303065973) ^ 92 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_35264271901 : Nat.Prime 35264271901 := by
  apply lucas_primality 35264271901 (7 : ZMod 35264271901)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (11, 1), (13, 1), (822011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (11, 1), (13, 1), (822011, 1)] : List FactorBlock).map factorBlockValue).prod) = 35264271901 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_5
      · exact prime_oneHundredFortyFourEL_11
      · exact prime_oneHundredFortyFourEL_13
      · exact prime_oneHundredFortyFourEL_822011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 35264271901) ^ 17632135950 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (7 : ZMod 35264271901) ^ 11754757300 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (7 : ZMod 35264271901) ^ 7052854380 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (7 : ZMod 35264271901) ^ 3205842900 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (7 : ZMod 35264271901) ^ 2712636300 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (7 : ZMod 35264271901) ^ 42900 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_40869750521 : Nat.Prime 40869750521 := by
  apply lucas_primality 40869750521 (3 : ZMod 40869750521)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (47, 1), (89, 1), (244261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (47, 1), (89, 1), (244261, 1)] : List FactorBlock).map factorBlockValue).prod) = 40869750521 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_5
      · exact prime_oneHundredFortyFourEL_47
      · exact prime_oneHundredFortyFourEL_89
      · exact prime_oneHundredFortyFourEL_244261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 40869750521) ^ 20434875260 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 40869750521) ^ 8173950104 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 40869750521) ^ 869569160 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 40869750521) ^ 459210680 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 40869750521) ^ 167320 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_52656538663 : Nat.Prime 52656538663 := by
  apply lucas_primality 52656538663 (3 : ZMod 52656538663)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 2), (13, 1), (157, 1), (29251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 2), (13, 1), (157, 1), (29251, 1)] : List FactorBlock).map factorBlockValue).prod) = 52656538663 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_7
      · exact prime_oneHundredFortyFourEL_13
      · exact prime_oneHundredFortyFourEL_157
      · exact prime_oneHundredFortyFourEL_29251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 52656538663) ^ 26328269331 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 52656538663) ^ 17552179554 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 52656538663) ^ 7522362666 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 52656538663) ^ 4050502974 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 52656538663) ^ 335391966 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 52656538663) ^ 1800162 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_60673638397 : Nat.Prime 60673638397 := by
  apply lucas_primality 60673638397 (2 : ZMod 60673638397)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (722305219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (722305219, 1)] : List FactorBlock).map factorBlockValue).prod) = 60673638397 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_7
      · exact prime_oneHundredFortyFourEL_722305219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 60673638397) ^ 30336819198 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 60673638397) ^ 20224546132 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 60673638397) ^ 8667662628 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 60673638397) ^ 84 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_62891033057 : Nat.Prime 62891033057 := by
  apply lucas_primality 62891033057 (3 : ZMod 62891033057)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (1965344783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (1965344783, 1)] : List FactorBlock).map factorBlockValue).prod) = 62891033057 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_1965344783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 62891033057) ^ 31445516528 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 62891033057) ^ 32 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_70158716791 : Nat.Prime 70158716791 := by
  apply lucas_primality 70158716791 (3 : ZMod 70158716791)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (2338623893, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (2338623893, 1)] : List FactorBlock).map factorBlockValue).prod) = 70158716791 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_5
      · exact prime_oneHundredFortyFourEL_2338623893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 70158716791) ^ 35079358395 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 70158716791) ^ 23386238930 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 70158716791) ^ 14031743358 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 70158716791) ^ 30 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_92372079169 : Nat.Prime 92372079169 := by
  apply lucas_primality 92372079169 (11 : ZMod 92372079169)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (160368193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (160368193, 1)] : List FactorBlock).map factorBlockValue).prod) = 92372079169 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_160368193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 92372079169) ^ 46186039584 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (11 : ZMod 92372079169) ^ 30790693056 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (11 : ZMod 92372079169) ^ 576 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_100070648269 : Nat.Prime 100070648269 := by
  apply lucas_primality 100070648269 (2 : ZMod 100070648269)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (31, 2), (1321, 1), (6569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (31, 2), (1321, 1), (6569, 1)] : List FactorBlock).map factorBlockValue).prod) = 100070648269 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_31
      · exact prime_oneHundredFortyFourEL_1321
      · exact prime_oneHundredFortyFourEL_6569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 100070648269) ^ 50035324134 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 100070648269) ^ 33356882756 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 100070648269) ^ 3228085428 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 100070648269) ^ 75753708 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 100070648269) ^ 15233772 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_100607785529 : Nat.Prime 100607785529 := by
  apply lucas_primality 100607785529 (3 : ZMod 100607785529)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (1009, 1), (12463799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (1009, 1), (12463799, 1)] : List FactorBlock).map factorBlockValue).prod) = 100607785529 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_1009
      · exact prime_oneHundredFortyFourEL_12463799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 100607785529) ^ 50303892764 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 100607785529) ^ 99710392 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 100607785529) ^ 8072 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_108695598541 : Nat.Prime 108695598541 := by
  apply lucas_primality 108695598541 (2 : ZMod 108695598541)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (89, 1), (983, 1), (20707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (89, 1), (983, 1), (20707, 1)] : List FactorBlock).map factorBlockValue).prod) = 108695598541 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_5
      · exact prime_oneHundredFortyFourEL_89
      · exact prime_oneHundredFortyFourEL_983
      · exact prime_oneHundredFortyFourEL_20707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 108695598541) ^ 54347799270 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 108695598541) ^ 36231866180 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 108695598541) ^ 21739119708 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 108695598541) ^ 1221298860 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 108695598541) ^ 110575380 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 108695598541) ^ 5249220 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_126671154767 : Nat.Prime 126671154767 := by
  apply lucas_primality 126671154767 (5 : ZMod 126671154767)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (17, 2), (29, 1), (581311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (17, 2), (29, 1), (581311, 1)] : List FactorBlock).map factorBlockValue).prod) = 126671154767 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_13
      · exact prime_oneHundredFortyFourEL_17
      · exact prime_oneHundredFortyFourEL_29
      · exact prime_oneHundredFortyFourEL_581311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 126671154767) ^ 63335577383 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 126671154767) ^ 9743934982 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 126671154767) ^ 7451244398 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 126671154767) ^ 4367970854 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 126671154767) ^ 217906 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_150363951973 : Nat.Prime 150363951973 := by
  apply lucas_primality 150363951973 (2 : ZMod 150363951973)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (73, 1), (13203719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (73, 1), (13203719, 1)] : List FactorBlock).map factorBlockValue).prod) = 150363951973 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_13
      · exact prime_oneHundredFortyFourEL_73
      · exact prime_oneHundredFortyFourEL_13203719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 150363951973) ^ 75181975986 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 150363951973) ^ 50121317324 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 150363951973) ^ 11566457844 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 150363951973) ^ 2059780164 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 150363951973) ^ 11388 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_157705373099 : Nat.Prime 157705373099 := by
  apply lucas_primality 157705373099 (2 : ZMod 157705373099)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (13, 1), (71, 1), (1743487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (13, 1), (71, 1), (1743487, 1)] : List FactorBlock).map factorBlockValue).prod) = 157705373099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_7
      · exact prime_oneHundredFortyFourEL_13
      · exact prime_oneHundredFortyFourEL_71
      · exact prime_oneHundredFortyFourEL_1743487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 157705373099) ^ 78852686549 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 157705373099) ^ 22529339014 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 157705373099) ^ 12131182546 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 157705373099) ^ 2221202438 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 157705373099) ^ 90454 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_215565659143 : Nat.Prime 215565659143 := by
  apply lucas_primality 215565659143 (3 : ZMod 215565659143)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (47, 1), (764417231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (47, 1), (764417231, 1)] : List FactorBlock).map factorBlockValue).prod) = 215565659143 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_47
      · exact prime_oneHundredFortyFourEL_764417231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 215565659143) ^ 107782829571 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 215565659143) ^ 71855219714 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 215565659143) ^ 4586503386 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 215565659143) ^ 282 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_243364641461 : Nat.Prime 243364641461 := by
  apply lucas_primality 243364641461 (2 : ZMod 243364641461)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (19, 1), (640433267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (19, 1), (640433267, 1)] : List FactorBlock).map factorBlockValue).prod) = 243364641461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_5
      · exact prime_oneHundredFortyFourEL_19
      · exact prime_oneHundredFortyFourEL_640433267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 243364641461) ^ 121682320730 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 243364641461) ^ 48672928292 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 243364641461) ^ 12808665340 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 243364641461) ^ 380 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_255217709441 : Nat.Prime 255217709441 := by
  apply lucas_primality 255217709441 (3 : ZMod 255217709441)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (5, 1), (53, 1), (7524107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (5, 1), (53, 1), (7524107, 1)] : List FactorBlock).map factorBlockValue).prod) = 255217709441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_5
      · exact prime_oneHundredFortyFourEL_53
      · exact prime_oneHundredFortyFourEL_7524107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 255217709441) ^ 127608854720 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 255217709441) ^ 51043541888 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 255217709441) ^ 4815428480 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 255217709441) ^ 33920 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_273132904279 : Nat.Prime 273132904279 := by
  apply lucas_primality 273132904279 (11 : ZMod 273132904279)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (3501703901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (3501703901, 1)] : List FactorBlock).map factorBlockValue).prod) = 273132904279 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_13
      · exact prime_oneHundredFortyFourEL_3501703901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 273132904279) ^ 136566452139 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (11 : ZMod 273132904279) ^ 91044301426 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (11 : ZMod 273132904279) ^ 21010223406 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (11 : ZMod 273132904279) ^ 78 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_279774663671 : Nat.Prime 279774663671 := by
  apply lucas_primality 279774663671 (19 : ZMod 279774663671)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (751, 1), (37253617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (751, 1), (37253617, 1)] : List FactorBlock).map factorBlockValue).prod) = 279774663671 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_5
      · exact prime_oneHundredFortyFourEL_751
      · exact prime_oneHundredFortyFourEL_37253617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 279774663671) ^ 139887331835 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (19 : ZMod 279774663671) ^ 55954932734 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (19 : ZMod 279774663671) ^ 372536170 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (19 : ZMod 279774663671) ^ 7510 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_294096103603 : Nat.Prime 294096103603 := by
  apply lucas_primality 294096103603 (2 : ZMod 294096103603)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (409, 1), (557, 1), (4391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (409, 1), (557, 1), (4391, 1)] : List FactorBlock).map factorBlockValue).prod) = 294096103603 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_7
      · exact prime_oneHundredFortyFourEL_409
      · exact prime_oneHundredFortyFourEL_557
      · exact prime_oneHundredFortyFourEL_4391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 294096103603) ^ 147048051801 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 294096103603) ^ 98032034534 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 294096103603) ^ 42013729086 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 294096103603) ^ 719061378 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 294096103603) ^ 528000186 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 294096103603) ^ 66977022 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_323947351769 : Nat.Prime 323947351769 := by
  apply lucas_primality 323947351769 (3 : ZMod 323947351769)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (2803, 1), (14446457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (2803, 1), (14446457, 1)] : List FactorBlock).map factorBlockValue).prod) = 323947351769 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_2803
      · exact prime_oneHundredFortyFourEL_14446457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 323947351769) ^ 161973675884 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 323947351769) ^ 115571656 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 323947351769) ^ 22424 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_324699246947 : Nat.Prime 324699246947 := by
  apply lucas_primality 324699246947 (2 : ZMod 324699246947)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (659, 1), (1289, 1), (191123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (659, 1), (1289, 1), (191123, 1)] : List FactorBlock).map factorBlockValue).prod) = 324699246947 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_659
      · exact prime_oneHundredFortyFourEL_1289
      · exact prime_oneHundredFortyFourEL_191123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 324699246947) ^ 162349623473 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 324699246947) ^ 492715094 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 324699246947) ^ 251900114 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 324699246947) ^ 1698902 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_326958004169 : Nat.Prime 326958004169 := by
  apply lucas_primality 326958004169 (3 : ZMod 326958004169)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (40869750521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (40869750521, 1)] : List FactorBlock).map factorBlockValue).prod) = 326958004169 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_40869750521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 326958004169) ^ 163479002084 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 326958004169) ^ 8 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_395569541791 : Nat.Prime 395569541791 := by
  apply lucas_primality 395569541791 (3 : ZMod 395569541791)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (5, 1), (23, 2), (923171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (5, 1), (23, 2), (923171, 1)] : List FactorBlock).map factorBlockValue).prod) = 395569541791 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_5
      · exact prime_oneHundredFortyFourEL_23
      · exact prime_oneHundredFortyFourEL_923171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 395569541791) ^ 197784770895 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 395569541791) ^ 131856513930 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 395569541791) ^ 79113908358 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 395569541791) ^ 17198675730 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 395569541791) ^ 428490 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_457569029521 : Nat.Prime 457569029521 := by
  apply lucas_primality 457569029521 (11 : ZMod 457569029521)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5, 1), (59, 1), (2819, 1), (3821, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5, 1), (59, 1), (2819, 1), (3821, 1)] : List FactorBlock).map factorBlockValue).prod) = 457569029521 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_5
      · exact prime_oneHundredFortyFourEL_59
      · exact prime_oneHundredFortyFourEL_2819
      · exact prime_oneHundredFortyFourEL_3821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 457569029521) ^ 228784514760 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (11 : ZMod 457569029521) ^ 152523009840 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (11 : ZMod 457569029521) ^ 91513805904 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (11 : ZMod 457569029521) ^ 7755407280 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (11 : ZMod 457569029521) ^ 162316080 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (11 : ZMod 457569029521) ^ 119751120 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_497251057109 : Nat.Prime 497251057109 := by
  apply lucas_primality 497251057109 (2 : ZMod 497251057109)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (739, 1), (12939811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (739, 1), (12939811, 1)] : List FactorBlock).map factorBlockValue).prod) = 497251057109 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_13
      · exact prime_oneHundredFortyFourEL_739
      · exact prime_oneHundredFortyFourEL_12939811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 497251057109) ^ 248625528554 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 497251057109) ^ 38250081316 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 497251057109) ^ 672870172 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 497251057109) ^ 38428 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_626696252953 : Nat.Prime 626696252953 := by
  apply lucas_primality 626696252953 (5 : ZMod 626696252953)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 2), (11, 1), (43, 1), (1126649, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 2), (11, 1), (43, 1), (1126649, 1)] : List FactorBlock).map factorBlockValue).prod) = 626696252953 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_7
      · exact prime_oneHundredFortyFourEL_11
      · exact prime_oneHundredFortyFourEL_43
      · exact prime_oneHundredFortyFourEL_1126649
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 626696252953) ^ 313348126476 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 626696252953) ^ 208898750984 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 626696252953) ^ 89528036136 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 626696252953) ^ 56972386632 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 626696252953) ^ 14574331464 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 626696252953) ^ 556248 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_749523766273 : Nat.Prime 749523766273 := by
  apply lucas_primality 749523766273 (5 : ZMod 749523766273)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 10), (3, 1), (47, 1), (821, 1), (6323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 10), (3, 1), (47, 1), (821, 1), (6323, 1)] : List FactorBlock).map factorBlockValue).prod) = 749523766273 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_47
      · exact prime_oneHundredFortyFourEL_821
      · exact prime_oneHundredFortyFourEL_6323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 749523766273) ^ 374761883136 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 749523766273) ^ 249841255424 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 749523766273) ^ 15947314176 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 749523766273) ^ 912940032 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 749523766273) ^ 118539264 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_1491301720847 : Nat.Prime 1491301720847 := by
  apply lucas_primality 1491301720847 (7 : ZMod 1491301720847)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (17, 1), (6265973617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (17, 1), (6265973617, 1)] : List FactorBlock).map factorBlockValue).prod) = 1491301720847 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_7
      · exact prime_oneHundredFortyFourEL_17
      · exact prime_oneHundredFortyFourEL_6265973617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 1491301720847) ^ 745650860423 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (7 : ZMod 1491301720847) ^ 213043102978 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (7 : ZMod 1491301720847) ^ 87723630638 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (7 : ZMod 1491301720847) ^ 238 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_2517652494991 : Nat.Prime 2517652494991 := by
  apply lucas_primality 2517652494991 (3 : ZMod 2517652494991)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (107, 1), (4993, 1), (52361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (107, 1), (4993, 1), (52361, 1)] : List FactorBlock).map factorBlockValue).prod) = 2517652494991 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_5
      · exact prime_oneHundredFortyFourEL_107
      · exact prime_oneHundredFortyFourEL_4993
      · exact prime_oneHundredFortyFourEL_52361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2517652494991) ^ 1258826247495 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 2517652494991) ^ 839217498330 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 2517652494991) ^ 503530498998 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 2517652494991) ^ 23529462570 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 2517652494991) ^ 504236430 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 2517652494991) ^ 48082590 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_3367618405969 : Nat.Prime 3367618405969 := by
  apply lucas_primality 3367618405969 (7 : ZMod 3367618405969)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (70158716791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (70158716791, 1)] : List FactorBlock).map factorBlockValue).prod) = 3367618405969 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_70158716791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 3367618405969) ^ 1683809202984 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (7 : ZMod 3367618405969) ^ 1122539468656 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (7 : ZMod 3367618405969) ^ 48 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_3662228970263 : Nat.Prime 3662228970263 := by
  apply lucas_primality 3662228970263 (5 : ZMod 3662228970263)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (71, 1), (25790344861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (71, 1), (25790344861, 1)] : List FactorBlock).map factorBlockValue).prod) = 3662228970263 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_71
      · exact prime_oneHundredFortyFourEL_25790344861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 3662228970263) ^ 1831114485131 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 3662228970263) ^ 51580689722 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 3662228970263) ^ 142 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_3687111941479 : Nat.Prime 3687111941479 := by
  apply lucas_primality 3687111941479 (3 : ZMod 3687111941479)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (17, 1), (37, 1), (139568171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (17, 1), (37, 1), (139568171, 1)] : List FactorBlock).map factorBlockValue).prod) = 3687111941479 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_7
      · exact prime_oneHundredFortyFourEL_17
      · exact prime_oneHundredFortyFourEL_37
      · exact prime_oneHundredFortyFourEL_139568171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3687111941479) ^ 1843555970739 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 3687111941479) ^ 1229037313826 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 3687111941479) ^ 526730277354 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 3687111941479) ^ 216888937734 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 3687111941479) ^ 99651674094 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 3687111941479) ^ 26418 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_3722103952517 : Nat.Prime 3722103952517 := by
  apply lucas_primality 3722103952517 (2 : ZMod 3722103952517)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (31, 1), (4951, 1), (6062809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (31, 1), (4951, 1), (6062809, 1)] : List FactorBlock).map factorBlockValue).prod) = 3722103952517 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_31
      · exact prime_oneHundredFortyFourEL_4951
      · exact prime_oneHundredFortyFourEL_6062809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3722103952517) ^ 1861051976258 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 3722103952517) ^ 120067869436 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 3722103952517) ^ 751788316 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 3722103952517) ^ 613924 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_4014078193691 : Nat.Prime 4014078193691 := by
  apply lucas_primality 4014078193691 (2 : ZMod 4014078193691)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (829, 1), (1051, 1), (460711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (829, 1), (1051, 1), (460711, 1)] : List FactorBlock).map factorBlockValue).prod) = 4014078193691 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_5
      · exact prime_oneHundredFortyFourEL_829
      · exact prime_oneHundredFortyFourEL_1051
      · exact prime_oneHundredFortyFourEL_460711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4014078193691) ^ 2007039096845 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 4014078193691) ^ 802815638738 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 4014078193691) ^ 4842072610 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 4014078193691) ^ 3819294190 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 4014078193691) ^ 8712790 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_4237371767197 : Nat.Prime 4237371767197 := by
  apply lucas_primality 4237371767197 (2 : ZMod 4237371767197)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5051, 1), (23303261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5051, 1), (23303261, 1)] : List FactorBlock).map factorBlockValue).prod) = 4237371767197 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_5051
      · exact prime_oneHundredFortyFourEL_23303261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4237371767197) ^ 2118685883598 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 4237371767197) ^ 1412457255732 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 4237371767197) ^ 838917396 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 4237371767197) ^ 181836 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_4633170873559 : Nat.Prime 4633170873559 := by
  apply lucas_primality 4633170873559 (3 : ZMod 4633170873559)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (61, 1), (83, 1), (152517311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (61, 1), (83, 1), (152517311, 1)] : List FactorBlock).map factorBlockValue).prod) = 4633170873559 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_61
      · exact prime_oneHundredFortyFourEL_83
      · exact prime_oneHundredFortyFourEL_152517311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4633170873559) ^ 2316585436779 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 4633170873559) ^ 1544390291186 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 4633170873559) ^ 75953620878 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 4633170873559) ^ 55821335826 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 4633170873559) ^ 30378 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_5554715472751 : Nat.Prime 5554715472751 := by
  apply lucas_primality 5554715472751 (3 : ZMod 5554715472751)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 3), (7406287297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 3), (7406287297, 1)] : List FactorBlock).map factorBlockValue).prod) = 5554715472751 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_5
      · exact prime_oneHundredFortyFourEL_7406287297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 5554715472751) ^ 2777357736375 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 5554715472751) ^ 1851571824250 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 5554715472751) ^ 1110943094550 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 5554715472751) ^ 750 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_6232920282937 : Nat.Prime 6232920282937 := by
  apply lucas_primality 6232920282937 (7 : ZMod 6232920282937)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (19, 1), (1518742759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (19, 1), (1518742759, 1)] : List FactorBlock).map factorBlockValue).prod) = 6232920282937 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_19
      · exact prime_oneHundredFortyFourEL_1518742759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 6232920282937) ^ 3116460141468 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (7 : ZMod 6232920282937) ^ 2077640094312 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (7 : ZMod 6232920282937) ^ 328048435944 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (7 : ZMod 6232920282937) ^ 4104 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_6260335829159 : Nat.Prime 6260335829159 := by
  apply lucas_primality 6260335829159 (11 : ZMod 6260335829159)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (109, 1), (1381, 1), (1223203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (109, 1), (1381, 1), (1223203, 1)] : List FactorBlock).map factorBlockValue).prod) = 6260335829159 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_17
      · exact prime_oneHundredFortyFourEL_109
      · exact prime_oneHundredFortyFourEL_1381
      · exact prime_oneHundredFortyFourEL_1223203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 6260335829159) ^ 3130167914579 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (11 : ZMod 6260335829159) ^ 368255048774 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (11 : ZMod 6260335829159) ^ 57434273662 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (11 : ZMod 6260335829159) ^ 4533190318 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (11 : ZMod 6260335829159) ^ 5117986 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_6638390712727 : Nat.Prime 6638390712727 := by
  apply lucas_primality 6638390712727 (3 : ZMod 6638390712727)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (76487, 1), (628921, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (76487, 1), (628921, 1)] : List FactorBlock).map factorBlockValue).prod) = 6638390712727 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_23
      · exact prime_oneHundredFortyFourEL_76487
      · exact prime_oneHundredFortyFourEL_628921
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 6638390712727) ^ 3319195356363 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 6638390712727) ^ 2212796904242 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 6638390712727) ^ 288625683162 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 6638390712727) ^ 86791098 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 6638390712727) ^ 10555206 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_9785892628279 : Nat.Prime 9785892628279 := by
  apply lucas_primality 9785892628279 (6 : ZMod 9785892628279)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (13, 1), (229, 1), (20291147, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (13, 1), (229, 1), (20291147, 1)] : List FactorBlock).map factorBlockValue).prod) = 9785892628279 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_13
      · exact prime_oneHundredFortyFourEL_229
      · exact prime_oneHundredFortyFourEL_20291147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 9785892628279) ^ 4892946314139 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (6 : ZMod 9785892628279) ^ 3261964209426 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (6 : ZMod 9785892628279) ^ 752760971406 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (6 : ZMod 9785892628279) ^ 42733155582 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (6 : ZMod 9785892628279) ^ 482274 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_10937871458779 : Nat.Prime 10937871458779 := by
  apply lucas_primality 10937871458779 (3 : ZMod 10937871458779)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (13523, 1), (12255071, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (13523, 1), (12255071, 1)] : List FactorBlock).map factorBlockValue).prod) = 10937871458779 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_11
      · exact prime_oneHundredFortyFourEL_13523
      · exact prime_oneHundredFortyFourEL_12255071
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 10937871458779) ^ 5468935729389 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 10937871458779) ^ 3645957152926 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 10937871458779) ^ 994351950798 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 10937871458779) ^ 808834686 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 10937871458779) ^ 892518 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_11013696930283 : Nat.Prime 11013696930283 := by
  apply lucas_primality 11013696930283 (5 : ZMod 11013696930283)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (347, 1), (23929, 1), (221069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (347, 1), (23929, 1), (221069, 1)] : List FactorBlock).map factorBlockValue).prod) = 11013696930283 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_347
      · exact prime_oneHundredFortyFourEL_23929
      · exact prime_oneHundredFortyFourEL_221069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 11013696930283) ^ 5506848465141 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 11013696930283) ^ 3671232310094 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 11013696930283) ^ 31739760606 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 11013696930283) ^ 460265658 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 11013696930283) ^ 49820178 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_11446482564799 : Nat.Prime 11446482564799 := by
  apply lucas_primality 11446482564799 (7 : ZMod 11446482564799)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (463, 1), (937, 1), (141853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (463, 1), (937, 1), (141853, 1)] : List FactorBlock).map factorBlockValue).prod) = 11446482564799 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_31
      · exact prime_oneHundredFortyFourEL_463
      · exact prime_oneHundredFortyFourEL_937
      · exact prime_oneHundredFortyFourEL_141853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 11446482564799) ^ 5723241282399 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (7 : ZMod 11446482564799) ^ 3815494188266 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (7 : ZMod 11446482564799) ^ 369241373058 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (7 : ZMod 11446482564799) ^ 24722424546 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (7 : ZMod 11446482564799) ^ 12216096654 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (7 : ZMod 11446482564799) ^ 80692566 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_13971226936099 : Nat.Prime 13971226936099 := by
  apply lucas_primality 13971226936099 (2 : ZMod 13971226936099)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (21617, 1), (6336347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (21617, 1), (6336347, 1)] : List FactorBlock).map factorBlockValue).prod) = 13971226936099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_17
      · exact prime_oneHundredFortyFourEL_21617
      · exact prime_oneHundredFortyFourEL_6336347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 13971226936099) ^ 6985613468049 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 13971226936099) ^ 4657075645366 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 13971226936099) ^ 821836878594 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 13971226936099) ^ 646307394 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 13971226936099) ^ 2204934 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_14286766865669 : Nat.Prime 14286766865669 := by
  apply lucas_primality 14286766865669 (2 : ZMod 14286766865669)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (324699246947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (324699246947, 1)] : List FactorBlock).map factorBlockValue).prod) = 14286766865669 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_11
      · exact prime_oneHundredFortyFourEL_324699246947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 14286766865669) ^ 7143383432834 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 14286766865669) ^ 1298796987788 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 14286766865669) ^ 44 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_14305552217941 : Nat.Prime 14305552217941 := by
  apply lucas_primality 14305552217941 (2 : ZMod 14305552217941)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (6427, 1), (37097537, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (6427, 1), (37097537, 1)] : List FactorBlock).map factorBlockValue).prod) = 14305552217941 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_5
      · exact prime_oneHundredFortyFourEL_6427
      · exact prime_oneHundredFortyFourEL_37097537
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 14305552217941) ^ 7152776108970 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 14305552217941) ^ 4768517405980 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 14305552217941) ^ 2861110443588 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 14305552217941) ^ 2225852220 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 14305552217941) ^ 385620 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_14489574872303 : Nat.Prime 14489574872303 := by
  apply lucas_primality 14489574872303 (5 : ZMod 14489574872303)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (31, 1), (859, 1), (1301, 1), (7211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (31, 1), (859, 1), (1301, 1), (7211, 1)] : List FactorBlock).map factorBlockValue).prod) = 14489574872303 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_29
      · exact prime_oneHundredFortyFourEL_31
      · exact prime_oneHundredFortyFourEL_859
      · exact prime_oneHundredFortyFourEL_1301
      · exact prime_oneHundredFortyFourEL_7211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 14489574872303) ^ 7244787436151 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 14489574872303) ^ 499640512838 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 14489574872303) ^ 467405641042 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 14489574872303) ^ 16867956778 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 14489574872303) ^ 11137259702 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 14489574872303) ^ 2009371082 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_15239370115789 : Nat.Prime 15239370115789 := by
  apply lucas_primality 15239370115789 (2 : ZMod 15239370115789)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (13, 1), (547, 1), (25512737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (13, 1), (547, 1), (25512737, 1)] : List FactorBlock).map factorBlockValue).prod) = 15239370115789 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_7
      · exact prime_oneHundredFortyFourEL_13
      · exact prime_oneHundredFortyFourEL_547
      · exact prime_oneHundredFortyFourEL_25512737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 15239370115789) ^ 7619685057894 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 15239370115789) ^ 5079790038596 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 15239370115789) ^ 2177052873684 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 15239370115789) ^ 1172259239676 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 15239370115789) ^ 27859908804 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 15239370115789) ^ 597324 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_17139873932003 : Nat.Prime 17139873932003 := by
  apply lucas_primality 17139873932003 (2 : ZMod 17139873932003)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (599, 1), (8737, 1), (34841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (599, 1), (8737, 1), (34841, 1)] : List FactorBlock).map factorBlockValue).prod) = 17139873932003 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_47
      · exact prime_oneHundredFortyFourEL_599
      · exact prime_oneHundredFortyFourEL_8737
      · exact prime_oneHundredFortyFourEL_34841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 17139873932003) ^ 8569936966001 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 17139873932003) ^ 364678168766 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 17139873932003) ^ 28614146798 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 17139873932003) ^ 1961757346 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 17139873932003) ^ 491945522 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_18451138510529 : Nat.Prime 18451138510529 := by
  apply lucas_primality 18451138510529 (3 : ZMod 18451138510529)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (311, 1), (927006557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (311, 1), (927006557, 1)] : List FactorBlock).map factorBlockValue).prod) = 18451138510529 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_311
      · exact prime_oneHundredFortyFourEL_927006557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 18451138510529) ^ 9225569255264 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 18451138510529) ^ 59328419648 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 18451138510529) ^ 19904 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_23194197396883 : Nat.Prime 23194197396883 := by
  apply lucas_primality 23194197396883 (2 : ZMod 23194197396883)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (103, 1), (127, 1), (98506729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (103, 1), (127, 1), (98506729, 1)] : List FactorBlock).map factorBlockValue).prod) = 23194197396883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_103
      · exact prime_oneHundredFortyFourEL_127
      · exact prime_oneHundredFortyFourEL_98506729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 23194197396883) ^ 11597098698441 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 23194197396883) ^ 7731399132294 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 23194197396883) ^ 225186382494 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 23194197396883) ^ 182631475566 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 23194197396883) ^ 235458 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_23642614645087 : Nat.Prime 23642614645087 := by
  apply lucas_primality 23642614645087 (3 : ZMod 23642614645087)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (71, 1), (157, 1), (353497423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (71, 1), (157, 1), (353497423, 1)] : List FactorBlock).map factorBlockValue).prod) = 23642614645087 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_71
      · exact prime_oneHundredFortyFourEL_157
      · exact prime_oneHundredFortyFourEL_353497423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 23642614645087) ^ 11821307322543 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 23642614645087) ^ 7880871548362 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 23642614645087) ^ 332994572466 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 23642614645087) ^ 150589902198 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 23642614645087) ^ 66882 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_28979149744607 : Nat.Prime 28979149744607 := by
  apply lucas_primality 28979149744607 (5 : ZMod 28979149744607)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (14489574872303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (14489574872303, 1)] : List FactorBlock).map factorBlockValue).prod) = 28979149744607 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_14489574872303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 28979149744607) ^ 14489574872303 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 28979149744607) ^ 2 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_32052710477647 : Nat.Prime 32052710477647 := by
  apply lucas_primality 32052710477647 (3 : ZMod 32052710477647)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (8819, 1), (67305671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (8819, 1), (67305671, 1)] : List FactorBlock).map factorBlockValue).prod) = 32052710477647 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_8819
      · exact prime_oneHundredFortyFourEL_67305671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 32052710477647) ^ 16026355238823 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 32052710477647) ^ 10684236825882 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 32052710477647) ^ 3634506234 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 32052710477647) ^ 476226 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_32520964175027 : Nat.Prime 32520964175027 := by
  apply lucas_primality 32520964175027 (2 : ZMod 32520964175027)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (53, 1), (1151, 1), (266552171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (53, 1), (1151, 1), (266552171, 1)] : List FactorBlock).map factorBlockValue).prod) = 32520964175027 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_53
      · exact prime_oneHundredFortyFourEL_1151
      · exact prime_oneHundredFortyFourEL_266552171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 32520964175027) ^ 16260482087513 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 32520964175027) ^ 613603097642 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 32520964175027) ^ 28254530126 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 32520964175027) ^ 122006 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_38918314979767 : Nat.Prime 38918314979767 := by
  apply lucas_primality 38918314979767 (13 : ZMod 38918314979767)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (83, 1), (26049742289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (83, 1), (26049742289, 1)] : List FactorBlock).map factorBlockValue).prod) = 38918314979767 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_83
      · exact prime_oneHundredFortyFourEL_26049742289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 38918314979767) ^ 19459157489883 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (13 : ZMod 38918314979767) ^ 12972771659922 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (13 : ZMod 38918314979767) ^ 468895361202 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (13 : ZMod 38918314979767) ^ 1494 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_45752552594669 : Nat.Prime 45752552594669 := by
  apply lucas_primality 45752552594669 (2 : ZMod 45752552594669)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (47, 1), (243364641461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (47, 1), (243364641461, 1)] : List FactorBlock).map factorBlockValue).prod) = 45752552594669 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_47
      · exact prime_oneHundredFortyFourEL_243364641461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 45752552594669) ^ 22876276297334 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 45752552594669) ^ 973458565844 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 45752552594669) ^ 188 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_56777166273769 : Nat.Prime 56777166273769 := by
  apply lucas_primality 56777166273769 (11 : ZMod 56777166273769)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (191, 1), (461, 1), (26867557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (191, 1), (461, 1), (26867557, 1)] : List FactorBlock).map factorBlockValue).prod) = 56777166273769 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_191
      · exact prime_oneHundredFortyFourEL_461
      · exact prime_oneHundredFortyFourEL_26867557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 56777166273769) ^ 28388583136884 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (11 : ZMod 56777166273769) ^ 18925722091256 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (11 : ZMod 56777166273769) ^ 297262650648 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (11 : ZMod 56777166273769) ^ 123160881288 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (11 : ZMod 56777166273769) ^ 2113224 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_64323921637009 : Nat.Prime 64323921637009 := by
  apply lucas_primality 64323921637009 (13 : ZMod 64323921637009)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (11, 1), (41, 1), (990452107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (11, 1), (41, 1), (990452107, 1)] : List FactorBlock).map factorBlockValue).prod) = 64323921637009 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_11
      · exact prime_oneHundredFortyFourEL_41
      · exact prime_oneHundredFortyFourEL_990452107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 64323921637009) ^ 32161960818504 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (13 : ZMod 64323921637009) ^ 21441307212336 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (13 : ZMod 64323921637009) ^ 5847629239728 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (13 : ZMod 64323921637009) ^ 1568876137488 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (13 : ZMod 64323921637009) ^ 64944 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_80677106545561 : Nat.Prime 80677106545561 := by
  apply lucas_primality 80677106545561 (13 : ZMod 80677106545561)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (7, 1), (29873, 1), (3215083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (7, 1), (29873, 1), (3215083, 1)] : List FactorBlock).map factorBlockValue).prod) = 80677106545561 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_5
      · exact prime_oneHundredFortyFourEL_7
      · exact prime_oneHundredFortyFourEL_29873
      · exact prime_oneHundredFortyFourEL_3215083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 80677106545561) ^ 40338553272780 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (13 : ZMod 80677106545561) ^ 26892368848520 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (13 : ZMod 80677106545561) ^ 16135421309112 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (13 : ZMod 80677106545561) ^ 11525300935080 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (13 : ZMod 80677106545561) ^ 2700669720 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (13 : ZMod 80677106545561) ^ 25093320 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_85298847890759 : Nat.Prime 85298847890759 := by
  apply lucas_primality 85298847890759 (17 : ZMod 85298847890759)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (233, 1), (877, 1), (10985101, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (233, 1), (877, 1), (10985101, 1)] : List FactorBlock).map factorBlockValue).prod) = 85298847890759 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_19
      · exact prime_oneHundredFortyFourEL_233
      · exact prime_oneHundredFortyFourEL_877
      · exact prime_oneHundredFortyFourEL_10985101
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 85298847890759) ^ 42649423945379 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (17 : ZMod 85298847890759) ^ 4489413046882 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (17 : ZMod 85298847890759) ^ 366089475926 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (17 : ZMod 85298847890759) ^ 97262084254 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (17 : ZMod 85298847890759) ^ 7764958 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_99805395286837 : Nat.Prime 99805395286837 := by
  apply lucas_primality 99805395286837 (5 : ZMod 99805395286837)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (17, 1), (139, 1), (6067, 1), (193381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (17, 1), (139, 1), (6067, 1), (193381, 1)] : List FactorBlock).map factorBlockValue).prod) = 99805395286837 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_17
      · exact prime_oneHundredFortyFourEL_139
      · exact prime_oneHundredFortyFourEL_6067
      · exact prime_oneHundredFortyFourEL_193381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 99805395286837) ^ 49902697643418 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 99805395286837) ^ 33268465095612 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 99805395286837) ^ 5870905605108 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 99805395286837) ^ 718024426524 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 99805395286837) ^ 16450534908 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 99805395286837) ^ 516107556 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_113993486613649 : Nat.Prime 113993486613649 := by
  apply lucas_primality 113993486613649 (7 : ZMod 113993486613649)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (19, 1), (317, 1), (131433079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (19, 1), (317, 1), (131433079, 1)] : List FactorBlock).map factorBlockValue).prod) = 113993486613649 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_19
      · exact prime_oneHundredFortyFourEL_317
      · exact prime_oneHundredFortyFourEL_131433079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 113993486613649) ^ 56996743306824 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (7 : ZMod 113993486613649) ^ 37997828871216 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (7 : ZMod 113993486613649) ^ 5999657190192 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (7 : ZMod 113993486613649) ^ 359600904144 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (7 : ZMod 113993486613649) ^ 867312 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_114688177114201 : Nat.Prime 114688177114201 := by
  apply lucas_primality 114688177114201 (13 : ZMod 114688177114201)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 2), (5179, 1), (36908083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 2), (5179, 1), (36908083, 1)] : List FactorBlock).map factorBlockValue).prod) = 114688177114201 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_5
      · exact prime_oneHundredFortyFourEL_5179
      · exact prime_oneHundredFortyFourEL_36908083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 114688177114201) ^ 57344088557100 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (13 : ZMod 114688177114201) ^ 38229392371400 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (13 : ZMod 114688177114201) ^ 22937635422840 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (13 : ZMod 114688177114201) ^ 22144849800 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (13 : ZMod 114688177114201) ^ 3107400 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_130417135331503 : Nat.Prime 130417135331503 := by
  apply lucas_primality 130417135331503 (3 : ZMod 130417135331503)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 1), (749523766273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 1), (749523766273, 1)] : List FactorBlock).map factorBlockValue).prod) = 130417135331503 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_29
      · exact prime_oneHundredFortyFourEL_749523766273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 130417135331503) ^ 65208567665751 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 130417135331503) ^ 43472378443834 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 130417135331503) ^ 4497142597638 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 130417135331503) ^ 174 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_148631737990633 : Nat.Prime 148631737990633 := by
  apply lucas_primality 148631737990633 (10 : ZMod 148631737990633)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 1), (47, 1), (691, 1), (14668343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 1), (47, 1), (691, 1), (14668343, 1)] : List FactorBlock).map factorBlockValue).prod) = 148631737990633 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_13
      · exact prime_oneHundredFortyFourEL_47
      · exact prime_oneHundredFortyFourEL_691
      · exact prime_oneHundredFortyFourEL_14668343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 148631737990633) ^ 74315868995316 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (10 : ZMod 148631737990633) ^ 49543912663544 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (10 : ZMod 148631737990633) ^ 11433210614664 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (10 : ZMod 148631737990633) ^ 3162377404056 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (10 : ZMod 148631737990633) ^ 215096581752 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (10 : ZMod 148631737990633) ^ 10132824 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_152360405087833 : Nat.Prime 152360405087833 := by
  apply lucas_primality 152360405087833 (5 : ZMod 152360405087833)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (557, 1), (1266377461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (557, 1), (1266377461, 1)] : List FactorBlock).map factorBlockValue).prod) = 152360405087833 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_557
      · exact prime_oneHundredFortyFourEL_1266377461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 152360405087833) ^ 76180202543916 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 152360405087833) ^ 50786801695944 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 152360405087833) ^ 273537531576 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 152360405087833) ^ 120312 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_240844691621461 : Nat.Prime 240844691621461 := by
  apply lucas_primality 240844691621461 (2 : ZMod 240844691621461)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (4014078193691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (4014078193691, 1)] : List FactorBlock).map factorBlockValue).prod) = 240844691621461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_5
      · exact prime_oneHundredFortyFourEL_4014078193691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 240844691621461) ^ 120422345810730 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 240844691621461) ^ 80281563873820 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 240844691621461) ^ 48168938324292 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 240844691621461) ^ 60 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_258862483991359 : Nat.Prime 258862483991359 := by
  apply lucas_primality 258862483991359 (6 : ZMod 258862483991359)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (10789, 1), (102534983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (10789, 1), (102534983, 1)] : List FactorBlock).map factorBlockValue).prod) = 258862483991359 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_13
      · exact prime_oneHundredFortyFourEL_10789
      · exact prime_oneHundredFortyFourEL_102534983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 258862483991359) ^ 129431241995679 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (6 : ZMod 258862483991359) ^ 86287494663786 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (6 : ZMod 258862483991359) ^ 19912498768566 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (6 : ZMod 258862483991359) ^ 23993186022 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (6 : ZMod 258862483991359) ^ 2524626 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_309280368906961 : Nat.Prime 309280368906961 := by
  apply lucas_primality 309280368906961 (19 : ZMod 309280368906961)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (11, 1), (17, 1), (1249, 1), (5517433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (11, 1), (17, 1), (1249, 1), (5517433, 1)] : List FactorBlock).map factorBlockValue).prod) = 309280368906961 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_5
      · exact prime_oneHundredFortyFourEL_11
      · exact prime_oneHundredFortyFourEL_17
      · exact prime_oneHundredFortyFourEL_1249
      · exact prime_oneHundredFortyFourEL_5517433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 309280368906961) ^ 154640184453480 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (19 : ZMod 309280368906961) ^ 103093456302320 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (19 : ZMod 309280368906961) ^ 61856073781392 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (19 : ZMod 309280368906961) ^ 28116397173360 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (19 : ZMod 309280368906961) ^ 18192962876880 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (19 : ZMod 309280368906961) ^ 247622393040 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (19 : ZMod 309280368906961) ^ 56055120 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_334989034308223 : Nat.Prime 334989034308223 := by
  apply lucas_primality 334989034308223 (3 : ZMod 334989034308223)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (37, 1), (215565659143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (37, 1), (215565659143, 1)] : List FactorBlock).map factorBlockValue).prod) = 334989034308223 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_7
      · exact prime_oneHundredFortyFourEL_37
      · exact prime_oneHundredFortyFourEL_215565659143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 334989034308223) ^ 167494517154111 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 334989034308223) ^ 111663011436074 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 334989034308223) ^ 47855576329746 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 334989034308223) ^ 9053757684006 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 334989034308223) ^ 1554 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_366020420757353 : Nat.Prime 366020420757353 := by
  apply lucas_primality 366020420757353 (3 : ZMod 366020420757353)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (45752552594669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (45752552594669, 1)] : List FactorBlock).map factorBlockValue).prod) = 366020420757353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_45752552594669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 366020420757353) ^ 183010210378676 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 366020420757353) ^ 8 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_378245271535333 : Nat.Prime 378245271535333 := by
  apply lucas_primality 378245271535333 (2 : ZMod 378245271535333)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (733, 1), (9467, 1), (4542301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (733, 1), (9467, 1), (4542301, 1)] : List FactorBlock).map factorBlockValue).prod) = 378245271535333 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_733
      · exact prime_oneHundredFortyFourEL_9467
      · exact prime_oneHundredFortyFourEL_4542301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 378245271535333) ^ 189122635767666 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 378245271535333) ^ 126081757178444 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 378245271535333) ^ 516023562804 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 378245271535333) ^ 39954079596 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 378245271535333) ^ 83271732 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_613918377372439 : Nat.Prime 613918377372439 := by
  apply lucas_primality 613918377372439 (6 : ZMod 613918377372439)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (111577, 1), (305677483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (111577, 1), (305677483, 1)] : List FactorBlock).map factorBlockValue).prod) = 613918377372439 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_111577
      · exact prime_oneHundredFortyFourEL_305677483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 613918377372439) ^ 306959188686219 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (6 : ZMod 613918377372439) ^ 204639459124146 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (6 : ZMod 613918377372439) ^ 5502194694 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (6 : ZMod 613918377372439) ^ 2008386 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_829722028640579 : Nat.Prime 829722028640579 := by
  apply lucas_primality 829722028640579 (2 : ZMod 829722028640579)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (14305552217941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (14305552217941, 1)] : List FactorBlock).map factorBlockValue).prod) = 829722028640579 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_29
      · exact prime_oneHundredFortyFourEL_14305552217941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 829722028640579) ^ 414861014320289 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 829722028640579) ^ 28611104435882 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 829722028640579) ^ 58 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_1200138209940499 : Nat.Prime 1200138209940499 := by
  apply lucas_primality 1200138209940499 (2 : ZMod 1200138209940499)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (230551, 1), (37721171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (230551, 1), (37721171, 1)] : List FactorBlock).map factorBlockValue).prod) = 1200138209940499 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_23
      · exact prime_oneHundredFortyFourEL_230551
      · exact prime_oneHundredFortyFourEL_37721171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1200138209940499) ^ 600069104970249 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 1200138209940499) ^ 400046069980166 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 1200138209940499) ^ 52179922171326 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 1200138209940499) ^ 5205521598 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 1200138209940499) ^ 31816038 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_1291737826932829 : Nat.Prime 1291737826932829 := by
  apply lucas_primality 1291737826932829 (2 : ZMod 1291737826932829)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (9785892628279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (9785892628279, 1)] : List FactorBlock).map factorBlockValue).prod) = 1291737826932829 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_11
      · exact prime_oneHundredFortyFourEL_9785892628279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1291737826932829) ^ 645868913466414 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 1291737826932829) ^ 430579275644276 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 1291737826932829) ^ 117430711539348 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 1291737826932829) ^ 132 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_1352851298914249 : Nat.Prime 1352851298914249 := by
  apply lucas_primality 1352851298914249 (17 : ZMod 1352851298914249)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (7, 1), (37, 1), (229, 1), (316797919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (7, 1), (37, 1), (229, 1), (316797919, 1)] : List FactorBlock).map factorBlockValue).prod) = 1352851298914249 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_7
      · exact prime_oneHundredFortyFourEL_37
      · exact prime_oneHundredFortyFourEL_229
      · exact prime_oneHundredFortyFourEL_316797919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 1352851298914249) ^ 676425649457124 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (17 : ZMod 1352851298914249) ^ 450950432971416 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (17 : ZMod 1352851298914249) ^ 193264471273464 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (17 : ZMod 1352851298914249) ^ 36563548619304 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (17 : ZMod 1352851298914249) ^ 5907647593512 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (17 : ZMod 1352851298914249) ^ 4270392 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_1452722104942727 : Nat.Prime 1452722104942727 := by
  apply lucas_primality 1452722104942727 (5 : ZMod 1452722104942727)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (197, 1), (3687111941479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (197, 1), (3687111941479, 1)] : List FactorBlock).map factorBlockValue).prod) = 1452722104942727 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_197
      · exact prime_oneHundredFortyFourEL_3687111941479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1452722104942727) ^ 726361052471363 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 1452722104942727) ^ 7374223882958 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 1452722104942727) ^ 394 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_1499250865126921 : Nat.Prime 1499250865126921 := by
  apply lucas_primality 1499250865126921 (19 : ZMod 1499250865126921)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (349, 1), (13829, 1), (2588671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (349, 1), (13829, 1), (2588671, 1)] : List FactorBlock).map factorBlockValue).prod) = 1499250865126921 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_5
      · exact prime_oneHundredFortyFourEL_349
      · exact prime_oneHundredFortyFourEL_13829
      · exact prime_oneHundredFortyFourEL_2588671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 1499250865126921) ^ 749625432563460 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (19 : ZMod 1499250865126921) ^ 499750288375640 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (19 : ZMod 1499250865126921) ^ 299850173025384 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (19 : ZMod 1499250865126921) ^ 4295847751080 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (19 : ZMod 1499250865126921) ^ 108413541480 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (19 : ZMod 1499250865126921) ^ 579158520 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_2164499678281279 : Nat.Prime 2164499678281279 := by
  apply lucas_primality 2164499678281279 (11 : ZMod 2164499678281279)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (17, 1), (31, 1), (52656538663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (17, 1), (31, 1), (52656538663, 1)] : List FactorBlock).map factorBlockValue).prod) = 2164499678281279 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_13
      · exact prime_oneHundredFortyFourEL_17
      · exact prime_oneHundredFortyFourEL_31
      · exact prime_oneHundredFortyFourEL_52656538663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 2164499678281279) ^ 1082249839140639 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (11 : ZMod 2164499678281279) ^ 721499892760426 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (11 : ZMod 2164499678281279) ^ 166499975252406 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (11 : ZMod 2164499678281279) ^ 127323510487134 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (11 : ZMod 2164499678281279) ^ 69822570267138 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (11 : ZMod 2164499678281279) ^ 41106 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_2646704786930381 : Nat.Prime 2646704786930381 := by
  apply lucas_primality 2646704786930381 (10 : ZMod 2646704786930381)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (11, 1), (43, 1), (251, 1), (1889, 1), (590077, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (11, 1), (43, 1), (251, 1), (1889, 1), (590077, 1)] : List FactorBlock).map factorBlockValue).prod) = 2646704786930381 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_5
      · exact prime_oneHundredFortyFourEL_11
      · exact prime_oneHundredFortyFourEL_43
      · exact prime_oneHundredFortyFourEL_251
      · exact prime_oneHundredFortyFourEL_1889
      · exact prime_oneHundredFortyFourEL_590077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 2646704786930381) ^ 1323352393465190 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (10 : ZMod 2646704786930381) ^ 529340957386076 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (10 : ZMod 2646704786930381) ^ 240609526084580 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (10 : ZMod 2646704786930381) ^ 61551274114660 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (10 : ZMod 2646704786930381) ^ 10544640585380 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (10 : ZMod 2646704786930381) ^ 1401114233420 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (10 : ZMod 2646704786930381) ^ 4485354940 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_2719969280209463 : Nat.Prime 2719969280209463 := by
  apply lucas_primality 2719969280209463 (5 : ZMod 2719969280209463)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (4861, 1), (279774663671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (4861, 1), (279774663671, 1)] : List FactorBlock).map factorBlockValue).prod) = 2719969280209463 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_4861
      · exact prime_oneHundredFortyFourEL_279774663671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 2719969280209463) ^ 1359984640104731 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 2719969280209463) ^ 559549327342 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 2719969280209463) ^ 9722 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_4531774490983801 : Nat.Prime 4531774490983801 := by
  apply lucas_primality 4531774490983801 (7 : ZMod 4531774490983801)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 2), (2517652494991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 2), (2517652494991, 1)] : List FactorBlock).map factorBlockValue).prod) = 4531774490983801 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_5
      · exact prime_oneHundredFortyFourEL_2517652494991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 4531774490983801) ^ 2265887245491900 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (7 : ZMod 4531774490983801) ^ 1510591496994600 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (7 : ZMod 4531774490983801) ^ 906354898196760 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (7 : ZMod 4531774490983801) ^ 1800 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_4965793642285667 : Nat.Prime 4965793642285667 := by
  apply lucas_primality 4965793642285667 (2 : ZMod 4965793642285667)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (227, 1), (10937871458779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (227, 1), (10937871458779, 1)] : List FactorBlock).map factorBlockValue).prod) = 4965793642285667 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_227
      · exact prime_oneHundredFortyFourEL_10937871458779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4965793642285667) ^ 2482896821142833 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 4965793642285667) ^ 21875742917558 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 4965793642285667) ^ 454 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_6311847911033663 : Nat.Prime 6311847911033663 := by
  apply lucas_primality 6311847911033663 (5 : ZMod 6311847911033663)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (197, 1), (1163, 1), (1487, 1), (319427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (197, 1), (1163, 1), (1487, 1), (319427, 1)] : List FactorBlock).map factorBlockValue).prod) = 6311847911033663 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_29
      · exact prime_oneHundredFortyFourEL_197
      · exact prime_oneHundredFortyFourEL_1163
      · exact prime_oneHundredFortyFourEL_1487
      · exact prime_oneHundredFortyFourEL_319427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 6311847911033663) ^ 3155923955516831 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 6311847911033663) ^ 217649927966678 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 6311847911033663) ^ 32039837111846 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 6311847911033663) ^ 5427212305274 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 6311847911033663) ^ 4244685885026 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 6311847911033663) ^ 19759907306 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_8808631998632509 : Nat.Prime 8808631998632509 := by
  apply lucas_primality 8808631998632509 (2 : ZMod 8808631998632509)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 4), (47, 1), (139, 1), (149, 1), (314077, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 4), (47, 1), (139, 1), (149, 1), (314077, 1)] : List FactorBlock).map factorBlockValue).prod) = 8808631998632509 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_7
      · exact prime_oneHundredFortyFourEL_47
      · exact prime_oneHundredFortyFourEL_139
      · exact prime_oneHundredFortyFourEL_149
      · exact prime_oneHundredFortyFourEL_314077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8808631998632509) ^ 4404315999316254 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 8808631998632509) ^ 2936210666210836 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 8808631998632509) ^ 1258375999804644 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 8808631998632509) ^ 187417702098564 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 8808631998632509) ^ 63371453227572 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 8808631998632509) ^ 59118335561292 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 8808631998632509) ^ 28046090604 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_9932770333446151 : Nat.Prime 9932770333446151 := by
  apply lucas_primality 9932770333446151 (3 : ZMod 9932770333446151)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (19, 1), (23, 1), (272737, 1), (555589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (19, 1), (23, 1), (272737, 1), (555589, 1)] : List FactorBlock).map factorBlockValue).prod) = 9932770333446151 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_5
      · exact prime_oneHundredFortyFourEL_19
      · exact prime_oneHundredFortyFourEL_23
      · exact prime_oneHundredFortyFourEL_272737
      · exact prime_oneHundredFortyFourEL_555589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 9932770333446151) ^ 4966385166723075 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 9932770333446151) ^ 3310923444482050 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 9932770333446151) ^ 1986554066689230 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 9932770333446151) ^ 522777385970850 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 9932770333446151) ^ 431859579715050 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 9932770333446151) ^ 36418858950 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 9932770333446151) ^ 17877910350 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_13597228324225297 : Nat.Prime 13597228324225297 := by
  apply lucas_primality 13597228324225297 (5 : ZMod 13597228324225297)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (467371, 1), (202034779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (467371, 1), (202034779, 1)] : List FactorBlock).map factorBlockValue).prod) = 13597228324225297 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_467371
      · exact prime_oneHundredFortyFourEL_202034779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 13597228324225297) ^ 6798614162112648 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 13597228324225297) ^ 4532409441408432 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 13597228324225297) ^ 29093008176 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 13597228324225297) ^ 67301424 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_29580241950103007 : Nat.Prime 29580241950103007 := by
  apply lucas_primality 29580241950103007 (5 : ZMod 29580241950103007)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (479, 1), (91541, 1), (337303277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (479, 1), (91541, 1), (337303277, 1)] : List FactorBlock).map factorBlockValue).prod) = 29580241950103007 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_479
      · exact prime_oneHundredFortyFourEL_91541
      · exact prime_oneHundredFortyFourEL_337303277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 29580241950103007) ^ 14790120975051503 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 29580241950103007) ^ 61754158559714 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 29580241950103007) ^ 323136539366 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 29580241950103007) ^ 87696278 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_33978172901563879 : Nat.Prime 33978172901563879 := by
  apply lucas_primality 33978172901563879 (6 : ZMod 33978172901563879)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (23, 2), (182627, 1), (4509047, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (23, 2), (182627, 1), (4509047, 1)] : List FactorBlock).map factorBlockValue).prod) = 33978172901563879 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_13
      · exact prime_oneHundredFortyFourEL_23
      · exact prime_oneHundredFortyFourEL_182627
      · exact prime_oneHundredFortyFourEL_4509047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 33978172901563879) ^ 16989086450781939 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (6 : ZMod 33978172901563879) ^ 11326057633854626 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (6 : ZMod 33978172901563879) ^ 2613705607812606 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (6 : ZMod 33978172901563879) ^ 1477311865285386 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (6 : ZMod 33978172901563879) ^ 186052297314 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (6 : ZMod 33978172901563879) ^ 7535555274 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_37051420944511243 : Nat.Prime 37051420944511243 := by
  apply lucas_primality 37051420944511243 (3 : ZMod 37051420944511243)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (131, 1), (170603, 1), (92103133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (131, 1), (170603, 1), (92103133, 1)] : List FactorBlock).map factorBlockValue).prod) = 37051420944511243 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_131
      · exact prime_oneHundredFortyFourEL_170603
      · exact prime_oneHundredFortyFourEL_92103133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 37051420944511243) ^ 18525710472255621 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 37051420944511243) ^ 12350473648170414 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 37051420944511243) ^ 282835274385582 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 37051420944511243) ^ 217179187614 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 37051420944511243) ^ 402281874 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_53760126091519151 : Nat.Prime 53760126091519151 := by
  apply lucas_primality 53760126091519151 (13 : ZMod 53760126091519151)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (260417, 1), (4128772399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (260417, 1), (4128772399, 1)] : List FactorBlock).map factorBlockValue).prod) = 53760126091519151 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_5
      · exact prime_oneHundredFortyFourEL_260417
      · exact prime_oneHundredFortyFourEL_4128772399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 53760126091519151) ^ 26880063045759575 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (13 : ZMod 53760126091519151) ^ 10752025218303830 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (13 : ZMod 53760126091519151) ^ 206438619950 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (13 : ZMod 53760126091519151) ^ 13020850 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_70075919093336591 : Nat.Prime 70075919093336591 := by
  apply lucas_primality 70075919093336591 (14 : ZMod 70075919093336591)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (31, 1), (24841, 1), (1299989947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (31, 1), (24841, 1), (1299989947, 1)] : List FactorBlock).map factorBlockValue).prod) = 70075919093336591 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_5
      · exact prime_oneHundredFortyFourEL_7
      · exact prime_oneHundredFortyFourEL_31
      · exact prime_oneHundredFortyFourEL_24841
      · exact prime_oneHundredFortyFourEL_1299989947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 70075919093336591) ^ 35037959546668295 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (14 : ZMod 70075919093336591) ^ 14015183818667318 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (14 : ZMod 70075919093336591) ^ 10010845584762370 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (14 : ZMod 70075919093336591) ^ 2260513519139890 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (14 : ZMod 70075919093336591) ^ 2820978184990 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (14 : ZMod 70075919093336591) ^ 53904970 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_81005988925976273 : Nat.Prime 81005988925976273 := by
  apply lucas_primality 81005988925976273 (3 : ZMod 81005988925976273)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (50593, 1), (100070648269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (50593, 1), (100070648269, 1)] : List FactorBlock).map factorBlockValue).prod) = 81005988925976273 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_50593
      · exact prime_oneHundredFortyFourEL_100070648269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 81005988925976273) ^ 40502994462988136 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 81005988925976273) ^ 1601130372304 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 81005988925976273) ^ 809488 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_89956470563501489 : Nat.Prime 89956470563501489 := by
  apply lucas_primality 89956470563501489 (3 : ZMod 89956470563501489)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (19, 1), (47, 1), (2287, 1), (2752927673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (19, 1), (47, 1), (2287, 1), (2752927673, 1)] : List FactorBlock).map factorBlockValue).prod) = 89956470563501489 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_19
      · exact prime_oneHundredFortyFourEL_47
      · exact prime_oneHundredFortyFourEL_2287
      · exact prime_oneHundredFortyFourEL_2752927673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 89956470563501489) ^ 44978235281750744 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 89956470563501489) ^ 4734551082289552 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 89956470563501489) ^ 1913967458797904 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 89956470563501489) ^ 39333830591824 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 89956470563501489) ^ 32676656 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_104139632087311397 : Nat.Prime 104139632087311397 := by
  apply lucas_primality 104139632087311397 (2 : ZMod 104139632087311397)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (4177, 1), (6232920282937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (4177, 1), (6232920282937, 1)] : List FactorBlock).map factorBlockValue).prod) = 104139632087311397 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_4177
      · exact prime_oneHundredFortyFourEL_6232920282937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 104139632087311397) ^ 52069816043655698 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 104139632087311397) ^ 24931681131748 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 104139632087311397) ^ 16708 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_104997213222150383 : Nat.Prime 104997213222150383 := by
  apply lucas_primality 104997213222150383 (5 : ZMod 104997213222150383)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (1545121, 1), (4853859953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (1545121, 1), (4853859953, 1)] : List FactorBlock).map factorBlockValue).prod) = 104997213222150383 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_7
      · exact prime_oneHundredFortyFourEL_1545121
      · exact prime_oneHundredFortyFourEL_4853859953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 104997213222150383) ^ 52498606611075191 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 104997213222150383) ^ 14999601888878626 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 104997213222150383) ^ 67954039342 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 104997213222150383) ^ 21631694 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_116098628676928747 : Nat.Prime 116098628676928747 := by
  apply lucas_primality 116098628676928747 (3 : ZMod 116098628676928747)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (127, 1), (152360405087833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (127, 1), (152360405087833, 1)] : List FactorBlock).map factorBlockValue).prod) = 116098628676928747 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_127
      · exact prime_oneHundredFortyFourEL_152360405087833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 116098628676928747) ^ 58049314338464373 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 116098628676928747) ^ 38699542892309582 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 116098628676928747) ^ 914162430526998 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 116098628676928747) ^ 762 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_116754944939301001 : Nat.Prime 116754944939301001 := by
  apply lucas_primality 116754944939301001 (38 : ZMod 116754944939301001)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 3), (38918314979767, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 3), (38918314979767, 1)] : List FactorBlock).map factorBlockValue).prod) = 116754944939301001 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_5
      · exact prime_oneHundredFortyFourEL_38918314979767
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (38 : ZMod 116754944939301001) ^ 58377472469650500 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (38 : ZMod 116754944939301001) ^ 38918314979767000 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (38 : ZMod 116754944939301001) ^ 23350988987860200 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (38 : ZMod 116754944939301001) ^ 3000 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_147682248285261413 : Nat.Prime 147682248285261413 := by
  apply lucas_primality 147682248285261413 (2 : ZMod 147682248285261413)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 1), (37, 1), (23417, 1), (1469390833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 1), (37, 1), (23417, 1), (1469390833, 1)] : List FactorBlock).map factorBlockValue).prod) = 147682248285261413 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_29
      · exact prime_oneHundredFortyFourEL_37
      · exact prime_oneHundredFortyFourEL_23417
      · exact prime_oneHundredFortyFourEL_1469390833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 147682248285261413) ^ 73841124142630706 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 147682248285261413) ^ 5092491320181428 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 147682248285261413) ^ 3991412115817876 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 147682248285261413) ^ 6306625455236 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 147682248285261413) ^ 100505764 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_183019515847327619 : Nat.Prime 183019515847327619 := by
  apply lucas_primality 183019515847327619 (2 : ZMod 183019515847327619)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19751, 1), (4633170873559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19751, 1), (4633170873559, 1)] : List FactorBlock).map factorBlockValue).prod) = 183019515847327619 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_19751
      · exact prime_oneHundredFortyFourEL_4633170873559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 183019515847327619) ^ 91509757923663809 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 183019515847327619) ^ 9266341747118 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 183019515847327619) ^ 39502 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_557533530243080843 : Nat.Prime 557533530243080843 := by
  apply lucas_primality 557533530243080843 (2 : ZMod 557533530243080843)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (67, 1), (378245271535333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (67, 1), (378245271535333, 1)] : List FactorBlock).map factorBlockValue).prod) = 557533530243080843 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_11
      · exact prime_oneHundredFortyFourEL_67
      · exact prime_oneHundredFortyFourEL_378245271535333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 557533530243080843) ^ 278766765121540421 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 557533530243080843) ^ 50684866385734622 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 557533530243080843) ^ 8321395973777326 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 557533530243080843) ^ 1474 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_588750905660297287 : Nat.Prime 588750905660297287 := by
  apply lucas_primality 588750905660297287 (3 : ZMod 588750905660297287)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (139, 1), (197, 1), (3677, 1), (51292289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (139, 1), (197, 1), (3677, 1), (51292289, 1)] : List FactorBlock).map factorBlockValue).prod) = 588750905660297287 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_19
      · exact prime_oneHundredFortyFourEL_139
      · exact prime_oneHundredFortyFourEL_197
      · exact prime_oneHundredFortyFourEL_3677
      · exact prime_oneHundredFortyFourEL_51292289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 588750905660297287) ^ 294375452830148643 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 588750905660297287) ^ 196250301886765762 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 588750905660297287) ^ 30986889771594594 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 588750905660297287) ^ 4235618026333074 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 588750905660297287) ^ 2988583277463438 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 588750905660297287) ^ 160117189464318 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 588750905660297287) ^ 11478351174 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_605937399459231649 : Nat.Prime 605937399459231649 := by
  apply lucas_primality 605937399459231649 (7 : ZMod 605937399459231649)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (6311847911033663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (6311847911033663, 1)] : List FactorBlock).map factorBlockValue).prod) = 605937399459231649 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_6311847911033663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 605937399459231649) ^ 302968699729615824 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (7 : ZMod 605937399459231649) ^ 201979133153077216 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (7 : ZMod 605937399459231649) ^ 96 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_1110223939932987497 : Nat.Prime 1110223939932987497 := by
  apply lucas_primality 1110223939932987497 (3 : ZMod 1110223939932987497)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (739, 1), (4830151, 1), (38879033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (739, 1), (4830151, 1), (38879033, 1)] : List FactorBlock).map factorBlockValue).prod) = 1110223939932987497 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_739
      · exact prime_oneHundredFortyFourEL_4830151
      · exact prime_oneHundredFortyFourEL_38879033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1110223939932987497) ^ 555111969966493748 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 1110223939932987497) ^ 1502332800991864 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 1110223939932987497) ^ 229852843096 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 1110223939932987497) ^ 28555852712 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_1115067060486161687 : Nat.Prime 1115067060486161687 := by
  apply lucas_primality 1115067060486161687 (5 : ZMod 1115067060486161687)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (557533530243080843, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (557533530243080843, 1)] : List FactorBlock).map factorBlockValue).prod) = 1115067060486161687 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_557533530243080843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 1115067060486161687) ^ 557533530243080843 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 1115067060486161687) ^ 2 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_1131631914986108023 : Nat.Prime 1131631914986108023 := by
  apply lucas_primality 1131631914986108023 (3 : ZMod 1131631914986108023)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7170469, 1), (26303065973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7170469, 1), (26303065973, 1)] : List FactorBlock).map factorBlockValue).prod) = 1131631914986108023 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_7170469
      · exact prime_oneHundredFortyFourEL_26303065973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1131631914986108023) ^ 565815957493054011 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 1131631914986108023) ^ 377210638328702674 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 1131631914986108023) ^ 157818395838 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 1131631914986108023) ^ 43022814 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_1492065108799822793 : Nat.Prime 1492065108799822793 := by
  apply lucas_primality 1492065108799822793 (3 : ZMod 1492065108799822793)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (23, 1), (47981, 1), (88873, 1), (1901651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (23, 1), (47981, 1), (88873, 1), (1901651, 1)] : List FactorBlock).map factorBlockValue).prod) = 1492065108799822793 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_23
      · exact prime_oneHundredFortyFourEL_47981
      · exact prime_oneHundredFortyFourEL_88873
      · exact prime_oneHundredFortyFourEL_1901651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1492065108799822793) ^ 746032554399911396 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 1492065108799822793) ^ 64872396034774904 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 1492065108799822793) ^ 31096998995432 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 1492065108799822793) ^ 16788733460104 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 1492065108799822793) ^ 784615635992 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_2220502305087140441 : Nat.Prime 2220502305087140441 := by
  apply lucas_primality 2220502305087140441 (3 : ZMod 2220502305087140441)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (101, 1), (191, 1), (48017, 1), (59929613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (101, 1), (191, 1), (48017, 1), (59929613, 1)] : List FactorBlock).map factorBlockValue).prod) = 2220502305087140441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_5
      · exact prime_oneHundredFortyFourEL_101
      · exact prime_oneHundredFortyFourEL_191
      · exact prime_oneHundredFortyFourEL_48017
      · exact prime_oneHundredFortyFourEL_59929613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2220502305087140441) ^ 1110251152543570220 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 444100461017428088 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 21985171337496440 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 11625666518780840 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 46244086575320 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 37051837880 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_2325763089382150177 : Nat.Prime 2325763089382150177 := by
  apply lucas_primality 2325763089382150177 (10 : ZMod 2325763089382150177)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (11, 1), (29, 1), (37, 1), (41, 1), (43, 1), (1164258779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (11, 1), (29, 1), (37, 1), (41, 1), (43, 1), (1164258779, 1)] : List FactorBlock).map factorBlockValue).prod) = 2325763089382150177 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_11
      · exact prime_oneHundredFortyFourEL_29
      · exact prime_oneHundredFortyFourEL_37
      · exact prime_oneHundredFortyFourEL_41
      · exact prime_oneHundredFortyFourEL_43
      · exact prime_oneHundredFortyFourEL_1164258779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 2325763089382150177) ^ 1162881544691075088 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (10 : ZMod 2325763089382150177) ^ 775254363127383392 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (10 : ZMod 2325763089382150177) ^ 211433008125650016 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (10 : ZMod 2325763089382150177) ^ 80198727220074144 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (10 : ZMod 2325763089382150177) ^ 62858461875193248 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (10 : ZMod 2325763089382150177) ^ 56725929009320736 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (10 : ZMod 2325763089382150177) ^ 54087513706561632 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (10 : ZMod 2325763089382150177) ^ 1997634144 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_3503795954666829551 : Nat.Prime 3503795954666829551 := by
  apply lucas_primality 3503795954666829551 (13 : ZMod 3503795954666829551)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (70075919093336591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (70075919093336591, 1)] : List FactorBlock).map factorBlockValue).prod) = 3503795954666829551 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_5
      · exact prime_oneHundredFortyFourEL_70075919093336591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 3503795954666829551) ^ 1751897977333414775 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (13 : ZMod 3503795954666829551) ^ 700759190933365910 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (13 : ZMod 3503795954666829551) ^ 50 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_4402247467841949569 : Nat.Prime 4402247467841949569 := by
  apply lucas_primality 4402247467841949569 (3 : ZMod 4402247467841949569)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (29, 1), (37, 1), (32052710477647, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (29, 1), (37, 1), (32052710477647, 1)] : List FactorBlock).map factorBlockValue).prod) = 4402247467841949569 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_29
      · exact prime_oneHundredFortyFourEL_37
      · exact prime_oneHundredFortyFourEL_32052710477647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4402247467841949569) ^ 2201123733920974784 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 4402247467841949569) ^ 151801636822136192 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 4402247467841949569) ^ 118979661293025664 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 4402247467841949569) ^ 137344 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_13272973828697194921 : Nat.Prime 13272973828697194921 := by
  apply lucas_primality 13272973828697194921 (19 : ZMod 13272973828697194921)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (7, 1), (11, 1), (113, 1), (4237371767197, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (7, 1), (11, 1), (113, 1), (4237371767197, 1)] : List FactorBlock).map factorBlockValue).prod) = 13272973828697194921 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_5
      · exact prime_oneHundredFortyFourEL_7
      · exact prime_oneHundredFortyFourEL_11
      · exact prime_oneHundredFortyFourEL_113
      · exact prime_oneHundredFortyFourEL_4237371767197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 13272973828697194921) ^ 6636486914348597460 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (19 : ZMod 13272973828697194921) ^ 4424324609565731640 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (19 : ZMod 13272973828697194921) ^ 2654594765739438984 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (19 : ZMod 13272973828697194921) ^ 1896139118385313560 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (19 : ZMod 13272973828697194921) ^ 1206633984427017720 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (19 : ZMod 13272973828697194921) ^ 117459945386700840 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (19 : ZMod 13272973828697194921) ^ 3132360 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_13311937837557174217 : Nat.Prime 13311937837557174217 := by
  apply lucas_primality 13311937837557174217 (5 : ZMod 13311937837557174217)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (4253, 1), (130417135331503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (4253, 1), (130417135331503, 1)] : List FactorBlock).map factorBlockValue).prod) = 13311937837557174217 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_4253
      · exact prime_oneHundredFortyFourEL_130417135331503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 13311937837557174217) ^ 6655968918778587108 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 13311937837557174217) ^ 4437312612519058072 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 13311937837557174217) ^ 3130011247956072 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 13311937837557174217) ^ 102072 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_14606113093399511149 : Nat.Prime 14606113093399511149 := by
  apply lucas_primality 14606113093399511149 (2 : ZMod 14606113093399511149)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1453, 1), (3067, 1), (273132904279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1453, 1), (3067, 1), (273132904279, 1)] : List FactorBlock).map factorBlockValue).prod) = 14606113093399511149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_1453
      · exact prime_oneHundredFortyFourEL_3067
      · exact prime_oneHundredFortyFourEL_273132904279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 14606113093399511149) ^ 7303056546699755574 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 14606113093399511149) ^ 4868704364466503716 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 14606113093399511149) ^ 10052383409084316 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 14606113093399511149) ^ 4762345319008644 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 14606113093399511149) ^ 53476212 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_21705598351229560111 : Nat.Prime 21705598351229560111 := by
  apply lucas_primality 21705598351229560111 (6 : ZMod 21705598351229560111)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 1), (17393, 1), (31573, 1), (62739473, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 1), (17393, 1), (31573, 1), (62739473, 1)] : List FactorBlock).map factorBlockValue).prod) = 21705598351229560111 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_5
      · exact prime_oneHundredFortyFourEL_7
      · exact prime_oneHundredFortyFourEL_17393
      · exact prime_oneHundredFortyFourEL_31573
      · exact prime_oneHundredFortyFourEL_62739473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 21705598351229560111) ^ 10852799175614780055 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (6 : ZMod 21705598351229560111) ^ 7235199450409853370 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (6 : ZMod 21705598351229560111) ^ 4341119670245912022 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (6 : ZMod 21705598351229560111) ^ 3100799764461365730 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (6 : ZMod 21705598351229560111) ^ 1247950230048270 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (6 : ZMod 21705598351229560111) ^ 687473421950070 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (6 : ZMod 21705598351229560111) ^ 345963989070 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_26661987197588219303 : Nat.Prime 26661987197588219303 := by
  apply lucas_primality 26661987197588219303 (5 : ZMod 26661987197588219303)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (179, 1), (41687, 1), (255217709441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (179, 1), (41687, 1), (255217709441, 1)] : List FactorBlock).map factorBlockValue).prod) = 26661987197588219303 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_7
      · exact prime_oneHundredFortyFourEL_179
      · exact prime_oneHundredFortyFourEL_41687
      · exact prime_oneHundredFortyFourEL_255217709441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 26661987197588219303) ^ 13330993598794109651 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 26661987197588219303) ^ 3808855313941174186 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 26661987197588219303) ^ 148949649148537538 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 26661987197588219303) ^ 639575579859146 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 26661987197588219303) ^ 104467622 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_45407637658287822941 : Nat.Prime 45407637658287822941 := by
  apply lucas_primality 45407637658287822941 (12 : ZMod 45407637658287822941)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (11, 1), (199, 1), (94823, 1), (10938038801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (11, 1), (199, 1), (94823, 1), (10938038801, 1)] : List FactorBlock).map factorBlockValue).prod) = 45407637658287822941 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_5
      · exact prime_oneHundredFortyFourEL_11
      · exact prime_oneHundredFortyFourEL_199
      · exact prime_oneHundredFortyFourEL_94823
      · exact prime_oneHundredFortyFourEL_10938038801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (12 : ZMod 45407637658287822941) ^ 22703818829143911470 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (12 : ZMod 45407637658287822941) ^ 9081527531657564588 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (12 : ZMod 45407637658287822941) ^ 4127967059844347540 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (12 : ZMod 45407637658287822941) ^ 228179083709989060 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (12 : ZMod 45407637658287822941) ^ 478867338707780 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (12 : ZMod 45407637658287822941) ^ 4151350940 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_46949410428577858931 : Nat.Prime 46949410428577858931 := by
  apply lucas_primality 46949410428577858931 (2 : ZMod 46949410428577858931)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (751, 1), (19379, 1), (18976229401, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (751, 1), (19379, 1), (18976229401, 1)] : List FactorBlock).map factorBlockValue).prod) = 46949410428577858931 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_5
      · exact prime_oneHundredFortyFourEL_17
      · exact prime_oneHundredFortyFourEL_751
      · exact prime_oneHundredFortyFourEL_19379
      · exact prime_oneHundredFortyFourEL_18976229401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 46949410428577858931) ^ 23474705214288929465 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 46949410428577858931) ^ 9389882085715571786 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 46949410428577858931) ^ 2761730025210462290 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 46949410428577858931) ^ 62515859425536430 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 46949410428577858931) ^ 2422695207625670 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 46949410428577858931) ^ 2474116930 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_72424442559110913473 : Nat.Prime 72424442559110913473 := by
  apply lucas_primality 72424442559110913473 (3 : ZMod 72424442559110913473)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (1131631914986108023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (1131631914986108023, 1)] : List FactorBlock).map factorBlockValue).prod) = 72424442559110913473 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_1131631914986108023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 72424442559110913473) ^ 36212221279555456736 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 72424442559110913473) ^ 64 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_137639855401863636917 : Nat.Prime 137639855401863636917 := by
  apply lucas_primality 137639855401863636917 (2 : ZMod 137639855401863636917)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (233, 1), (147682248285261413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (233, 1), (147682248285261413, 1)] : List FactorBlock).map factorBlockValue).prod) = 137639855401863636917 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_233
      · exact prime_oneHundredFortyFourEL_147682248285261413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 137639855401863636917) ^ 68819927700931818458 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 137639855401863636917) ^ 590728993141045652 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 137639855401863636917) ^ 932 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_183751593910716929477 : Nat.Prime 183751593910716929477 := by
  apply lucas_primality 183751593910716929477 (2 : ZMod 183751593910716929477)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (251, 1), (183019515847327619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (251, 1), (183019515847327619, 1)] : List FactorBlock).map factorBlockValue).prod) = 183751593910716929477 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_251
      · exact prime_oneHundredFortyFourEL_183019515847327619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 183751593910716929477) ^ 91875796955358464738 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 183751593910716929477) ^ 732078063389310476 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 183751593910716929477) ^ 1004 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_256223811061086791179 : Nat.Prime 256223811061086791179 := by
  apply lucas_primality 256223811061086791179 (2 : ZMod 256223811061086791179)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (6863, 1), (366020420757353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (6863, 1), (366020420757353, 1)] : List FactorBlock).map factorBlockValue).prod) = 256223811061086791179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_17
      · exact prime_oneHundredFortyFourEL_6863
      · exact prime_oneHundredFortyFourEL_366020420757353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 256223811061086791179) ^ 128111905530543395589 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 85407937020362263726 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 15071988885946281834 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 37334082917250006 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 700026 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_318599651038406015063 : Nat.Prime 318599651038406015063 := by
  apply lucas_primality 318599651038406015063 (5 : ZMod 318599651038406015063)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (61, 1), (5251819, 1), (497251057109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (61, 1), (5251819, 1), (497251057109, 1)] : List FactorBlock).map factorBlockValue).prod) = 318599651038406015063 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_61
      · exact prime_oneHundredFortyFourEL_5251819
      · exact prime_oneHundredFortyFourEL_497251057109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 318599651038406015063) ^ 159299825519203007531 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 318599651038406015063) ^ 5222945098990262542 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 318599651038406015063) ^ 60664628967298 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 318599651038406015063) ^ 640721918 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_336283195596828725831 : Nat.Prime 336283195596828725831 := by
  apply lucas_primality 336283195596828725831 (11 : ZMod 336283195596828725831)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (17, 1), (14600507, 1), (10421853289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (17, 1), (14600507, 1), (10421853289, 1)] : List FactorBlock).map factorBlockValue).prod) = 336283195596828725831 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_5
      · exact prime_oneHundredFortyFourEL_13
      · exact prime_oneHundredFortyFourEL_17
      · exact prime_oneHundredFortyFourEL_14600507
      · exact prime_oneHundredFortyFourEL_10421853289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 336283195596828725831) ^ 168141597798414362915 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (11 : ZMod 336283195596828725831) ^ 67256639119365745166 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (11 : ZMod 336283195596828725831) ^ 25867938122832978910 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (11 : ZMod 336283195596828725831) ^ 19781364446872277990 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (11 : ZMod 336283195596828725831) ^ 23032295768690 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (11 : ZMod 336283195596828725831) ^ 32267120470 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_454820280659747008033 : Nat.Prime 454820280659747008033 := by
  apply lucas_primality 454820280659747008033 (10 : ZMod 454820280659747008033)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (13, 1), (65609, 1), (5554715472751, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (13, 1), (65609, 1), (5554715472751, 1)] : List FactorBlock).map factorBlockValue).prod) = 454820280659747008033 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_13
      · exact prime_oneHundredFortyFourEL_65609
      · exact prime_oneHundredFortyFourEL_5554715472751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 454820280659747008033) ^ 227410140329873504016 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (10 : ZMod 454820280659747008033) ^ 151606760219915669344 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (10 : ZMod 454820280659747008033) ^ 34986175435365154464 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (10 : ZMod 454820280659747008033) ^ 6932284909993248 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (10 : ZMod 454820280659747008033) ^ 81880032 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_619554621871215616219 : Nat.Prime 619554621871215616219 := by
  apply lucas_primality 619554621871215616219 (2 : ZMod 619554621871215616219)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (541, 1), (4051, 1), (1639493, 1), (28738181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (541, 1), (4051, 1), (1639493, 1), (28738181, 1)] : List FactorBlock).map factorBlockValue).prod) = 619554621871215616219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_541
      · exact prime_oneHundredFortyFourEL_4051
      · exact prime_oneHundredFortyFourEL_1639493
      · exact prime_oneHundredFortyFourEL_28738181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 619554621871215616219) ^ 309777310935607808109 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 619554621871215616219) ^ 206518207290405205406 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 619554621871215616219) ^ 1145202628227755298 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 619554621871215616219) ^ 152938687205928318 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 619554621871215616219) ^ 377894033015826 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 619554621871215616219) ^ 21558588620178 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_696245741410278887299 : Nat.Prime 696245741410278887299 := by
  apply lucas_primality 696245741410278887299 (3 : ZMod 696245741410278887299)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (637514413, 1), (60673638397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (637514413, 1), (60673638397, 1)] : List FactorBlock).map factorBlockValue).prod) = 696245741410278887299 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_637514413
      · exact prime_oneHundredFortyFourEL_60673638397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 696245741410278887299) ^ 348122870705139443649 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 696245741410278887299) ^ 232081913803426295766 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 696245741410278887299) ^ 1092125491146 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 696245741410278887299) ^ 11475259434 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_925341976526380756771 : Nat.Prime 925341976526380756771 := by
  apply lucas_primality 925341976526380756771 (26 : ZMod 925341976526380756771)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (139, 1), (199, 1), (1063, 1), (64817, 1), (2312027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (139, 1), (199, 1), (1063, 1), (64817, 1), (2312027, 1)] : List FactorBlock).map factorBlockValue).prod) = 925341976526380756771 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_5
      · exact prime_oneHundredFortyFourEL_7
      · exact prime_oneHundredFortyFourEL_139
      · exact prime_oneHundredFortyFourEL_199
      · exact prime_oneHundredFortyFourEL_1063
      · exact prime_oneHundredFortyFourEL_64817
      · exact prime_oneHundredFortyFourEL_2312027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (26 : ZMod 925341976526380756771) ^ 462670988263190378385 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (26 : ZMod 925341976526380756771) ^ 308447325508793585590 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (26 : ZMod 925341976526380756771) ^ 185068395305276151354 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (26 : ZMod 925341976526380756771) ^ 132191710932340108110 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (26 : ZMod 925341976526380756771) ^ 6657136521772523430 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (26 : ZMod 925341976526380756771) ^ 4649959681037089230 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (26 : ZMod 925341976526380756771) ^ 870500448284459790 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (26 : ZMod 925341976526380756771) ^ 14276223468015810 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (26 : ZMod 925341976526380756771) ^ 400229744949510 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_1121278343585159108429 : Nat.Prime 1121278343585159108429 := by
  apply lucas_primality 1121278343585159108429 (2 : ZMod 1121278343585159108429)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (405373, 1), (2155273, 1), (320845783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (405373, 1), (2155273, 1), (320845783, 1)] : List FactorBlock).map factorBlockValue).prod) = 1121278343585159108429 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_405373
      · exact prime_oneHundredFortyFourEL_2155273
      · exact prime_oneHundredFortyFourEL_320845783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1121278343585159108429) ^ 560639171792579554214 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 1121278343585159108429) ^ 2766041013055036 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 1121278343585159108429) ^ 520248870368236 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 1121278343585159108429) ^ 3494757927316 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_1146250422224934728417 : Nat.Prime 1146250422224934728417 := by
  apply lucas_primality 1146250422224934728417 (3 : ZMod 1146250422224934728417)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (11, 1), (13, 1), (23, 1), (7573, 1), (1154401, 1), (1245779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (11, 1), (13, 1), (23, 1), (7573, 1), (1154401, 1), (1245779, 1)] : List FactorBlock).map factorBlockValue).prod) = 1146250422224934728417 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_11
      · exact prime_oneHundredFortyFourEL_13
      · exact prime_oneHundredFortyFourEL_23
      · exact prime_oneHundredFortyFourEL_7573
      · exact prime_oneHundredFortyFourEL_1154401
      · exact prime_oneHundredFortyFourEL_1245779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1146250422224934728417) ^ 573125211112467364208 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 1146250422224934728417) ^ 104204583838630429856 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 1146250422224934728417) ^ 88173109401918056032 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 1146250422224934728417) ^ 49836974879344988192 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 1146250422224934728417) ^ 151360150828592992 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 1146250422224934728417) ^ 992939561058016 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 1146250422224934728417) ^ 920107356300704 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_1205269042013298899237 : Nat.Prime 1205269042013298899237 := by
  apply lucas_primality 1205269042013298899237 (2 : ZMod 1205269042013298899237)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (1549, 1), (47713, 1), (341461, 1), (519119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (1549, 1), (47713, 1), (341461, 1), (519119, 1)] : List FactorBlock).map factorBlockValue).prod) = 1205269042013298899237 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_23
      · exact prime_oneHundredFortyFourEL_1549
      · exact prime_oneHundredFortyFourEL_47713
      · exact prime_oneHundredFortyFourEL_341461
      · exact prime_oneHundredFortyFourEL_519119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1205269042013298899237) ^ 602634521006649449618 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 1205269042013298899237) ^ 52403001826665169532 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 1205269042013298899237) ^ 778094927058294964 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 1205269042013298899237) ^ 25260810303550372 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 1205269042013298899237) ^ 3529741440496276 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 1205269042013298899237) ^ 2321758675782044 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_1907120781648088563523 : Nat.Prime 1907120781648088563523 := by
  apply lucas_primality 1907120781648088563523 (2 : ZMod 1907120781648088563523)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (45407637658287822941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (45407637658287822941, 1)] : List FactorBlock).map factorBlockValue).prod) = 1907120781648088563523 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_7
      · exact prime_oneHundredFortyFourEL_45407637658287822941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1907120781648088563523) ^ 953560390824044281761 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 1907120781648088563523) ^ 635706927216029521174 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 1907120781648088563523) ^ 272445825949726937646 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 1907120781648088563523) ^ 42 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_2565337097194552275503 : Nat.Prime 2565337097194552275503 := by
  apply lucas_primality 2565337097194552275503 (5 : ZMod 2565337097194552275503)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (60133, 1), (1804687, 1), (11819515781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (60133, 1), (1804687, 1), (11819515781, 1)] : List FactorBlock).map factorBlockValue).prod) = 2565337097194552275503 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_60133
      · exact prime_oneHundredFortyFourEL_1804687
      · exact prime_oneHundredFortyFourEL_11819515781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2565337097194552275503) ^ 1282668548597276137751 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 2565337097194552275503) ^ 42661052952531094 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 2565337097194552275503) ^ 1421485884917746 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 2565337097194552275503) ^ 217042486742 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_3074685732733041494149 : Nat.Prime 3074685732733041494149 := by
  apply lucas_primality 3074685732733041494149 (2 : ZMod 3074685732733041494149)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (256223811061086791179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (256223811061086791179, 1)] : List FactorBlock).map factorBlockValue).prod) = 3074685732733041494149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_256223811061086791179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3074685732733041494149) ^ 1537342866366520747074 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 3074685732733041494149) ^ 1024895244244347164716 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 3074685732733041494149) ^ 12 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_3380357550857605843033 : Nat.Prime 3380357550857605843033 := by
  apply lucas_primality 3380357550857605843033 (5 : ZMod 3380357550857605843033)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (46949410428577858931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (46949410428577858931, 1)] : List FactorBlock).map factorBlockValue).prod) = 3380357550857605843033 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_46949410428577858931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 3380357550857605843033) ^ 1690178775428802921516 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 3380357550857605843033) ^ 1126785850285868614344 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 3380357550857605843033) ^ 72 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_3420880671711613886411 : Nat.Prime 3420880671711613886411 := by
  apply lucas_primality 3420880671711613886411 (6 : ZMod 3420880671711613886411)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (1559, 1), (13048621, 1), (989186707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (1559, 1), (13048621, 1), (989186707, 1)] : List FactorBlock).map factorBlockValue).prod) = 3420880671711613886411 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_5
      · exact prime_oneHundredFortyFourEL_17
      · exact prime_oneHundredFortyFourEL_1559
      · exact prime_oneHundredFortyFourEL_13048621
      · exact prime_oneHundredFortyFourEL_989186707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 3420880671711613886411) ^ 1710440335855806943205 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (6 : ZMod 3420880671711613886411) ^ 684176134342322777282 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (6 : ZMod 3420880671711613886411) ^ 201228274806565522730 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (6 : ZMod 3420880671711613886411) ^ 2194278814439777990 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (6 : ZMod 3420880671711613886411) ^ 262164152956210 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (6 : ZMod 3420880671711613886411) ^ 3458276023630 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_6765081881491418082743 : Nat.Prime 6765081881491418082743 := by
  apply lucas_primality 6765081881491418082743 (5 : ZMod 6765081881491418082743)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (163, 1), (229, 1), (293, 1), (309280368906961, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (163, 1), (229, 1), (293, 1), (309280368906961, 1)] : List FactorBlock).map factorBlockValue).prod) = 6765081881491418082743 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_163
      · exact prime_oneHundredFortyFourEL_229
      · exact prime_oneHundredFortyFourEL_293
      · exact prime_oneHundredFortyFourEL_309280368906961
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 6765081881491418082743) ^ 3382540940745709041371 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 6765081881491418082743) ^ 41503569825100724434 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 6765081881491418082743) ^ 29541842277255100798 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 6765081881491418082743) ^ 23089016660380266494 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 6765081881491418082743) ^ 21873622 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_7774081564259573168707 : Nat.Prime 7774081564259573168707 := by
  apply lucas_primality 7774081564259573168707 (2 : ZMod 7774081564259573168707)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (78167, 1), (613918377372439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (78167, 1), (613918377372439, 1)] : List FactorBlock).map factorBlockValue).prod) = 7774081564259573168707 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_78167
      · exact prime_oneHundredFortyFourEL_613918377372439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7774081564259573168707) ^ 3887040782129786584353 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 7774081564259573168707) ^ 2591360521419857722902 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 7774081564259573168707) ^ 99454777134335118 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 7774081564259573168707) ^ 12663054 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_43345213432436553513973 : Nat.Prime 43345213432436553513973 := by
  apply lucas_primality 43345213432436553513973 (5 : ZMod 43345213432436553513973)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (43, 1), (212357987, 1), (395569541791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (43, 1), (212357987, 1), (395569541791, 1)] : List FactorBlock).map factorBlockValue).prod) = 43345213432436553513973 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_43
      · exact prime_oneHundredFortyFourEL_212357987
      · exact prime_oneHundredFortyFourEL_395569541791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 43345213432436553513973) ^ 21672606716218276756986 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 43345213432436553513973) ^ 14448404477478851171324 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 43345213432436553513973) ^ 1008028219358989616604 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 43345213432436553513973) ^ 204113883564156 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 43345213432436553513973) ^ 109576721292 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_47735865348336522210649 : Nat.Prime 47735865348336522210649 := by
  apply lucas_primality 47735865348336522210649 (19 : ZMod 47735865348336522210649)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (21532419833, 1), (92372079169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (21532419833, 1), (92372079169, 1)] : List FactorBlock).map factorBlockValue).prod) = 47735865348336522210649 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_21532419833
      · exact prime_oneHundredFortyFourEL_92372079169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 47735865348336522210649) ^ 23867932674168261105324 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (19 : ZMod 47735865348336522210649) ^ 15911955116112174070216 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (19 : ZMod 47735865348336522210649) ^ 2216929900056 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (19 : ZMod 47735865348336522210649) ^ 516778075992 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_47886543588161587791203 : Nat.Prime 47886543588161587791203 := by
  apply lucas_primality 47886543588161587791203 (2 : ZMod 47886543588161587791203)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (14201963, 1), (240844691621461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (14201963, 1), (240844691621461, 1)] : List FactorBlock).map factorBlockValue).prod) = 47886543588161587791203 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_7
      · exact prime_oneHundredFortyFourEL_14201963
      · exact prime_oneHundredFortyFourEL_240844691621461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 47886543588161587791203) ^ 23943271794080793895601 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 47886543588161587791203) ^ 6840934798308798255886 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 47886543588161587791203) ^ 3371825682700454 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 47886543588161587791203) ^ 198827482 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_50435018577897128050349 : Nat.Prime 50435018577897128050349 := by
  apply lucas_primality 50435018577897128050349 (2 : ZMod 50435018577897128050349)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (1146250422224934728417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (1146250422224934728417, 1)] : List FactorBlock).map factorBlockValue).prod) = 50435018577897128050349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_11
      · exact prime_oneHundredFortyFourEL_1146250422224934728417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 50435018577897128050349) ^ 25217509288948564025174 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 50435018577897128050349) ^ 4585001688899738913668 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 50435018577897128050349) ^ 44 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_123333107292132399552323 : Nat.Prime 123333107292132399552323 := by
  apply lucas_primality 123333107292132399552323 (2 : ZMod 123333107292132399552323)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (1907, 1), (1115067060486161687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (1907, 1), (1115067060486161687, 1)] : List FactorBlock).map factorBlockValue).prod) = 123333107292132399552323 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_29
      · exact prime_oneHundredFortyFourEL_1907
      · exact prime_oneHundredFortyFourEL_1115067060486161687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 123333107292132399552323) ^ 61666553646066199776161 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 123333107292132399552323) ^ 4252865768694220674218 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 123333107292132399552323) ^ 64673889508197377846 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 123333107292132399552323) ^ 110606 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_224575811670016923756907 : Nat.Prime 224575811670016923756907 := by
  apply lucas_primality 224575811670016923756907 (7 : ZMod 224575811670016923756907)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (22481, 1), (33978172901563879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (22481, 1), (33978172901563879, 1)] : List FactorBlock).map factorBlockValue).prod) = 224575811670016923756907 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_7
      · exact prime_oneHundredFortyFourEL_22481
      · exact prime_oneHundredFortyFourEL_33978172901563879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 224575811670016923756907) ^ 112287905835008461878453 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (7 : ZMod 224575811670016923756907) ^ 74858603890005641252302 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (7 : ZMod 224575811670016923756907) ^ 32082258810002417679558 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (7 : ZMod 224575811670016923756907) ^ 9989582833059780426 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (7 : ZMod 224575811670016923756907) ^ 6609414 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_363690497301491172040717 : Nat.Prime 363690497301491172040717 := by
  apply lucas_primality 363690497301491172040717 (2 : ZMod 363690497301491172040717)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (157, 1), (13511921, 1), (14286766865669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (157, 1), (13511921, 1), (14286766865669, 1)] : List FactorBlock).map factorBlockValue).prod) = 363690497301491172040717 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_157
      · exact prime_oneHundredFortyFourEL_13511921
      · exact prime_oneHundredFortyFourEL_14286766865669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 363690497301491172040717) ^ 181845248650745586020358 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 363690497301491172040717) ^ 121230165767163724013572 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 363690497301491172040717) ^ 2316499982812045681788 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 363690497301491172040717) ^ 26916268774920396 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 363690497301491172040717) ^ 25456459164 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_421226894041107731343491 : Nat.Prime 421226894041107731343491 := by
  apply lucas_primality 421226894041107731343491 (2 : ZMod 421226894041107731343491)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (47, 1), (66373, 1), (85621, 1), (157705373099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (47, 1), (66373, 1), (85621, 1), (157705373099, 1)] : List FactorBlock).map factorBlockValue).prod) = 421226894041107731343491 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_5
      · exact prime_oneHundredFortyFourEL_47
      · exact prime_oneHundredFortyFourEL_66373
      · exact prime_oneHundredFortyFourEL_85621
      · exact prime_oneHundredFortyFourEL_157705373099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 421226894041107731343491) ^ 210613447020553865671745 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 421226894041107731343491) ^ 84245378808221546268698 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 421226894041107731343491) ^ 8962274341300164496670 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 421226894041107731343491) ^ 6346359122551455130 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 421226894041107731343491) ^ 4919668002488965690 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 421226894041107731343491) ^ 2670973637510 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_581830219274470462096123 : Nat.Prime 581830219274470462096123 := by
  apply lucas_primality 581830219274470462096123 (7 : ZMod 581830219274470462096123)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (101, 1), (173, 1), (271, 1), (1326859, 1), (2204882453, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (101, 1), (173, 1), (271, 1), (1326859, 1), (2204882453, 1)] : List FactorBlock).map factorBlockValue).prod) = 581830219274470462096123 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_7
      · exact prime_oneHundredFortyFourEL_101
      · exact prime_oneHundredFortyFourEL_173
      · exact prime_oneHundredFortyFourEL_271
      · exact prime_oneHundredFortyFourEL_1326859
      · exact prime_oneHundredFortyFourEL_2204882453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 581830219274470462096123) ^ 290915109637235231048061 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (7 : ZMod 581830219274470462096123) ^ 193943406424823487365374 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (7 : ZMod 581830219274470462096123) ^ 83118602753495780299446 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (7 : ZMod 581830219274470462096123) ^ 5760695240341291703922 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (7 : ZMod 581830219274470462096123) ^ 3363180458233933306914 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (7 : ZMod 581830219274470462096123) ^ 2146974978872584730982 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (7 : ZMod 581830219274470462096123) ^ 438501920154643758 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (7 : ZMod 581830219274470462096123) ^ 263882647568274 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_878899926231809511221431 : Nat.Prime 878899926231809511221431 := by
  apply lucas_primality 878899926231809511221431 (6 : ZMod 878899926231809511221431)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 1), (797, 1), (125287, 1), (13971226936099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 1), (797, 1), (125287, 1), (13971226936099, 1)] : List FactorBlock).map factorBlockValue).prod) = 878899926231809511221431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_5
      · exact prime_oneHundredFortyFourEL_7
      · exact prime_oneHundredFortyFourEL_797
      · exact prime_oneHundredFortyFourEL_125287
      · exact prime_oneHundredFortyFourEL_13971226936099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 878899926231809511221431) ^ 439449963115904755610715 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (6 : ZMod 878899926231809511221431) ^ 292966642077269837073810 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (6 : ZMod 878899926231809511221431) ^ 175779985246361902244286 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (6 : ZMod 878899926231809511221431) ^ 125557132318829930174490 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (6 : ZMod 878899926231809511221431) ^ 1102760258760112310190 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (6 : ZMod 878899926231809511221431) ^ 7015092756884668890 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (6 : ZMod 878899926231809511221431) ^ 62907855570 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_1454761989205964688162869 : Nat.Prime 1454761989205964688162869 := by
  apply lucas_primality 1454761989205964688162869 (2 : ZMod 1454761989205964688162869)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (363690497301491172040717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (363690497301491172040717, 1)] : List FactorBlock).map factorBlockValue).prod) = 1454761989205964688162869 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_363690497301491172040717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 1454761989205964688162869) ^ 727380994602982344081434 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 1454761989205964688162869) ^ 4 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_1600571905597713833007127 : Nat.Prime 1600571905597713833007127 := by
  apply lucas_primality 1600571905597713833007127 (3 : ZMod 1600571905597713833007127)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2325976321, 1), (114688177114201, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2325976321, 1), (114688177114201, 1)] : List FactorBlock).map factorBlockValue).prod) = 1600571905597713833007127 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_2325976321
      · exact prime_oneHundredFortyFourEL_114688177114201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1600571905597713833007127) ^ 800285952798856916503563 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 1600571905597713833007127) ^ 533523968532571277669042 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 1600571905597713833007127) ^ 688129062685206 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 1600571905597713833007127) ^ 13955857926 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_1941834217042948565255393 : Nat.Prime 1941834217042948565255393 := by
  apply lucas_primality 1941834217042948565255393 (3 : ZMod 1941834217042948565255393)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (41, 1), (79, 1), (124596973, 1), (150363951973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (41, 1), (79, 1), (124596973, 1), (150363951973, 1)] : List FactorBlock).map factorBlockValue).prod) = 1941834217042948565255393 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_41
      · exact prime_oneHundredFortyFourEL_79
      · exact prime_oneHundredFortyFourEL_124596973
      · exact prime_oneHundredFortyFourEL_150363951973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1941834217042948565255393) ^ 970917108521474282627696 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 1941834217042948565255393) ^ 47361810171779233298912 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 1941834217042948565255393) ^ 24580179962568969180448 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 1941834217042948565255393) ^ 15584922894097504 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 1941834217042948565255393) ^ 12914227057504 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_4472636383743338313409943 : Nat.Prime 4472636383743338313409943 := by
  apply lucas_primality 4472636383743338313409943 (5 : ZMod 4472636383743338313409943)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (70496453, 1), (4531774490983801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (70496453, 1), (4531774490983801, 1)] : List FactorBlock).map factorBlockValue).prod) = 4472636383743338313409943 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_7
      · exact prime_oneHundredFortyFourEL_70496453
      · exact prime_oneHundredFortyFourEL_4531774490983801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 4472636383743338313409943) ^ 2236318191871669156704971 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 4472636383743338313409943) ^ 638948054820476901915706 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 4472636383743338313409943) ^ 63444842873773214 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (5 : ZMod 4472636383743338313409943) ^ 986950342 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_13370488597408814070653897 : Nat.Prime 13370488597408814070653897 := by
  apply lucas_primality 13370488597408814070653897 (3 : ZMod 13370488597408814070653897)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (263, 1), (311, 1), (18427, 1), (85298847890759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (263, 1), (311, 1), (18427, 1), (85298847890759, 1)] : List FactorBlock).map factorBlockValue).prod) = 13370488597408814070653897 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_13
      · exact prime_oneHundredFortyFourEL_263
      · exact prime_oneHundredFortyFourEL_311
      · exact prime_oneHundredFortyFourEL_18427
      · exact prime_oneHundredFortyFourEL_85298847890759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 13370488597408814070653897) ^ 6685244298704407035326948 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 13370488597408814070653897) ^ 1028499122877601082357992 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 13370488597408814070653897) ^ 50838359685965072511992 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 13370488597408814070653897) ^ 42991924750510656175736 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 13370488597408814070653897) ^ 725592261215000492248 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 13370488597408814070653897) ^ 156748759544 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_14372851946881083120442049 : Nat.Prime 14372851946881083120442049 := by
  apply lucas_primality 14372851946881083120442049 (3 : ZMod 14372851946881083120442049)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (224575811670016923756907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (224575811670016923756907, 1)] : List FactorBlock).map factorBlockValue).prod) = 14372851946881083120442049 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_224575811670016923756907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 14372851946881083120442049) ^ 7186425973440541560221024 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 14372851946881083120442049) ^ 64 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_53251933472257250410270901 : Nat.Prime 53251933472257250410270901 := by
  apply lucas_primality 53251933472257250410270901 (3 : ZMod 53251933472257250410270901)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (74887, 1), (1910471, 1), (3722103952517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (74887, 1), (1910471, 1), (3722103952517, 1)] : List FactorBlock).map factorBlockValue).prod) = 53251933472257250410270901 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_5
      · exact prime_oneHundredFortyFourEL_74887
      · exact prime_oneHundredFortyFourEL_1910471
      · exact prime_oneHundredFortyFourEL_3722103952517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 53251933472257250410270901) ^ 26625966736128625205135450 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 53251933472257250410270901) ^ 10650386694451450082054180 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 53251933472257250410270901) ^ 711097166026910550700 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 53251933472257250410270901) ^ 27873719869214057900 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 53251933472257250410270901) ^ 14306944177700 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_1685608230800063659026099707 : Nat.Prime 1685608230800063659026099707 := by
  apply lucas_primality 1685608230800063659026099707 (2 : ZMod 1685608230800063659026099707)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1431512219, 1), (588750905660297287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1431512219, 1), (588750905660297287, 1)] : List FactorBlock).map factorBlockValue).prod) = 1685608230800063659026099707 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_1431512219
      · exact prime_oneHundredFortyFourEL_588750905660297287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1685608230800063659026099707) ^ 842804115400031829513049853 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 1685608230800063659026099707) ^ 1177501811320594574 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 1685608230800063659026099707) ^ 2863024438 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_2579491383497067114570243491 : Nat.Prime 2579491383497067114570243491 := by
  apply lucas_primality 2579491383497067114570243491 (2 : ZMod 2579491383497067114570243491)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (103573, 1), (10089149659, 1), (35264271901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (103573, 1), (10089149659, 1), (35264271901, 1)] : List FactorBlock).map factorBlockValue).prod) = 2579491383497067114570243491 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_5
      · exact prime_oneHundredFortyFourEL_7
      · exact prime_oneHundredFortyFourEL_103573
      · exact prime_oneHundredFortyFourEL_10089149659
      · exact prime_oneHundredFortyFourEL_35264271901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2579491383497067114570243491) ^ 1289745691748533557285121745 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 2579491383497067114570243491) ^ 515898276699413422914048698 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 2579491383497067114570243491) ^ 368498769071009587795749070 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 2579491383497067114570243491) ^ 24905056177740020223130 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 2579491383497067114570243491) ^ 255669850352159110 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 2579491383497067114570243491) ^ 73147444834212490 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_3273969832900123645416078277 : Nat.Prime 3273969832900123645416078277 := by
  apply lucas_primality 3273969832900123645416078277 (2 : ZMod 3273969832900123645416078277)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (61, 1), (4472636383743338313409943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (61, 1), (4472636383743338313409943, 1)] : List FactorBlock).map factorBlockValue).prod) = 3273969832900123645416078277 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_61
      · exact prime_oneHundredFortyFourEL_4472636383743338313409943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3273969832900123645416078277) ^ 1636984916450061822708039138 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 3273969832900123645416078277) ^ 1091323277633374548472026092 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 3273969832900123645416078277) ^ 53671636604920059760919316 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 3273969832900123645416078277) ^ 732 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_21280803913850803695204508801 : Nat.Prime 21280803913850803695204508801 := by
  apply lucas_primality 21280803913850803695204508801 (14 : ZMod 21280803913850803695204508801)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 2), (5, 2), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 2), (5, 2), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850803695204508801 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_5
      · exact prime_oneHundredFortyFourEL_171401
      · exact prime_oneHundredFortyFourEL_714027719
      · exact prime_oneHundredFortyFourEL_6037638679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 21280803913850803695204508801) ^ 10640401956925401847602254400 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (14 : ZMod 21280803913850803695204508801) ^ 7093601304616934565068169600 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (14 : ZMod 21280803913850803695204508801) ^ 4256160782770160739040901760 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (14 : ZMod 21280803913850803695204508801) ^ 124157991574441244188800 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (14 : ZMod 21280803913850803695204508801) ^ 29803890447915235200 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (14 : ZMod 21280803913850803695204508801) ^ 3524689873852387200 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_56748810436935476520545356807 : Nat.Prime 56748810436935476520545356807 := by
  apply lucas_primality 56748810436935476520545356807 (3 : ZMod 56748810436935476520545356807)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (89, 1), (347, 1), (2755243, 1), (37051420944511243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (89, 1), (347, 1), (2755243, 1), (37051420944511243, 1)] : List FactorBlock).map factorBlockValue).prod) = 56748810436935476520545356807 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_89
      · exact prime_oneHundredFortyFourEL_347
      · exact prime_oneHundredFortyFourEL_2755243
      · exact prime_oneHundredFortyFourEL_37051420944511243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 56748810436935476520545356807) ^ 28374405218467738260272678403 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 56748810436935476520545356807) ^ 18916270145645158840181785602 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 56748810436935476520545356807) ^ 637627083561072769893768054 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 56748810436935476520545356807) ^ 163541240452263621096672498 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 56748810436935476520545356807) ^ 20596662594528132916242 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 56748810436935476520545356807) ^ 1531623052242 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_85123215655403214780818035207 : Nat.Prime 85123215655403214780818035207 := by
  apply lucas_primality 85123215655403214780818035207 (3 : ZMod 85123215655403214780818035207)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (31, 1), (503, 1), (47886543588161587791203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (31, 1), (503, 1), (47886543588161587791203, 1)] : List FactorBlock).map factorBlockValue).prod) = 85123215655403214780818035207 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_19
      · exact prime_oneHundredFortyFourEL_31
      · exact prime_oneHundredFortyFourEL_503
      · exact prime_oneHundredFortyFourEL_47886543588161587791203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 85123215655403214780818035207) ^ 42561607827701607390409017603 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 85123215655403214780818035207) ^ 28374405218467738260272678402 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 85123215655403214780818035207) ^ 4480169245021221830569370274 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 85123215655403214780818035207) ^ 2745910182432361767123162426 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 85123215655403214780818035207) ^ 169231045040563051254111402 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 85123215655403214780818035207) ^ 1777602 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_170246431310806429561636070441 : Nat.Prime 170246431310806429561636070441 := by
  apply lucas_primality 170246431310806429561636070441 (3 : ZMod 170246431310806429561636070441)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (84389, 1), (50435018577897128050349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (84389, 1), (50435018577897128050349, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_5
      · exact prime_oneHundredFortyFourEL_84389
      · exact prime_oneHundredFortyFourEL_50435018577897128050349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 170246431310806429561636070441) ^ 85123215655403214780818035220 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 170246431310806429561636070441) ^ 34049286262161285912327214088 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 170246431310806429561636070441) ^ 2017400743115885122013960 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (3 : ZMod 170246431310806429561636070441) ^ 3375560 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem prime_oneHundredFortyFourEL_170246431310806429561636070491 : Nat.Prime 170246431310806429561636070491 := by
  apply lucas_primality 170246431310806429561636070491 (2 : ZMod 170246431310806429561636070491)
  · rw [← oneHundredFortyFourELFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (271, 1), (1217, 1), (4440187, 1), (1291737826932829, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (271, 1), (1217, 1), (4440187, 1), (1291737826932829, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070491 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFortyFourEL_2
      · exact prime_oneHundredFortyFourEL_3
      · exact prime_oneHundredFortyFourEL_5
      · exact prime_oneHundredFortyFourEL_271
      · exact prime_oneHundredFortyFourEL_1217
      · exact prime_oneHundredFortyFourEL_4440187
      · exact prime_oneHundredFortyFourEL_1291737826932829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 170246431310806429561636070491) ^ 85123215655403214780818035245 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 170246431310806429561636070491) ^ 56748810436935476520545356830 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 170246431310806429561636070491) ^ 34049286262161285912327214098 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 170246431310806429561636070491) ^ 628215613693012655208989190 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 170246431310806429561636070491) ^ 139890247584886137684170970 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 170246431310806429561636070491) ^ 38342175973851198060270 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide
    · change (2 : ZMod 170246431310806429561636070491) ^ 131796427851810 ≠ 1
      rw [← oneHundredFortyFourELFastPow_eq_pow]
      decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070400 : Nat.totient 170246431310806429561636070400 = 45398783408065799221592064000 := by
  rw [← show ((([(2, 10), (3, 2), (5, 2), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070400 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_2, prime_oneHundredFortyFourEL_3, prime_oneHundredFortyFourEL_5, prime_oneHundredFortyFourEL_171401, prime_oneHundredFortyFourEL_714027719, prime_oneHundredFortyFourEL_6037638679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070401 : Nat.totient 170246431310806429561636070401 = 170168232012650049364389434880 := by
  rw [← show ((([(2179, 1), (2487047, 1), (499514461, 1), (62891033057, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070401 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_2179, prime_oneHundredFortyFourEL_2487047, prime_oneHundredFortyFourEL_499514461, prime_oneHundredFortyFourEL_62891033057]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070402 : Nat.totient 170246431310806429561636070402 = 85122365002117604788644743040 := by
  rw [← show ((([(2, 1), (100069, 1), (10543823989, 1), (80677106545561, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070402 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_2, prime_oneHundredFortyFourEL_100069, prime_oneHundredFortyFourEL_10543823989, prime_oneHundredFortyFourEL_80677106545561]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070403 : Nat.totient 170246431310806429561636070403 = 97283136458340307929368976768 := by
  rw [← show ((([(3, 1), (7, 1), (182653, 1), (16318037, 1), (2719969280209463, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070403 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_3, prime_oneHundredFortyFourEL_7, prime_oneHundredFortyFourEL_182653, prime_oneHundredFortyFourEL_16318037, prime_oneHundredFortyFourEL_2719969280209463]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070404 : Nat.totient 170246431310806429561636070404 = 78575275989602967489985878624 := by
  rw [← show ((([(2, 2), (13, 1), (3273969832900123645416078277, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070404 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_2, prime_oneHundredFortyFourEL_13, prime_oneHundredFortyFourEL_3273969832900123645416078277]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070405 : Nat.totient 170246431310806429561636070405 = 129010719075204602089087822848 := by
  rw [← show ((([(5, 1), (23, 1), (103, 1), (14372851946881083120442049, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070405 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_5, prime_oneHundredFortyFourEL_23, prime_oneHundredFortyFourEL_103, prime_oneHundredFortyFourEL_14372851946881083120442049]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070406 : Nat.totient 170246431310806429561636070406 = 51589827669941342291404869800 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (2579491383497067114570243491, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070406 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_2, prime_oneHundredFortyFourEL_3, prime_oneHundredFortyFourEL_11, prime_oneHundredFortyFourEL_2579491383497067114570243491]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070407 : Nat.totient 170246431310806429561636070407 = 168560823080006365902609970600 := by
  rw [← show ((([(101, 1), (1685608230800063659026099707, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070407 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_101, prime_oneHundredFortyFourEL_1685608230800063659026099707]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070408 : Nat.totient 170246431310806429561636070408 = 85123215655403214780818035200 := by
  rw [← show ((([(2, 3), (21280803913850803695204508801, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070408 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_2, prime_oneHundredFortyFourEL_21280803913850803695204508801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070409 : Nat.totient 170246431310806429561636070409 = 109473996102439802018306583168 := by
  rw [← show ((([(3, 2), (29, 1), (997, 1), (1953042799, 1), (334989034308223, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070409 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_3, prime_oneHundredFortyFourEL_29, prime_oneHundredFortyFourEL_997, prime_oneHundredFortyFourEL_1953042799, prime_oneHundredFortyFourEL_334989034308223]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070410 : Nat.totient 170246431310806429561636070410 = 57547524501405401686432372800 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (71, 1), (101863, 1), (336283195596828725831, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070410 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_2, prime_oneHundredFortyFourEL_5, prime_oneHundredFortyFourEL_7, prime_oneHundredFortyFourEL_71, prime_oneHundredFortyFourEL_101863, prime_oneHundredFortyFourEL_336283195596828725831]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070411 : Nat.totient 170246431310806429561636070411 = 164653275227858846087080790016 := by
  rw [← show ((([(37, 1), (167, 1), (11846617, 1), (2325763089382150177, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070411 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_37, prime_oneHundredFortyFourEL_167, prime_oneHundredFortyFourEL_11846617, prime_oneHundredFortyFourEL_2325763089382150177]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070412 : Nat.totient 170246431310806429561636070412 = 51924336943515372873756152640 := by
  rw [← show ((([(2, 2), (3, 1), (19, 1), (31, 1), (503, 1), (47886543588161587791203, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070412 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_2, prime_oneHundredFortyFourEL_3, prime_oneHundredFortyFourEL_19, prime_oneHundredFortyFourEL_31, prime_oneHundredFortyFourEL_503, prime_oneHundredFortyFourEL_47886543588161587791203]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070413 : Nat.totient 170246431310806429561636070413 = 167455505410972156719620294400 := by
  rw [← show ((([(61, 1), (210271273, 1), (13272973828697194921, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070413 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_61, prime_oneHundredFortyFourEL_210271273, prime_oneHundredFortyFourEL_13272973828697194921]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070414 : Nat.totient 170246431310806429561636070414 = 85123215655403214780818035206 := by
  rw [← show ((([(2, 1), (85123215655403214780818035207, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070414 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_2, prime_oneHundredFortyFourEL_85123215655403214780818035207]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070415 : Nat.totient 170246431310806429561636070415 = 90793442057342566669175645856 := by
  rw [← show ((([(3, 1), (5, 1), (19507, 1), (581830219274470462096123, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070415 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_3, prime_oneHundredFortyFourEL_5, prime_oneHundredFortyFourEL_19507, prime_oneHundredFortyFourEL_581830219274470462096123]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070416 : Nat.totient 170246431310806429561636070416 = 78066458596338135682052063232 := by
  rw [← show ((([(2, 4), (17, 1), (73, 1), (83, 1), (906208483, 1), (113993486613649, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070416 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_2, prime_oneHundredFortyFourEL_17, prime_oneHundredFortyFourEL_73, prime_oneHundredFortyFourEL_83, prime_oneHundredFortyFourEL_906208483, prime_oneHundredFortyFourEL_113993486613649]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070417 : Nat.totient 170246431310806429561636070417 = 121833376707460069573765764480 := by
  rw [← show ((([(7, 2), (11, 1), (13, 1), (197, 1), (123333107292132399552323, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070417 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_7, prime_oneHundredFortyFourEL_11, prime_oneHundredFortyFourEL_13, prime_oneHundredFortyFourEL_197, prime_oneHundredFortyFourEL_123333107292132399552323]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070418 : Nat.totient 170246431310806429561636070418 = 55949459348399723610728628096 := by
  rw [← show ((([(2, 1), (3, 3), (89, 1), (347, 1), (2755243, 1), (37051420944511243, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070418 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_2, prime_oneHundredFortyFourEL_3, prime_oneHundredFortyFourEL_89, prime_oneHundredFortyFourEL_347, prime_oneHundredFortyFourEL_2755243, prime_oneHundredFortyFourEL_37051420944511243]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070419 : Nat.totient 170246431310806429561636070419 = 170193639779345304038252868480 := by
  rw [← show ((([(5227, 1), (11483, 1), (31531, 1), (89956470563501489, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070419 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_5227, prime_oneHundredFortyFourEL_11483, prime_oneHundredFortyFourEL_31531, prime_oneHundredFortyFourEL_89956470563501489]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070420 : Nat.totient 170246431310806429561636070420 = 68098546564904517849066781440 := by
  rw [← show ((([(2, 2), (5, 1), (2623979, 1), (10014130171, 1), (323947351769, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070420 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_2, prime_oneHundredFortyFourEL_5, prime_oneHundredFortyFourEL_2623979, prime_oneHundredFortyFourEL_10014130171, prime_oneHundredFortyFourEL_323947351769]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070421 : Nat.totient 170246431310806429561636070421 = 113497620873870953041090713612 := by
  rw [← show ((([(3, 1), (56748810436935476520545356807, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070421 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_3, prime_oneHundredFortyFourEL_56748810436935476520545356807]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070422 : Nat.totient 170246431310806429561636070422 = 85108460470877597653278627840 := by
  rw [← show ((([(2, 1), (5779, 1), (3345961, 1), (4402247467841949569, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070422 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_2, prime_oneHundredFortyFourEL_5779, prime_oneHundredFortyFourEL_3345961, prime_oneHundredFortyFourEL_4402247467841949569]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070423 : Nat.totient 170246431310806429561636070423 = 170214994587827508507813590784 := by
  rw [← show ((([(5923, 1), (63197, 1), (454820280659747008033, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070423 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_5923, prime_oneHundredFortyFourEL_63197, prime_oneHundredFortyFourEL_454820280659747008033]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070424 : Nat.totient 170246431310806429561636070424 = 48599650320914138732500193280 := by
  rw [← show ((([(2, 3), (3, 1), (7, 1), (1153, 1), (878899926231809511221431, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070424 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_2, prime_oneHundredFortyFourEL_3, prime_oneHundredFortyFourEL_7, prime_oneHundredFortyFourEL_1153, prime_oneHundredFortyFourEL_878899926231809511221431]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070425 : Nat.totient 170246431310806429561636070425 = 136197145047569938594055378000 := by
  rw [← show ((([(5, 2), (126671154767, 1), (53760126091519151, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070425 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_5, prime_oneHundredFortyFourEL_126671154767, prime_oneHundredFortyFourEL_53760126091519151]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070426 : Nat.totient 170246431310806429561636070426 = 83312077075982563852340382096 := by
  rw [← show ((([(2, 1), (47, 1), (13158487, 1), (137639855401863636917, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070426 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_2, prime_oneHundredFortyFourEL_47, prime_oneHundredFortyFourEL_13158487, prime_oneHundredFortyFourEL_137639855401863636917]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070427 : Nat.totient 170246431310806429561636070427 = 109454784962551391219264946720 := by
  rw [← show ((([(3, 2), (43, 2), (79, 1), (1233371, 1), (104997213222150383, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070427 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_3, prime_oneHundredFortyFourEL_43, prime_oneHundredFortyFourEL_79, prime_oneHundredFortyFourEL_1233371, prime_oneHundredFortyFourEL_104997213222150383]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070428 : Nat.totient 170246431310806429561636070428 = 73436148045809571899527358400 := by
  rw [← show ((([(2, 2), (11, 1), (23, 1), (127, 1), (61027, 1), (21705598351229560111, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070428 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_2, prime_oneHundredFortyFourEL_11, prime_oneHundredFortyFourEL_23, prime_oneHundredFortyFourEL_127, prime_oneHundredFortyFourEL_61027, prime_oneHundredFortyFourEL_21705598351229560111]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070429 : Nat.totient 170246431310806429561636070429 = 170246431310803718532927503040 := by
  rw [← show ((([(64323921637009, 1), (2646704786930381, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070429 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_64323921637009, prime_oneHundredFortyFourEL_2646704786930381]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070430 : Nat.totient 170246431310806429561636070430 = 41906813858281878017399514240 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (13, 1), (14757462491, 1), (29580241950103007, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070430 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_2, prime_oneHundredFortyFourEL_3, prime_oneHundredFortyFourEL_5, prime_oneHundredFortyFourEL_13, prime_oneHundredFortyFourEL_14757462491, prime_oneHundredFortyFourEL_29580241950103007]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070431 : Nat.totient 170246431310806429561636070431 = 137995275527104252160597704704 := by
  rw [← show ((([(7, 1), (19, 1), (563, 1), (31393, 1), (72424442559110913473, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070431 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_7, prime_oneHundredFortyFourEL_19, prime_oneHundredFortyFourEL_563, prime_oneHundredFortyFourEL_31393, prime_oneHundredFortyFourEL_72424442559110913473]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070432 : Nat.totient 170246431310806429561636070432 = 85123215655379912631475427392 := by
  rw [← show ((([(2, 5), (3662228970263, 1), (1452722104942727, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070432 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_2, prime_oneHundredFortyFourEL_3662228970263, prime_oneHundredFortyFourEL_1452722104942727]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070433 : Nat.totient 170246431310806429561636070433 = 104109121056243553523821117440 := by
  rw [← show ((([(3, 1), (17, 1), (41, 1), (1249, 1), (4463, 1), (14606113093399511149, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070433 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_3, prime_oneHundredFortyFourEL_17, prime_oneHundredFortyFourEL_41, prime_oneHundredFortyFourEL_1249, prime_oneHundredFortyFourEL_4463, prime_oneHundredFortyFourEL_14606113093399511149]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070434 : Nat.totient 170246431310806429561636070434 = 85120127797355926098006893248 := by
  rw [← show ((([(2, 1), (45233, 1), (70583, 1), (26661987197588219303, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070434 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_2, prime_oneHundredFortyFourEL_45233, prime_oneHundredFortyFourEL_70583, prime_oneHundredFortyFourEL_26661987197588219303]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070435 : Nat.totient 170246431310806429561636070435 = 135235251430065934423022016000 := by
  rw [← show ((([(5, 1), (151, 1), (2467, 1), (34757, 1), (113381, 1), (23194197396883, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070435 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_5, prime_oneHundredFortyFourEL_151, prime_oneHundredFortyFourEL_2467, prime_oneHundredFortyFourEL_34757, prime_oneHundredFortyFourEL_113381, prime_oneHundredFortyFourEL_23194197396883]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070436 : Nat.totient 170246431310806429561636070436 = 56741304949830443959591236480 := by
  rw [← show ((([(2, 2), (3, 2), (7561, 1), (2416168199, 1), (258862483991359, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070436 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_2, prime_oneHundredFortyFourEL_3, prime_oneHundredFortyFourEL_7561, prime_oneHundredFortyFourEL_2416168199, prime_oneHundredFortyFourEL_258862483991359]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070437 : Nat.totient 170246431310806429561636070437 = 167959904379435044156986705152 := by
  rw [← show ((([(137, 1), (163, 1), (23929, 1), (318599651038406015063, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070437 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_137, prime_oneHundredFortyFourEL_163, prime_oneHundredFortyFourEL_23929, prime_oneHundredFortyFourEL_318599651038406015063]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070438 : Nat.totient 170246431310806429561636070438 = 70445493117389520072375590304 := by
  rw [← show ((([(2, 1), (7, 1), (29, 1), (53939, 1), (7774081564259573168707, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070438 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_2, prime_oneHundredFortyFourEL_7, prime_oneHundredFortyFourEL_29, prime_oneHundredFortyFourEL_53939, prime_oneHundredFortyFourEL_7774081564259573168707]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070439 : Nat.totient 170246431310806429561636070439 = 103017014041335925345208064000 := by
  rw [← show ((([(3, 1), (11, 1), (661, 1), (15791, 1), (4952209, 1), (99805395286837, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070439 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_3, prime_oneHundredFortyFourEL_11, prime_oneHundredFortyFourEL_661, prime_oneHundredFortyFourEL_15791, prime_oneHundredFortyFourEL_4952209, prime_oneHundredFortyFourEL_99805395286837]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070440 : Nat.totient 170246431310806429561636070440 = 68097765564025325470604272384 := by
  rw [← show ((([(2, 3), (5, 1), (84389, 1), (50435018577897128050349, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070440 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_2, prime_oneHundredFortyFourEL_5, prime_oneHundredFortyFourEL_84389, prime_oneHundredFortyFourEL_50435018577897128050349]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070441 : Nat.totient 170246431310806429561636070441 = 170246431310806429561636070440 := by
  rw [← show ((([(170246431310806429561636070441, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070441 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_170246431310806429561636070441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070442 : Nat.totient 170246431310806429561636070442 = 56729709524543374302228685440 := by
  rw [← show ((([(2, 1), (3, 1), (2971, 1), (626696252953, 1), (15239370115789, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070442 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_2, prime_oneHundredFortyFourEL_3, prime_oneHundredFortyFourEL_2971, prime_oneHundredFortyFourEL_626696252953, prime_oneHundredFortyFourEL_15239370115789]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070443 : Nat.totient 170246431310806429561636070443 = 149391218917736061810647040000 := by
  rw [← show ((([(13, 1), (31, 1), (59, 1), (1381, 1), (40213, 1), (438401, 1), (294096103603, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070443 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_13, prime_oneHundredFortyFourEL_31, prime_oneHundredFortyFourEL_59, prime_oneHundredFortyFourEL_1381, prime_oneHundredFortyFourEL_40213, prime_oneHundredFortyFourEL_438401, prime_oneHundredFortyFourEL_294096103603]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070444 : Nat.totient 170246431310806429561636070444 = 85123207809988048627971901136 := by
  rw [← show ((([(2, 2), (10895267, 1), (2619477239, 1), (1491301720847, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070444 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_2, prime_oneHundredFortyFourEL_10895267, prime_oneHundredFortyFourEL_2619477239, prime_oneHundredFortyFourEL_1491301720847]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070445 : Nat.totient 170246431310806429561636070445 = 77763954907043908251696820224 := by
  rw [← show ((([(3, 6), (5, 1), (7, 1), (1277, 1), (38153, 1), (45994279, 1), (2977549837, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070445 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_3, prime_oneHundredFortyFourEL_5, prime_oneHundredFortyFourEL_7, prime_oneHundredFortyFourEL_1277, prime_oneHundredFortyFourEL_38153, prime_oneHundredFortyFourEL_45994279, prime_oneHundredFortyFourEL_2977549837]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070446 : Nat.totient 170246431310806429561636070446 = 85123215655389611292157980768 := by
  rw [← show ((([(2, 1), (6260335829159, 1), (13597228324225297, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070446 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_2, prime_oneHundredFortyFourEL_6260335829159, prime_oneHundredFortyFourEL_13597228324225297]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070447 : Nat.totient 170246431310806429561636070447 = 170225574004461135087641303064 := by
  rw [← show ((([(13907, 1), (19759, 1), (619554621871215616219, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070447 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_13907, prime_oneHundredFortyFourEL_19759, prime_oneHundredFortyFourEL_619554621871215616219]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070448 : Nat.totient 170246431310806429561636070448 = 55213287784522733734017435648 := by
  rw [← show ((([(2, 4), (3, 1), (37, 1), (31177, 1), (3074685732733041494149, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070448 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_2, prime_oneHundredFortyFourEL_3, prime_oneHundredFortyFourEL_37, prime_oneHundredFortyFourEL_31177, prime_oneHundredFortyFourEL_3074685732733041494149]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070449 : Nat.totient 170246431310806429561636070449 = 166335872761895561413472010240 := by
  rw [← show ((([(53, 1), (283, 1), (1549, 1), (246817, 1), (20386907, 1), (1456256521, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070449 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_53, prime_oneHundredFortyFourEL_283, prime_oneHundredFortyFourEL_1549, prime_oneHundredFortyFourEL_246817, prime_oneHundredFortyFourEL_20386907, prime_oneHundredFortyFourEL_1456256521]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070450 : Nat.totient 170246431310806429561636070450 = 54296036627613610411524096000 := by
  rw [← show ((([(2, 1), (5, 2), (11, 1), (17, 1), (19, 1), (67, 1), (857, 1), (3361, 1), (4965793642285667, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070450 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_2, prime_oneHundredFortyFourEL_5, prime_oneHundredFortyFourEL_11, prime_oneHundredFortyFourEL_17, prime_oneHundredFortyFourEL_19, prime_oneHundredFortyFourEL_67, prime_oneHundredFortyFourEL_857, prime_oneHundredFortyFourEL_3361, prime_oneHundredFortyFourEL_4965793642285667]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070451 : Nat.totient 170246431310806429561636070451 = 108561034516050753961381824096 := by
  rw [← show ((([(3, 1), (23, 1), (56923, 1), (43345213432436553513973, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070451 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_3, prime_oneHundredFortyFourEL_23, prime_oneHundredFortyFourEL_56923, prime_oneHundredFortyFourEL_43345213432436553513973]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070452 : Nat.totient 170246431310806429561636070452 = 72939717748522732251845087712 := by
  rw [← show ((([(2, 2), (7, 1), (3167, 1), (886981163, 1), (2164499678281279, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070452 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_2, prime_oneHundredFortyFourEL_7, prime_oneHundredFortyFourEL_3167, prime_oneHundredFortyFourEL_886981163, prime_oneHundredFortyFourEL_2164499678281279]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070453 : Nat.totient 170246431310806429561636070453 = 170246431310796479651428692300 := by
  rw [← show ((([(17139873932003, 1), (9932770333446151, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070453 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_17139873932003, prime_oneHundredFortyFourEL_9932770333446151]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070454 : Nat.totient 170246431310806429561636070454 = 56673230341708626606805950000 := by
  rw [← show ((([(2, 1), (3, 2), (751, 1), (3594403, 1), (3503795954666829551, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070454 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_2, prime_oneHundredFortyFourEL_3, prime_oneHundredFortyFourEL_751, prime_oneHundredFortyFourEL_3594403, prime_oneHundredFortyFourEL_3503795954666829551]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070455 : Nat.totient 170246431310806429561636070455 = 136188757905323772750696557568 := by
  rw [← show ((([(5, 1), (16249, 1), (25868083, 1), (81005988925976273, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070455 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_5, prime_oneHundredFortyFourEL_16249, prime_oneHundredFortyFourEL_25868083, prime_oneHundredFortyFourEL_81005988925976273]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070456 : Nat.totient 170246431310806429561636070456 = 78575275989595304509109674752 := by
  rw [← show ((([(2, 3), (13, 1), (11013696930283, 1), (148631737990633, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070456 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_2, prime_oneHundredFortyFourEL_13, prime_oneHundredFortyFourEL_11013696930283, prime_oneHundredFortyFourEL_148631737990633]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070457 : Nat.totient 170246431310806429561636070457 = 113433750514043666898268718592 := by
  rw [← show ((([(3, 1), (1777, 1), (23605829803, 1), (1352851298914249, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070457 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_3, prime_oneHundredFortyFourEL_1777, prime_oneHundredFortyFourEL_23605829803, prime_oneHundredFortyFourEL_1352851298914249]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070458 : Nat.totient 170246431310806429561636070458 = 85123215471651620869637854176 := by
  rw [← show ((([(2, 1), (463251577, 1), (183751593910716929477, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070458 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_2, prime_oneHundredFortyFourEL_463251577, prime_oneHundredFortyFourEL_183751593910716929477]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070459 : Nat.totient 170246431310806429561636070459 = 145587376409882314221873561600 := by
  rw [← show ((([(7, 1), (509, 1), (3677, 1), (12301, 1), (132178273, 1), (7992231833, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070459 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_7, prime_oneHundredFortyFourEL_509, prime_oneHundredFortyFourEL_3677, prime_oneHundredFortyFourEL_12301, prime_oneHundredFortyFourEL_132178273, prime_oneHundredFortyFourEL_7992231833]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070460 : Nat.totient 170246431310806429561636070460 = 45399048136557375812111096832 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (213150073, 1), (13311937837557174217, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070460 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_2, prime_oneHundredFortyFourEL_3, prime_oneHundredFortyFourEL_5, prime_oneHundredFortyFourEL_213150073, prime_oneHundredFortyFourEL_13311937837557174217]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070461 : Nat.totient 170246431310806429561636070461 = 154506677091079868394592435200 := by
  rw [← show ((([(11, 1), (593, 1), (90887, 1), (2009731, 1), (5281853, 1), (27052327, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070461 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_11, prime_oneHundredFortyFourEL_593, prime_oneHundredFortyFourEL_90887, prime_oneHundredFortyFourEL_2009731, prime_oneHundredFortyFourEL_5281853, prime_oneHundredFortyFourEL_27052327]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070462 : Nat.totient 170246431310806429561636070462 = 85123195292157729226278028800 := by
  rw [← show ((([(2, 1), (4185953, 1), (3063309401, 1), (6638390712727, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070462 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_2, prime_oneHundredFortyFourEL_4185953, prime_oneHundredFortyFourEL_3063309401, prime_oneHundredFortyFourEL_6638390712727]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070463 : Nat.totient 170246431310806429561636070463 = 113488892301935717252961658416 := by
  rw [← show ((([(3, 2), (13003, 1), (1454761989205964688162869, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070463 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_3, prime_oneHundredFortyFourEL_13003, prime_oneHundredFortyFourEL_1454761989205964688162869]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070464 : Nat.totient 170246431310806429561636070464 = 85075371052379441368734988800 := by
  rw [← show ((([(2, 6), (2411, 1), (7039, 1), (188911, 1), (829722028640579, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070464 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_2, prime_oneHundredFortyFourEL_2411, prime_oneHundredFortyFourEL_7039, prime_oneHundredFortyFourEL_188911, prime_oneHundredFortyFourEL_829722028640579]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070465 : Nat.totient 170246431310806429561636070465 = 136197145048228583813127594112 := by
  rw [← show ((([(5, 1), (326958004169, 1), (104139632087311397, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070465 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_5, prime_oneHundredFortyFourEL_326958004169, prime_oneHundredFortyFourEL_104139632087311397]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070466 : Nat.totient 170246431310806429561636070466 = 48641826738396050315108309280 := by
  rw [← show ((([(2, 1), (3, 1), (7, 2), (4517543, 1), (4980897683, 1), (25734798431, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070466 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_2, prime_oneHundredFortyFourEL_3, prime_oneHundredFortyFourEL_7, prime_oneHundredFortyFourEL_4517543, prime_oneHundredFortyFourEL_4980897683, prime_oneHundredFortyFourEL_25734798431]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070467 : Nat.totient 170246431310806429561636070467 = 153656632931810259230040821760 := by
  rw [← show ((([(17, 1), (29, 1), (157, 1), (2377, 1), (925341976526380756771, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070467 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_17, prime_oneHundredFortyFourEL_29, prime_oneHundredFortyFourEL_157, prime_oneHundredFortyFourEL_2377, prime_oneHundredFortyFourEL_925341976526380756771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070468 : Nat.totient 170246431310806429561636070468 = 85123210524729020391680302152 := by
  rw [← show ((([(2, 2), (16591039, 1), (2565337097194552275503, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070468 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_2, prime_oneHundredFortyFourEL_16591039, prime_oneHundredFortyFourEL_2565337097194552275503]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070469 : Nat.totient 170246431310806429561636070469 = 99233660218488395106106768896 := by
  rw [← show ((([(3, 1), (13, 2), (19, 2), (10079, 1), (10477, 1), (8808631998632509, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070469 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_3, prime_oneHundredFortyFourEL_13, prime_oneHundredFortyFourEL_19, prime_oneHundredFortyFourEL_10079, prime_oneHundredFortyFourEL_10477, prime_oneHundredFortyFourEL_8808631998632509]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070470 : Nat.totient 170246431310806429561636070470 = 66514884689401307865623393280 := by
  rw [← show ((([(2, 1), (5, 1), (43, 1), (653404021, 1), (605937399459231649, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070470 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_2, prime_oneHundredFortyFourEL_5, prime_oneHundredFortyFourEL_43, prime_oneHundredFortyFourEL_653404021, prime_oneHundredFortyFourEL_605937399459231649]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070471 : Nat.totient 170246431310806429561636070471 = 170079359130487693946980316088 := by
  rw [← show ((([(1019, 1), (1439052847, 1), (116098628676928747, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070471 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_1019, prime_oneHundredFortyFourEL_1439052847, prime_oneHundredFortyFourEL_116098628676928747]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070472 : Nat.totient 170246431310806429561636070472 = 51477183719686484517305088000 := by
  rw [← show ((([(2, 3), (3, 3), (11, 1), (461, 1), (69997, 1), (2220502305087140441, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070472 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_2, prime_oneHundredFortyFourEL_3, prime_oneHundredFortyFourEL_11, prime_oneHundredFortyFourEL_461, prime_oneHundredFortyFourEL_69997, prime_oneHundredFortyFourEL_2220502305087140441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070473 : Nat.totient 170246431310806429561636070473 = 142077658080249169505045596800 := by
  rw [← show ((([(7, 1), (47, 1), (331, 1), (457, 1), (3420880671711613886411, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070473 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_7, prime_oneHundredFortyFourEL_47, prime_oneHundredFortyFourEL_331, prime_oneHundredFortyFourEL_457, prime_oneHundredFortyFourEL_3420880671711613886411]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070474 : Nat.totient 170246431310806429561636070474 = 75613610711765051181666432000 := by
  rw [← show ((([(2, 1), (23, 1), (31, 1), (41, 1), (61, 1), (47735865348336522210649, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070474 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_2, prime_oneHundredFortyFourEL_23, prime_oneHundredFortyFourEL_31, prime_oneHundredFortyFourEL_41, prime_oneHundredFortyFourEL_61, prime_oneHundredFortyFourEL_47735865348336522210649]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070475 : Nat.totient 170246431310806429561636070475 = 90351754151359843785418272000 := by
  rw [← show ((([(3, 1), (5, 2), (211, 1), (5641, 1), (1907120781648088563523, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070475 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_3, prime_oneHundredFortyFourEL_5, prime_oneHundredFortyFourEL_211, prime_oneHundredFortyFourEL_5641, prime_oneHundredFortyFourEL_1907120781648088563523]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070476 : Nat.totient 170246431310806429561636070476 = 85123213412846527610423902160 := by
  rw [← show ((([(2, 2), (37958111, 1), (1121278343585159108429, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070476 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_2, prime_oneHundredFortyFourEL_37958111, prime_oneHundredFortyFourEL_1121278343585159108429]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070477 : Nat.totient 170246431310806429561636070477 = 170246430630465549050024233200 := by
  rw [← show ((([(261788987, 1), (5982940531, 1), (108695598541, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070477 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_261788987, prime_oneHundredFortyFourEL_5982940531, prime_oneHundredFortyFourEL_108695598541]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070478 : Nat.totient 170246431310806429561636070478 = 56748810436933028958896185656 := by
  rw [← show ((([(2, 1), (3, 1), (23642614645087, 1), (1200138209940499, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070478 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_2, prime_oneHundredFortyFourEL_3, prime_oneHundredFortyFourEL_23642614645087, prime_oneHundredFortyFourEL_1200138209940499]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070479 : Nat.totient 170246431310806429561636070479 = 170243515781026086163756035456 := by
  rw [← show ((([(58393, 1), (100607785529, 1), (28979149744607, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070479 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_58393, prime_oneHundredFortyFourEL_100607785529, prime_oneHundredFortyFourEL_28979149744607]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070480 : Nat.totient 170246431310806429561636070480 = 58367408911863199088351803392 := by
  rw [← show ((([(2, 4), (5, 1), (7, 1), (28403, 1), (79847, 1), (5816549, 1), (23046330287, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070480 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_2, prime_oneHundredFortyFourEL_5, prime_oneHundredFortyFourEL_7, prime_oneHundredFortyFourEL_28403, prime_oneHundredFortyFourEL_79847, prime_oneHundredFortyFourEL_5816549, prime_oneHundredFortyFourEL_23046330287]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070481 : Nat.totient 170246431310806429561636070481 = 111425798073747816417923700480 := by
  rw [← show ((([(3, 2), (71, 1), (239, 1), (22307, 1), (1536649, 1), (32520964175027, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070481 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_3, prime_oneHundredFortyFourEL_71, prime_oneHundredFortyFourEL_239, prime_oneHundredFortyFourEL_22307, prime_oneHundredFortyFourEL_1536649, prime_oneHundredFortyFourEL_32520964175027]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070482 : Nat.totient 170246431310806429561636070482 = 78556069126735794923989744080 := by
  rw [← show ((([(2, 1), (13, 1), (4091, 1), (1600571905597713833007127, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070482 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_2, prime_oneHundredFortyFourEL_13, prime_oneHundredFortyFourEL_4091, prime_oneHundredFortyFourEL_1600571905597713833007127]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070483 : Nat.totient 170246431310806429561636070483 = 154318059282761299547297280000 := by
  rw [← show ((([(11, 1), (601, 1), (811, 1), (67933, 1), (138799, 1), (3367618405969, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070483 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_11, prime_oneHundredFortyFourEL_601, prime_oneHundredFortyFourEL_811, prime_oneHundredFortyFourEL_67933, prime_oneHundredFortyFourEL_138799, prime_oneHundredFortyFourEL_3367618405969]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070484 : Nat.totient 170246431310806429561636070484 = 53410645021623575608586984448 := by
  rw [← show ((([(2, 2), (3, 1), (17, 1), (559319647, 1), (1492065108799822793, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070484 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_2, prime_oneHundredFortyFourEL_3, prime_oneHundredFortyFourEL_17, prime_oneHundredFortyFourEL_559319647, prime_oneHundredFortyFourEL_1492065108799822793]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070485 : Nat.totient 170246431310806429561636070485 = 131300396714095299126856581120 := by
  rw [← show ((([(5, 1), (37, 1), (109, 1), (457569029521, 1), (18451138510529, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070485 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_5, prime_oneHundredFortyFourEL_37, prime_oneHundredFortyFourEL_109, prime_oneHundredFortyFourEL_457569029521, prime_oneHundredFortyFourEL_18451138510529]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070486 : Nat.totient 170246431310806429561636070486 = 85094622015970360905578016000 := by
  rw [← show ((([(2, 1), (7877, 1), (8677, 1), (10667, 1), (116754944939301001, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070486 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_2, prime_oneHundredFortyFourEL_7877, prime_oneHundredFortyFourEL_8677, prime_oneHundredFortyFourEL_10667, prime_oneHundredFortyFourEL_116754944939301001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070487 : Nat.totient 170246431310806429561636070487 = 97283634470455920886778859072 := by
  rw [← show ((([(3, 1), (7, 1), (2398259, 1), (3380357550857605843033, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070487 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_3, prime_oneHundredFortyFourEL_7, prime_oneHundredFortyFourEL_2398259, prime_oneHundredFortyFourEL_3380357550857605843033]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070488 : Nat.totient 170246431310806429561636070488 = 80612718074011033193591742240 := by
  rw [← show ((([(2, 3), (19, 1), (2659, 1), (421226894041107731343491, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070488 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_2, prime_oneHundredFortyFourEL_19, prime_oneHundredFortyFourEL_2659, prime_oneHundredFortyFourEL_421226894041107731343491]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070489 : Nat.totient 170246431310806429561636070489 = 167774476352510756038065868800 := by
  rw [← show ((([(73, 1), (1201, 1), (1941834217042948565255393, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070489 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_73, prime_oneHundredFortyFourEL_1201, prime_oneHundredFortyFourEL_1941834217042948565255393]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070490 : Nat.totient 170246431310806429561636070490 = 45194347594773677087878717440 := by
  rw [← show ((([(2, 1), (3, 2), (5, 1), (271, 1), (1217, 1), (4440187, 1), (1291737826932829, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070490 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_2, prime_oneHundredFortyFourEL_3, prime_oneHundredFortyFourEL_5, prime_oneHundredFortyFourEL_271, prime_oneHundredFortyFourEL_1217, prime_oneHundredFortyFourEL_4440187, prime_oneHundredFortyFourEL_1291737826932829]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070491 : Nat.totient 170246431310806429561636070491 = 170246431310806429561636070490 := by
  rw [← show ((([(170246431310806429561636070491, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070491 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_170246431310806429561636070491]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070492 : Nat.totient 170246431310806429561636070492 = 84651055912368304115089305600 := by
  rw [← show ((([(2, 2), (181, 1), (45377, 1), (452722021, 1), (11446482564799, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070492 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_2, prime_oneHundredFortyFourEL_181, prime_oneHundredFortyFourEL_45377, prime_oneHundredFortyFourEL_452722021, prime_oneHundredFortyFourEL_11446482564799]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070493 : Nat.totient 170246431310806429561636070493 = 112327408628978592442217135616 := by
  rw [← show ((([(3, 1), (97, 1), (840277, 1), (696245741410278887299, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070493 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_3, prime_oneHundredFortyFourEL_97, prime_oneHundredFortyFourEL_840277, prime_oneHundredFortyFourEL_696245741410278887299]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070494 : Nat.totient 170246431310806429561636070494 = 66259884786001220276574796800 := by
  rw [← show ((([(2, 1), (7, 1), (11, 2), (953, 1), (226691, 1), (224466569, 1), (2072458123, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070494 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_2, prime_oneHundredFortyFourEL_7, prime_oneHundredFortyFourEL_11, prime_oneHundredFortyFourEL_953, prime_oneHundredFortyFourEL_226691, prime_oneHundredFortyFourEL_224466569, prime_oneHundredFortyFourEL_2072458123]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070495 : Nat.totient 170246431310806429561636070495 = 125720116859434436395890850560 := by
  rw [← show ((([(5, 1), (13, 1), (387161, 1), (6765081881491418082743, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070495 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_5, prime_oneHundredFortyFourEL_13, prime_oneHundredFortyFourEL_387161, prime_oneHundredFortyFourEL_6765081881491418082743]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070496 : Nat.totient 170246431310806429561636070496 = 54186119189045119868986720256 := by
  rw [← show ((([(2, 5), (3, 1), (29, 1), (113, 1), (449, 1), (1205269042013298899237, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070496 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_2, prime_oneHundredFortyFourEL_3, prime_oneHundredFortyFourEL_29, prime_oneHundredFortyFourEL_113, prime_oneHundredFortyFourEL_449, prime_oneHundredFortyFourEL_1205269042013298899237]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070497 : Nat.totient 170246431310806429561636070497 = 161672870021773012245582452400 := by
  rw [← show ((([(23, 1), (139, 1), (53251933472257250410270901, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070497 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_23, prime_oneHundredFortyFourEL_139, prime_oneHundredFortyFourEL_53251933472257250410270901]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070498 : Nat.totient 170246431310806429561636070498 = 85123215655401658752786634560 := by
  rw [← show ((([(2, 1), (56777166273769, 1), (1499250865126921, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070498 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_2, prime_oneHundredFortyFourEL_56777166273769, prime_oneHundredFortyFourEL_1499250865126921]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070499 : Nat.totient 170246431310806429561636070499 = 112121745850945265256557051904 := by
  rw [← show ((([(3, 3), (83, 1), (13627, 1), (560969, 1), (21727217, 1), (457396609, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070499 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_3, prime_oneHundredFortyFourEL_83, prime_oneHundredFortyFourEL_13627, prime_oneHundredFortyFourEL_560969, prime_oneHundredFortyFourEL_21727217, prime_oneHundredFortyFourEL_457396609]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070500 : Nat.totient 170246431310806429561636070500 = 68089689622579167930361241600 := by
  rw [← show ((([(2, 2), (5, 3), (10337, 1), (29669, 1), (1110223939932987497, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070500 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_2, prime_oneHundredFortyFourEL_5, prime_oneHundredFortyFourEL_10337, prime_oneHundredFortyFourEL_29669, prime_oneHundredFortyFourEL_1110223939932987497]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFortyFourEL_170246431310806429561636070501 : Nat.totient 170246431310806429561636070501 = 136058091967232091982974045696 := by
  rw [← show ((([(7, 1), (17, 1), (107, 1), (13370488597408814070653897, 1)] : List FactorBlock).map factorBlockValue).prod) = 170246431310806429561636070501 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFortyFourEL_7, prime_oneHundredFortyFourEL_17, prime_oneHundredFortyFourEL_107, prime_oneHundredFortyFourEL_13370488597408814070653897]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64OneHundredFortyFourEL : certifiedKill 1 170246431310806429561636070399 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_oneHundredFortyFourEL_170246431310806429561636070400, phi_oneHundredFortyFourEL_170246431310806429561636070401, phi_oneHundredFortyFourEL_170246431310806429561636070402,
    phi_oneHundredFortyFourEL_170246431310806429561636070403, phi_oneHundredFortyFourEL_170246431310806429561636070404, phi_oneHundredFortyFourEL_170246431310806429561636070405,
    phi_oneHundredFortyFourEL_170246431310806429561636070406, phi_oneHundredFortyFourEL_170246431310806429561636070407, phi_oneHundredFortyFourEL_170246431310806429561636070408,
    phi_oneHundredFortyFourEL_170246431310806429561636070409, phi_oneHundredFortyFourEL_170246431310806429561636070410, phi_oneHundredFortyFourEL_170246431310806429561636070411,
    phi_oneHundredFortyFourEL_170246431310806429561636070412, phi_oneHundredFortyFourEL_170246431310806429561636070413, phi_oneHundredFortyFourEL_170246431310806429561636070414,
    phi_oneHundredFortyFourEL_170246431310806429561636070415, phi_oneHundredFortyFourEL_170246431310806429561636070416, phi_oneHundredFortyFourEL_170246431310806429561636070417,
    phi_oneHundredFortyFourEL_170246431310806429561636070418, phi_oneHundredFortyFourEL_170246431310806429561636070419, phi_oneHundredFortyFourEL_170246431310806429561636070420,
    phi_oneHundredFortyFourEL_170246431310806429561636070421, phi_oneHundredFortyFourEL_170246431310806429561636070422, phi_oneHundredFortyFourEL_170246431310806429561636070423,
    phi_oneHundredFortyFourEL_170246431310806429561636070424, phi_oneHundredFortyFourEL_170246431310806429561636070425, phi_oneHundredFortyFourEL_170246431310806429561636070426,
    phi_oneHundredFortyFourEL_170246431310806429561636070427, phi_oneHundredFortyFourEL_170246431310806429561636070428, phi_oneHundredFortyFourEL_170246431310806429561636070429,
    phi_oneHundredFortyFourEL_170246431310806429561636070430, phi_oneHundredFortyFourEL_170246431310806429561636070431, phi_oneHundredFortyFourEL_170246431310806429561636070432,
    phi_oneHundredFortyFourEL_170246431310806429561636070433, phi_oneHundredFortyFourEL_170246431310806429561636070434, phi_oneHundredFortyFourEL_170246431310806429561636070435,
    phi_oneHundredFortyFourEL_170246431310806429561636070436, phi_oneHundredFortyFourEL_170246431310806429561636070437, phi_oneHundredFortyFourEL_170246431310806429561636070438,
    phi_oneHundredFortyFourEL_170246431310806429561636070439, phi_oneHundredFortyFourEL_170246431310806429561636070440, phi_oneHundredFortyFourEL_170246431310806429561636070441,
    phi_oneHundredFortyFourEL_170246431310806429561636070442, phi_oneHundredFortyFourEL_170246431310806429561636070443, phi_oneHundredFortyFourEL_170246431310806429561636070444,
    phi_oneHundredFortyFourEL_170246431310806429561636070445, phi_oneHundredFortyFourEL_170246431310806429561636070446, phi_oneHundredFortyFourEL_170246431310806429561636070447,
    phi_oneHundredFortyFourEL_170246431310806429561636070448, phi_oneHundredFortyFourEL_170246431310806429561636070449, phi_oneHundredFortyFourEL_170246431310806429561636070450,
    phi_oneHundredFortyFourEL_170246431310806429561636070451, phi_oneHundredFortyFourEL_170246431310806429561636070452, phi_oneHundredFortyFourEL_170246431310806429561636070453,
    phi_oneHundredFortyFourEL_170246431310806429561636070454, phi_oneHundredFortyFourEL_170246431310806429561636070455, phi_oneHundredFortyFourEL_170246431310806429561636070456,
    phi_oneHundredFortyFourEL_170246431310806429561636070457, phi_oneHundredFortyFourEL_170246431310806429561636070458, phi_oneHundredFortyFourEL_170246431310806429561636070459,
    phi_oneHundredFortyFourEL_170246431310806429561636070460, phi_oneHundredFortyFourEL_170246431310806429561636070461, phi_oneHundredFortyFourEL_170246431310806429561636070462,
    phi_oneHundredFortyFourEL_170246431310806429561636070463, phi_oneHundredFortyFourEL_170246431310806429561636070464, phi_oneHundredFortyFourEL_170246431310806429561636070465,
    phi_oneHundredFortyFourEL_170246431310806429561636070466, phi_oneHundredFortyFourEL_170246431310806429561636070467, phi_oneHundredFortyFourEL_170246431310806429561636070468,
    phi_oneHundredFortyFourEL_170246431310806429561636070469, phi_oneHundredFortyFourEL_170246431310806429561636070470, phi_oneHundredFortyFourEL_170246431310806429561636070471,
    phi_oneHundredFortyFourEL_170246431310806429561636070472, phi_oneHundredFortyFourEL_170246431310806429561636070473, phi_oneHundredFortyFourEL_170246431310806429561636070474,
    phi_oneHundredFortyFourEL_170246431310806429561636070475, phi_oneHundredFortyFourEL_170246431310806429561636070476, phi_oneHundredFortyFourEL_170246431310806429561636070477,
    phi_oneHundredFortyFourEL_170246431310806429561636070478, phi_oneHundredFortyFourEL_170246431310806429561636070479, phi_oneHundredFortyFourEL_170246431310806429561636070480,
    phi_oneHundredFortyFourEL_170246431310806429561636070481, phi_oneHundredFortyFourEL_170246431310806429561636070482, phi_oneHundredFortyFourEL_170246431310806429561636070483,
    phi_oneHundredFortyFourEL_170246431310806429561636070484, phi_oneHundredFortyFourEL_170246431310806429561636070485, phi_oneHundredFortyFourEL_170246431310806429561636070486,
    phi_oneHundredFortyFourEL_170246431310806429561636070487, phi_oneHundredFortyFourEL_170246431310806429561636070488, phi_oneHundredFortyFourEL_170246431310806429561636070489,
    phi_oneHundredFortyFourEL_170246431310806429561636070490, phi_oneHundredFortyFourEL_170246431310806429561636070491, phi_oneHundredFortyFourEL_170246431310806429561636070492,
    phi_oneHundredFortyFourEL_170246431310806429561636070493, phi_oneHundredFortyFourEL_170246431310806429561636070494, phi_oneHundredFortyFourEL_170246431310806429561636070495,
    phi_oneHundredFortyFourEL_170246431310806429561636070496, phi_oneHundredFortyFourEL_170246431310806429561636070497, phi_oneHundredFortyFourEL_170246431310806429561636070498,
    phi_oneHundredFortyFourEL_170246431310806429561636070499, phi_oneHundredFortyFourEL_170246431310806429561636070500, phi_oneHundredFortyFourEL_170246431310806429561636070501]

end TotientTailPeriodKiller
end Erdos249257
