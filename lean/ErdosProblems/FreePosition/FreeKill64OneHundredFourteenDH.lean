import Erdos249257.DiagonalPincerCertificatesT64

/- Kernel-checked off-diagonal certificate at a freely chosen position. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def oneHundredFourteenDHFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem oneHundredFourteenDHFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : oneHundredFourteenDHFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [oneHundredFourteenDHFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [oneHundredFourteenDHFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then oneHundredFourteenDHFastPow a n * oneHundredFourteenDHFastPow a n * a else oneHundredFourteenDHFastPow a n * oneHundredFourteenDHFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_oneHundredFourteenDH_2 : Nat.Prime 2 := by norm_num

private theorem prime_oneHundredFourteenDH_3 : Nat.Prime 3 := by norm_num

private theorem prime_oneHundredFourteenDH_5 : Nat.Prime 5 := by norm_num

private theorem prime_oneHundredFourteenDH_7 : Nat.Prime 7 := by norm_num

private theorem prime_oneHundredFourteenDH_11 : Nat.Prime 11 := by norm_num

private theorem prime_oneHundredFourteenDH_13 : Nat.Prime 13 := by norm_num

private theorem prime_oneHundredFourteenDH_17 : Nat.Prime 17 := by norm_num

private theorem prime_oneHundredFourteenDH_19 : Nat.Prime 19 := by norm_num

private theorem prime_oneHundredFourteenDH_23 : Nat.Prime 23 := by norm_num

private theorem prime_oneHundredFourteenDH_29 : Nat.Prime 29 := by norm_num

private theorem prime_oneHundredFourteenDH_31 : Nat.Prime 31 := by norm_num

private theorem prime_oneHundredFourteenDH_37 : Nat.Prime 37 := by norm_num

private theorem prime_oneHundredFourteenDH_41 : Nat.Prime 41 := by norm_num

private theorem prime_oneHundredFourteenDH_43 : Nat.Prime 43 := by norm_num

private theorem prime_oneHundredFourteenDH_47 : Nat.Prime 47 := by norm_num

private theorem prime_oneHundredFourteenDH_53 : Nat.Prime 53 := by norm_num

private theorem prime_oneHundredFourteenDH_59 : Nat.Prime 59 := by norm_num

private theorem prime_oneHundredFourteenDH_61 : Nat.Prime 61 := by norm_num

private theorem prime_oneHundredFourteenDH_67 : Nat.Prime 67 := by norm_num

private theorem prime_oneHundredFourteenDH_71 : Nat.Prime 71 := by norm_num

private theorem prime_oneHundredFourteenDH_73 : Nat.Prime 73 := by norm_num

private theorem prime_oneHundredFourteenDH_79 : Nat.Prime 79 := by norm_num

private theorem prime_oneHundredFourteenDH_83 : Nat.Prime 83 := by norm_num

private theorem prime_oneHundredFourteenDH_89 : Nat.Prime 89 := by norm_num

private theorem prime_oneHundredFourteenDH_97 : Nat.Prime 97 := by norm_num

private theorem prime_oneHundredFourteenDH_101 : Nat.Prime 101 := by norm_num

private theorem prime_oneHundredFourteenDH_103 : Nat.Prime 103 := by norm_num

private theorem prime_oneHundredFourteenDH_107 : Nat.Prime 107 := by norm_num

private theorem prime_oneHundredFourteenDH_109 : Nat.Prime 109 := by norm_num

private theorem prime_oneHundredFourteenDH_113 : Nat.Prime 113 := by norm_num

private theorem prime_oneHundredFourteenDH_127 : Nat.Prime 127 := by norm_num

private theorem prime_oneHundredFourteenDH_131 : Nat.Prime 131 := by norm_num

private theorem prime_oneHundredFourteenDH_137 : Nat.Prime 137 := by norm_num

private theorem prime_oneHundredFourteenDH_139 : Nat.Prime 139 := by norm_num

private theorem prime_oneHundredFourteenDH_149 : Nat.Prime 149 := by norm_num

private theorem prime_oneHundredFourteenDH_151 : Nat.Prime 151 := by norm_num

private theorem prime_oneHundredFourteenDH_157 : Nat.Prime 157 := by norm_num

private theorem prime_oneHundredFourteenDH_163 : Nat.Prime 163 := by norm_num

private theorem prime_oneHundredFourteenDH_167 : Nat.Prime 167 := by norm_num

private theorem prime_oneHundredFourteenDH_173 : Nat.Prime 173 := by norm_num

private theorem prime_oneHundredFourteenDH_181 : Nat.Prime 181 := by norm_num

private theorem prime_oneHundredFourteenDH_191 : Nat.Prime 191 := by norm_num

private theorem prime_oneHundredFourteenDH_193 : Nat.Prime 193 := by norm_num

private theorem prime_oneHundredFourteenDH_197 : Nat.Prime 197 := by norm_num

private theorem prime_oneHundredFourteenDH_199 : Nat.Prime 199 := by norm_num

private theorem prime_oneHundredFourteenDH_211 : Nat.Prime 211 := by norm_num

private theorem prime_oneHundredFourteenDH_223 : Nat.Prime 223 := by norm_num

private theorem prime_oneHundredFourteenDH_227 : Nat.Prime 227 := by norm_num

private theorem prime_oneHundredFourteenDH_229 : Nat.Prime 229 := by norm_num

private theorem prime_oneHundredFourteenDH_233 : Nat.Prime 233 := by norm_num

private theorem prime_oneHundredFourteenDH_239 : Nat.Prime 239 := by norm_num

private theorem prime_oneHundredFourteenDH_241 : Nat.Prime 241 := by norm_num

private theorem prime_oneHundredFourteenDH_251 : Nat.Prime 251 := by norm_num

private theorem prime_oneHundredFourteenDH_257 : Nat.Prime 257 := by norm_num

private theorem prime_oneHundredFourteenDH_263 : Nat.Prime 263 := by norm_num

private theorem prime_oneHundredFourteenDH_269 : Nat.Prime 269 := by norm_num

private theorem prime_oneHundredFourteenDH_271 : Nat.Prime 271 := by norm_num

private theorem prime_oneHundredFourteenDH_277 : Nat.Prime 277 := by norm_num

private theorem prime_oneHundredFourteenDH_281 : Nat.Prime 281 := by norm_num

private theorem prime_oneHundredFourteenDH_283 : Nat.Prime 283 := by norm_num

private theorem prime_oneHundredFourteenDH_307 : Nat.Prime 307 := by norm_num

private theorem prime_oneHundredFourteenDH_311 : Nat.Prime 311 := by norm_num

private theorem prime_oneHundredFourteenDH_313 : Nat.Prime 313 := by norm_num

private theorem prime_oneHundredFourteenDH_331 : Nat.Prime 331 := by norm_num

private theorem prime_oneHundredFourteenDH_337 : Nat.Prime 337 := by norm_num

private theorem prime_oneHundredFourteenDH_347 : Nat.Prime 347 := by norm_num

private theorem prime_oneHundredFourteenDH_349 : Nat.Prime 349 := by norm_num

private theorem prime_oneHundredFourteenDH_353 : Nat.Prime 353 := by norm_num

private theorem prime_oneHundredFourteenDH_359 : Nat.Prime 359 := by norm_num

private theorem prime_oneHundredFourteenDH_373 : Nat.Prime 373 := by norm_num

private theorem prime_oneHundredFourteenDH_383 : Nat.Prime 383 := by norm_num

private theorem prime_oneHundredFourteenDH_389 : Nat.Prime 389 := by norm_num

private theorem prime_oneHundredFourteenDH_397 : Nat.Prime 397 := by norm_num

private theorem prime_oneHundredFourteenDH_409 : Nat.Prime 409 := by norm_num

private theorem prime_oneHundredFourteenDH_419 : Nat.Prime 419 := by norm_num

private theorem prime_oneHundredFourteenDH_431 : Nat.Prime 431 := by norm_num

private theorem prime_oneHundredFourteenDH_449 : Nat.Prime 449 := by norm_num

private theorem prime_oneHundredFourteenDH_457 : Nat.Prime 457 := by norm_num

private theorem prime_oneHundredFourteenDH_461 : Nat.Prime 461 := by norm_num

private theorem prime_oneHundredFourteenDH_467 : Nat.Prime 467 := by norm_num

private theorem prime_oneHundredFourteenDH_479 : Nat.Prime 479 := by norm_num

private theorem prime_oneHundredFourteenDH_487 : Nat.Prime 487 := by norm_num

private theorem prime_oneHundredFourteenDH_509 : Nat.Prime 509 := by norm_num

private theorem prime_oneHundredFourteenDH_523 : Nat.Prime 523 := by norm_num

private theorem prime_oneHundredFourteenDH_541 : Nat.Prime 541 := by norm_num

private theorem prime_oneHundredFourteenDH_557 : Nat.Prime 557 := by norm_num

private theorem prime_oneHundredFourteenDH_563 : Nat.Prime 563 := by norm_num

private theorem prime_oneHundredFourteenDH_587 : Nat.Prime 587 := by norm_num

private theorem prime_oneHundredFourteenDH_593 : Nat.Prime 593 := by norm_num

private theorem prime_oneHundredFourteenDH_599 : Nat.Prime 599 := by norm_num

private theorem prime_oneHundredFourteenDH_601 : Nat.Prime 601 := by norm_num

private theorem prime_oneHundredFourteenDH_607 : Nat.Prime 607 := by norm_num

private theorem prime_oneHundredFourteenDH_617 : Nat.Prime 617 := by norm_num

private theorem prime_oneHundredFourteenDH_619 : Nat.Prime 619 := by norm_num

private theorem prime_oneHundredFourteenDH_641 : Nat.Prime 641 := by norm_num

private theorem prime_oneHundredFourteenDH_653 : Nat.Prime 653 := by norm_num

private theorem prime_oneHundredFourteenDH_659 : Nat.Prime 659 := by norm_num

private theorem prime_oneHundredFourteenDH_709 : Nat.Prime 709 := by norm_num

private theorem prime_oneHundredFourteenDH_719 : Nat.Prime 719 := by norm_num

private theorem prime_oneHundredFourteenDH_727 : Nat.Prime 727 := by norm_num

private theorem prime_oneHundredFourteenDH_733 : Nat.Prime 733 := by norm_num

private theorem prime_oneHundredFourteenDH_743 : Nat.Prime 743 := by norm_num

private theorem prime_oneHundredFourteenDH_797 : Nat.Prime 797 := by norm_num

private theorem prime_oneHundredFourteenDH_809 : Nat.Prime 809 := by norm_num

private theorem prime_oneHundredFourteenDH_811 : Nat.Prime 811 := by norm_num

private theorem prime_oneHundredFourteenDH_821 : Nat.Prime 821 := by norm_num

private theorem prime_oneHundredFourteenDH_823 : Nat.Prime 823 := by norm_num

private theorem prime_oneHundredFourteenDH_857 : Nat.Prime 857 := by norm_num

private theorem prime_oneHundredFourteenDH_859 : Nat.Prime 859 := by norm_num

private theorem prime_oneHundredFourteenDH_863 : Nat.Prime 863 := by norm_num

private theorem prime_oneHundredFourteenDH_947 : Nat.Prime 947 := by norm_num

private theorem prime_oneHundredFourteenDH_967 : Nat.Prime 967 := by norm_num

private theorem prime_oneHundredFourteenDH_971 : Nat.Prime 971 := by norm_num

private theorem prime_oneHundredFourteenDH_997 : Nat.Prime 997 := by norm_num

private theorem prime_oneHundredFourteenDH_1033 : Nat.Prime 1033 := by norm_num

private theorem prime_oneHundredFourteenDH_1061 : Nat.Prime 1061 := by norm_num

private theorem prime_oneHundredFourteenDH_1063 : Nat.Prime 1063 := by norm_num

private theorem prime_oneHundredFourteenDH_1093 : Nat.Prime 1093 := by norm_num

private theorem prime_oneHundredFourteenDH_1117 : Nat.Prime 1117 := by norm_num

private theorem prime_oneHundredFourteenDH_1123 : Nat.Prime 1123 := by norm_num

private theorem prime_oneHundredFourteenDH_1151 : Nat.Prime 1151 := by norm_num

private theorem prime_oneHundredFourteenDH_1153 : Nat.Prime 1153 := by norm_num

private theorem prime_oneHundredFourteenDH_1187 : Nat.Prime 1187 := by norm_num

private theorem prime_oneHundredFourteenDH_1193 : Nat.Prime 1193 := by norm_num

private theorem prime_oneHundredFourteenDH_1201 : Nat.Prime 1201 := by norm_num

private theorem prime_oneHundredFourteenDH_1213 : Nat.Prime 1213 := by norm_num

private theorem prime_oneHundredFourteenDH_1259 : Nat.Prime 1259 := by norm_num

private theorem prime_oneHundredFourteenDH_1279 : Nat.Prime 1279 := by norm_num

private theorem prime_oneHundredFourteenDH_1303 : Nat.Prime 1303 := by norm_num

private theorem prime_oneHundredFourteenDH_1327 : Nat.Prime 1327 := by norm_num

private theorem prime_oneHundredFourteenDH_1361 : Nat.Prime 1361 := by norm_num

private theorem prime_oneHundredFourteenDH_1429 : Nat.Prime 1429 := by norm_num

private theorem prime_oneHundredFourteenDH_1451 : Nat.Prime 1451 := by norm_num

private theorem prime_oneHundredFourteenDH_1459 : Nat.Prime 1459 := by norm_num

private theorem prime_oneHundredFourteenDH_1483 : Nat.Prime 1483 := by norm_num

private theorem prime_oneHundredFourteenDH_1489 : Nat.Prime 1489 := by norm_num

private theorem prime_oneHundredFourteenDH_1531 : Nat.Prime 1531 := by norm_num

private theorem prime_oneHundredFourteenDH_1549 : Nat.Prime 1549 := by norm_num

private theorem prime_oneHundredFourteenDH_1597 : Nat.Prime 1597 := by norm_num

private theorem prime_oneHundredFourteenDH_1723 : Nat.Prime 1723 := by norm_num

private theorem prime_oneHundredFourteenDH_1753 : Nat.Prime 1753 := by norm_num

private theorem prime_oneHundredFourteenDH_1759 : Nat.Prime 1759 := by norm_num

private theorem prime_oneHundredFourteenDH_1783 : Nat.Prime 1783 := by norm_num

private theorem prime_oneHundredFourteenDH_1787 : Nat.Prime 1787 := by norm_num

private theorem prime_oneHundredFourteenDH_1801 : Nat.Prime 1801 := by norm_num

private theorem prime_oneHundredFourteenDH_1811 : Nat.Prime 1811 := by norm_num

private theorem prime_oneHundredFourteenDH_1867 : Nat.Prime 1867 := by norm_num

private theorem prime_oneHundredFourteenDH_1901 : Nat.Prime 1901 := by norm_num

private theorem prime_oneHundredFourteenDH_2027 : Nat.Prime 2027 := by norm_num

private theorem prime_oneHundredFourteenDH_2069 : Nat.Prime 2069 := by norm_num

private theorem prime_oneHundredFourteenDH_2089 : Nat.Prime 2089 := by norm_num

private theorem prime_oneHundredFourteenDH_2203 : Nat.Prime 2203 := by norm_num

private theorem prime_oneHundredFourteenDH_2239 : Nat.Prime 2239 := by norm_num

private theorem prime_oneHundredFourteenDH_2251 : Nat.Prime 2251 := by norm_num

private theorem prime_oneHundredFourteenDH_2269 : Nat.Prime 2269 := by norm_num

private theorem prime_oneHundredFourteenDH_2293 : Nat.Prime 2293 := by norm_num

private theorem prime_oneHundredFourteenDH_2297 : Nat.Prime 2297 := by norm_num

private theorem prime_oneHundredFourteenDH_2383 : Nat.Prime 2383 := by norm_num

private theorem prime_oneHundredFourteenDH_2591 : Nat.Prime 2591 := by norm_num

private theorem prime_oneHundredFourteenDH_2609 : Nat.Prime 2609 := by norm_num

private theorem prime_oneHundredFourteenDH_2647 : Nat.Prime 2647 := by norm_num

private theorem prime_oneHundredFourteenDH_2693 : Nat.Prime 2693 := by norm_num

private theorem prime_oneHundredFourteenDH_2789 : Nat.Prime 2789 := by norm_num

private theorem prime_oneHundredFourteenDH_2819 : Nat.Prime 2819 := by norm_num

private theorem prime_oneHundredFourteenDH_3229 : Nat.Prime 3229 := by norm_num

private theorem prime_oneHundredFourteenDH_3319 : Nat.Prime 3319 := by norm_num

private theorem prime_oneHundredFourteenDH_3347 : Nat.Prime 3347 := by norm_num

private theorem prime_oneHundredFourteenDH_3449 : Nat.Prime 3449 := by norm_num

private theorem prime_oneHundredFourteenDH_3511 : Nat.Prime 3511 := by norm_num

private theorem prime_oneHundredFourteenDH_3547 : Nat.Prime 3547 := by norm_num

private theorem prime_oneHundredFourteenDH_3673 : Nat.Prime 3673 := by norm_num

private theorem prime_oneHundredFourteenDH_3691 : Nat.Prime 3691 := by norm_num

private theorem prime_oneHundredFourteenDH_3701 : Nat.Prime 3701 := by norm_num

private theorem prime_oneHundredFourteenDH_3739 : Nat.Prime 3739 := by norm_num

private theorem prime_oneHundredFourteenDH_3923 : Nat.Prime 3923 := by norm_num

private theorem prime_oneHundredFourteenDH_4157 : Nat.Prime 4157 := by norm_num

private theorem prime_oneHundredFourteenDH_4217 : Nat.Prime 4217 := by norm_num

private theorem prime_oneHundredFourteenDH_4523 : Nat.Prime 4523 := by norm_num

private theorem prime_oneHundredFourteenDH_4783 : Nat.Prime 4783 := by norm_num

private theorem prime_oneHundredFourteenDH_4789 : Nat.Prime 4789 := by norm_num

private theorem prime_oneHundredFourteenDH_4801 : Nat.Prime 4801 := by norm_num

private theorem prime_oneHundredFourteenDH_4969 : Nat.Prime 4969 := by norm_num

private theorem prime_oneHundredFourteenDH_5009 : Nat.Prime 5009 := by norm_num

private theorem prime_oneHundredFourteenDH_5059 : Nat.Prime 5059 := by norm_num

private theorem prime_oneHundredFourteenDH_5081 : Nat.Prime 5081 := by norm_num

private theorem prime_oneHundredFourteenDH_5333 : Nat.Prime 5333 := by norm_num

private theorem prime_oneHundredFourteenDH_5399 : Nat.Prime 5399 := by norm_num

private theorem prime_oneHundredFourteenDH_5563 : Nat.Prime 5563 := by norm_num

private theorem prime_oneHundredFourteenDH_5857 : Nat.Prime 5857 := by norm_num

private theorem prime_oneHundredFourteenDH_5903 : Nat.Prime 5903 := by norm_num

private theorem prime_oneHundredFourteenDH_6299 : Nat.Prime 6299 := by norm_num

private theorem prime_oneHundredFourteenDH_6329 : Nat.Prime 6329 := by norm_num

private theorem prime_oneHundredFourteenDH_6793 : Nat.Prime 6793 := by norm_num

private theorem prime_oneHundredFourteenDH_6863 : Nat.Prime 6863 := by norm_num

private theorem prime_oneHundredFourteenDH_6959 : Nat.Prime 6959 := by norm_num

private theorem prime_oneHundredFourteenDH_7489 : Nat.Prime 7489 := by norm_num

private theorem prime_oneHundredFourteenDH_7817 : Nat.Prime 7817 := by norm_num

private theorem prime_oneHundredFourteenDH_8273 : Nat.Prime 8273 := by norm_num

private theorem prime_oneHundredFourteenDH_8779 : Nat.Prime 8779 := by norm_num

private theorem prime_oneHundredFourteenDH_9041 : Nat.Prime 9041 := by norm_num

private theorem prime_oneHundredFourteenDH_9091 : Nat.Prime 9091 := by norm_num

private theorem prime_oneHundredFourteenDH_9463 : Nat.Prime 9463 := by norm_num

private theorem prime_oneHundredFourteenDH_9887 : Nat.Prime 9887 := by norm_num

private theorem prime_oneHundredFourteenDH_10789 : Nat.Prime 10789 := by norm_num

private theorem prime_oneHundredFourteenDH_11113 : Nat.Prime 11113 := by norm_num

private theorem prime_oneHundredFourteenDH_11437 : Nat.Prime 11437 := by norm_num

private theorem prime_oneHundredFourteenDH_11491 : Nat.Prime 11491 := by norm_num

private theorem prime_oneHundredFourteenDH_11689 : Nat.Prime 11689 := by norm_num

private theorem prime_oneHundredFourteenDH_11777 : Nat.Prime 11777 := by norm_num

private theorem prime_oneHundredFourteenDH_11789 : Nat.Prime 11789 := by norm_num

private theorem prime_oneHundredFourteenDH_11971 : Nat.Prime 11971 := by norm_num

private theorem prime_oneHundredFourteenDH_12479 : Nat.Prime 12479 := by norm_num

private theorem prime_oneHundredFourteenDH_12941 : Nat.Prime 12941 := by norm_num

private theorem prime_oneHundredFourteenDH_13037 : Nat.Prime 13037 := by norm_num

private theorem prime_oneHundredFourteenDH_14251 : Nat.Prime 14251 := by norm_num

private theorem prime_oneHundredFourteenDH_14503 : Nat.Prime 14503 := by norm_num

private theorem prime_oneHundredFourteenDH_14699 : Nat.Prime 14699 := by norm_num

private theorem prime_oneHundredFourteenDH_15313 : Nat.Prime 15313 := by norm_num

private theorem prime_oneHundredFourteenDH_15391 : Nat.Prime 15391 := by norm_num

private theorem prime_oneHundredFourteenDH_15461 : Nat.Prime 15461 := by norm_num

private theorem prime_oneHundredFourteenDH_15467 : Nat.Prime 15467 := by norm_num

private theorem prime_oneHundredFourteenDH_16007 : Nat.Prime 16007 := by norm_num

private theorem prime_oneHundredFourteenDH_16661 : Nat.Prime 16661 := by norm_num

private theorem prime_oneHundredFourteenDH_16879 : Nat.Prime 16879 := by norm_num

private theorem prime_oneHundredFourteenDH_17093 : Nat.Prime 17093 := by norm_num

private theorem prime_oneHundredFourteenDH_17183 : Nat.Prime 17183 := by norm_num

private theorem prime_oneHundredFourteenDH_17203 : Nat.Prime 17203 := by norm_num

private theorem prime_oneHundredFourteenDH_18043 : Nat.Prime 18043 := by norm_num

private theorem prime_oneHundredFourteenDH_18049 : Nat.Prime 18049 := by norm_num

private theorem prime_oneHundredFourteenDH_18059 : Nat.Prime 18059 := by norm_num

private theorem prime_oneHundredFourteenDH_19403 : Nat.Prime 19403 := by norm_num

private theorem prime_oneHundredFourteenDH_19697 : Nat.Prime 19697 := by norm_num

private theorem prime_oneHundredFourteenDH_20639 : Nat.Prime 20639 := by norm_num

private theorem prime_oneHundredFourteenDH_20753 : Nat.Prime 20753 := by norm_num

private theorem prime_oneHundredFourteenDH_20983 : Nat.Prime 20983 := by norm_num

private theorem prime_oneHundredFourteenDH_21227 : Nat.Prime 21227 := by norm_num

private theorem prime_oneHundredFourteenDH_21283 : Nat.Prime 21283 := by norm_num

private theorem prime_oneHundredFourteenDH_21617 : Nat.Prime 21617 := by norm_num

private theorem prime_oneHundredFourteenDH_22397 : Nat.Prime 22397 := by norm_num

private theorem prime_oneHundredFourteenDH_25117 : Nat.Prime 25117 := by norm_num

private theorem prime_oneHundredFourteenDH_26407 : Nat.Prime 26407 := by norm_num

private theorem prime_oneHundredFourteenDH_31177 : Nat.Prime 31177 := by norm_num

private theorem prime_oneHundredFourteenDH_32251 : Nat.Prime 32251 := by norm_num

private theorem prime_oneHundredFourteenDH_32353 : Nat.Prime 32353 := by norm_num

private theorem prime_oneHundredFourteenDH_32603 : Nat.Prime 32603 := by norm_num

private theorem prime_oneHundredFourteenDH_34351 : Nat.Prime 34351 := by norm_num

private theorem prime_oneHundredFourteenDH_35527 : Nat.Prime 35527 := by norm_num

private theorem prime_oneHundredFourteenDH_36793 : Nat.Prime 36793 := by norm_num

private theorem prime_oneHundredFourteenDH_38317 : Nat.Prime 38317 := by norm_num

private theorem prime_oneHundredFourteenDH_38351 : Nat.Prime 38351 := by norm_num

private theorem prime_oneHundredFourteenDH_40277 : Nat.Prime 40277 := by norm_num

private theorem prime_oneHundredFourteenDH_40771 : Nat.Prime 40771 := by norm_num

private theorem prime_oneHundredFourteenDH_42473 : Nat.Prime 42473 := by norm_num

private theorem prime_oneHundredFourteenDH_44129 : Nat.Prime 44129 := by norm_num

private theorem prime_oneHundredFourteenDH_44507 : Nat.Prime 44507 := by norm_num

private theorem prime_oneHundredFourteenDH_44753 : Nat.Prime 44753 := by norm_num

private theorem prime_oneHundredFourteenDH_45503 : Nat.Prime 45503 := by norm_num

private theorem prime_oneHundredFourteenDH_46681 : Nat.Prime 46681 := by norm_num

private theorem prime_oneHundredFourteenDH_46687 : Nat.Prime 46687 := by norm_num

private theorem prime_oneHundredFourteenDH_47653 : Nat.Prime 47653 := by norm_num

private theorem prime_oneHundredFourteenDH_47713 : Nat.Prime 47713 := by norm_num

private theorem prime_oneHundredFourteenDH_47881 : Nat.Prime 47881 := by norm_num

private theorem prime_oneHundredFourteenDH_48017 : Nat.Prime 48017 := by norm_num

private theorem prime_oneHundredFourteenDH_49529 : Nat.Prime 49529 := by norm_num

private theorem prime_oneHundredFourteenDH_51283 : Nat.Prime 51283 := by norm_num

private theorem prime_oneHundredFourteenDH_52127 : Nat.Prime 52127 := by norm_num

private theorem prime_oneHundredFourteenDH_52147 : Nat.Prime 52147 := by norm_num

private theorem prime_oneHundredFourteenDH_53003 : Nat.Prime 53003 := by norm_num

private theorem prime_oneHundredFourteenDH_54833 : Nat.Prime 54833 := by norm_num

private theorem prime_oneHundredFourteenDH_59693 : Nat.Prime 59693 := by norm_num

private theorem prime_oneHundredFourteenDH_60457 : Nat.Prime 60457 := by norm_num

private theorem prime_oneHundredFourteenDH_60589 : Nat.Prime 60589 := by norm_num

private theorem prime_oneHundredFourteenDH_60821 : Nat.Prime 60821 := by norm_num

private theorem prime_oneHundredFourteenDH_62047 : Nat.Prime 62047 := by norm_num

private theorem prime_oneHundredFourteenDH_62081 : Nat.Prime 62081 := by norm_num

private theorem prime_oneHundredFourteenDH_69997 : Nat.Prime 69997 := by norm_num

private theorem prime_oneHundredFourteenDH_70199 : Nat.Prime 70199 := by norm_num

private theorem prime_oneHundredFourteenDH_71039 : Nat.Prime 71039 := by norm_num

private theorem prime_oneHundredFourteenDH_72077 : Nat.Prime 72077 := by norm_num

private theorem prime_oneHundredFourteenDH_74197 : Nat.Prime 74197 := by norm_num

private theorem prime_oneHundredFourteenDH_76511 : Nat.Prime 76511 := by norm_num

private theorem prime_oneHundredFourteenDH_78691 : Nat.Prime 78691 := by norm_num

private theorem prime_oneHundredFourteenDH_83873 : Nat.Prime 83873 := by norm_num

private theorem prime_oneHundredFourteenDH_96589 : Nat.Prime 96589 := by norm_num

private theorem prime_oneHundredFourteenDH_98323 : Nat.Prime 98323 := by norm_num

private theorem prime_oneHundredFourteenDH_100511 : Nat.Prime 100511 := by norm_num

private theorem prime_oneHundredFourteenDH_108799 : Nat.Prime 108799 := by norm_num

private theorem prime_oneHundredFourteenDH_108803 : Nat.Prime 108803 := by norm_num

private theorem prime_oneHundredFourteenDH_116131 : Nat.Prime 116131 := by norm_num

private theorem prime_oneHundredFourteenDH_118457 : Nat.Prime 118457 := by norm_num

private theorem prime_oneHundredFourteenDH_125287 : Nat.Prime 125287 := by norm_num

private theorem prime_oneHundredFourteenDH_125471 : Nat.Prime 125471 := by norm_num

private theorem prime_oneHundredFourteenDH_136709 : Nat.Prime 136709 := by norm_num

private theorem prime_oneHundredFourteenDH_137737 : Nat.Prime 137737 := by norm_num

private theorem prime_oneHundredFourteenDH_137999 : Nat.Prime 137999 := by norm_num

private theorem prime_oneHundredFourteenDH_143141 : Nat.Prime 143141 := by norm_num

private theorem prime_oneHundredFourteenDH_147457 : Nat.Prime 147457 := by norm_num

private theorem prime_oneHundredFourteenDH_151903 : Nat.Prime 151903 := by norm_num

private theorem prime_oneHundredFourteenDH_155723 : Nat.Prime 155723 := by norm_num

private theorem prime_oneHundredFourteenDH_156419 : Nat.Prime 156419 := by norm_num

private theorem prime_oneHundredFourteenDH_156593 : Nat.Prime 156593 := by norm_num

private theorem prime_oneHundredFourteenDH_159683 : Nat.Prime 159683 := by norm_num

private theorem prime_oneHundredFourteenDH_160883 : Nat.Prime 160883 := by norm_num

private theorem prime_oneHundredFourteenDH_161561 : Nat.Prime 161561 := by norm_num

private theorem prime_oneHundredFourteenDH_162251 : Nat.Prime 162251 := by norm_num

private theorem prime_oneHundredFourteenDH_171401 : Nat.Prime 171401 := by norm_num

private theorem prime_oneHundredFourteenDH_181787 : Nat.Prime 181787 := by norm_num

private theorem prime_oneHundredFourteenDH_201451 : Nat.Prime 201451 := by norm_num

private theorem prime_oneHundredFourteenDH_201823 : Nat.Prime 201823 := by norm_num

private theorem prime_oneHundredFourteenDH_208309 : Nat.Prime 208309 := by norm_num

private theorem prime_oneHundredFourteenDH_248543 : Nat.Prime 248543 := by norm_num

private theorem prime_oneHundredFourteenDH_271367 : Nat.Prime 271367 := by norm_num

private theorem prime_oneHundredFourteenDH_274199 : Nat.Prime 274199 := by norm_num

private theorem prime_oneHundredFourteenDH_283277 : Nat.Prime 283277 := by norm_num

private theorem prime_oneHundredFourteenDH_284587 : Nat.Prime 284587 := by norm_num

private theorem prime_oneHundredFourteenDH_299281 : Nat.Prime 299281 := by norm_num

private theorem prime_oneHundredFourteenDH_327343 : Nat.Prime 327343 := by norm_num

private theorem prime_oneHundredFourteenDH_341461 : Nat.Prime 341461 := by norm_num

private theorem prime_oneHundredFourteenDH_345769 : Nat.Prime 345769 := by norm_num

private theorem prime_oneHundredFourteenDH_352333 : Nat.Prime 352333 := by norm_num

private theorem prime_oneHundredFourteenDH_364691 : Nat.Prime 364691 := by norm_num

private theorem prime_oneHundredFourteenDH_378011 : Nat.Prime 378011 := by norm_num

private theorem prime_oneHundredFourteenDH_379451 : Nat.Prime 379451 := by norm_num

private theorem prime_oneHundredFourteenDH_390989 : Nat.Prime 390989 := by norm_num

private theorem prime_oneHundredFourteenDH_425653 : Nat.Prime 425653 := by norm_num

private theorem prime_oneHundredFourteenDH_435181 : Nat.Prime 435181 := by norm_num

private theorem prime_oneHundredFourteenDH_447197 : Nat.Prime 447197 := by norm_num

private theorem prime_oneHundredFourteenDH_470501 : Nat.Prime 470501 := by norm_num

private theorem prime_oneHundredFourteenDH_507109 : Nat.Prime 507109 := by norm_num

private theorem prime_oneHundredFourteenDH_509569 : Nat.Prime 509569 := by norm_num

private theorem prime_oneHundredFourteenDH_510199 : Nat.Prime 510199 := by norm_num

private theorem prime_oneHundredFourteenDH_519119 : Nat.Prime 519119 := by norm_num

private theorem prime_oneHundredFourteenDH_534253 : Nat.Prime 534253 := by norm_num

private theorem prime_oneHundredFourteenDH_553277 : Nat.Prime 553277 := by norm_num

private theorem prime_oneHundredFourteenDH_554969 : Nat.Prime 554969 := by norm_num

private theorem prime_oneHundredFourteenDH_573197 : Nat.Prime 573197 := by norm_num

private theorem prime_oneHundredFourteenDH_593519 : Nat.Prime 593519 := by norm_num

private theorem prime_oneHundredFourteenDH_594119 : Nat.Prime 594119 := by norm_num

private theorem prime_oneHundredFourteenDH_662111 : Nat.Prime 662111 := by norm_num

private theorem prime_oneHundredFourteenDH_670693 : Nat.Prime 670693 := by norm_num

private theorem prime_oneHundredFourteenDH_688013 : Nat.Prime 688013 := by norm_num

private theorem prime_oneHundredFourteenDH_693661 : Nat.Prime 693661 := by norm_num

private theorem prime_oneHundredFourteenDH_718841 : Nat.Prime 718841 := by norm_num

private theorem prime_oneHundredFourteenDH_738197 : Nat.Prime 738197 := by norm_num

private theorem prime_oneHundredFourteenDH_782123 : Nat.Prime 782123 := by norm_num

private theorem prime_oneHundredFourteenDH_814327 : Nat.Prime 814327 := by norm_num

private theorem prime_oneHundredFourteenDH_826153 : Nat.Prime 826153 := by norm_num

private theorem prime_oneHundredFourteenDH_827581 : Nat.Prime 827581 := by norm_num

private theorem prime_oneHundredFourteenDH_837667 : Nat.Prime 837667 := by norm_num

private theorem prime_oneHundredFourteenDH_852437 : Nat.Prime 852437 := by norm_num

private theorem prime_oneHundredFourteenDH_911321 : Nat.Prime 911321 := by norm_num

private theorem prime_oneHundredFourteenDH_918389 : Nat.Prime 918389 := by norm_num

private theorem prime_oneHundredFourteenDH_942247 : Nat.Prime 942247 := by norm_num

private theorem prime_oneHundredFourteenDH_984911 : Nat.Prime 984911 := by norm_num

private theorem prime_oneHundredFourteenDH_1030817 : Nat.Prime 1030817 := by norm_num

private theorem prime_oneHundredFourteenDH_1152857 : Nat.Prime 1152857 := by norm_num

private theorem prime_oneHundredFourteenDH_1201183 : Nat.Prime 1201183 := by norm_num

private theorem prime_oneHundredFourteenDH_1248553 : Nat.Prime 1248553 := by norm_num

private theorem prime_oneHundredFourteenDH_1260223 : Nat.Prime 1260223 := by norm_num

private theorem prime_oneHundredFourteenDH_1281773 : Nat.Prime 1281773 := by norm_num

private theorem prime_oneHundredFourteenDH_1293367 : Nat.Prime 1293367 := by norm_num

private theorem prime_oneHundredFourteenDH_1363847 : Nat.Prime 1363847 := by norm_num

private theorem prime_oneHundredFourteenDH_1391587 : Nat.Prime 1391587 := by norm_num

private theorem prime_oneHundredFourteenDH_1418513 : Nat.Prime 1418513 := by norm_num

private theorem prime_oneHundredFourteenDH_1471751 : Nat.Prime 1471751 := by norm_num

private theorem prime_oneHundredFourteenDH_1496927 : Nat.Prime 1496927 := by norm_num

private theorem prime_oneHundredFourteenDH_1608583 : Nat.Prime 1608583 := by norm_num

private theorem prime_oneHundredFourteenDH_1630933 : Nat.Prime 1630933 := by norm_num

private theorem prime_oneHundredFourteenDH_1681423 : Nat.Prime 1681423 := by norm_num

private theorem prime_oneHundredFourteenDH_1703297 : Nat.Prime 1703297 := by norm_num

private theorem prime_oneHundredFourteenDH_1805603 : Nat.Prime 1805603 := by norm_num

private theorem prime_oneHundredFourteenDH_2068607 : Nat.Prime 2068607 := by norm_num

private theorem prime_oneHundredFourteenDH_2155171 : Nat.Prime 2155171 := by norm_num

private theorem prime_oneHundredFourteenDH_2275657 : Nat.Prime 2275657 := by norm_num

private theorem prime_oneHundredFourteenDH_2527477 : Nat.Prime 2527477 := by norm_num

private theorem prime_oneHundredFourteenDH_2692093 : Nat.Prime 2692093 := by norm_num

private theorem prime_oneHundredFourteenDH_2794607 : Nat.Prime 2794607 := by norm_num

private theorem prime_oneHundredFourteenDH_2856551 : Nat.Prime 2856551 := by norm_num

private theorem prime_oneHundredFourteenDH_2857949 : Nat.Prime 2857949 := by norm_num

private theorem prime_oneHundredFourteenDH_2904623 : Nat.Prime 2904623 := by norm_num

private theorem prime_oneHundredFourteenDH_3026587 : Nat.Prime 3026587 := by norm_num

private theorem prime_oneHundredFourteenDH_3216511 : Nat.Prime 3216511 := by norm_num

private theorem prime_oneHundredFourteenDH_3282203 : Nat.Prime 3282203 := by norm_num

private theorem prime_oneHundredFourteenDH_3361741 : Nat.Prime 3361741 := by norm_num

private theorem prime_oneHundredFourteenDH_3557867 : Nat.Prime 3557867 := by norm_num

private theorem prime_oneHundredFourteenDH_3744023 : Nat.Prime 3744023 := by norm_num

private theorem prime_oneHundredFourteenDH_3824993 : Nat.Prime 3824993 := by norm_num

private theorem prime_oneHundredFourteenDH_4046719 : Nat.Prime 4046719 := by norm_num

private theorem prime_oneHundredFourteenDH_4241059 : Nat.Prime 4241059 := by norm_num

private theorem prime_oneHundredFourteenDH_4773203 : Nat.Prime 4773203 := by norm_num

private theorem prime_oneHundredFourteenDH_5529047 : Nat.Prime 5529047 := by norm_num

private theorem prime_oneHundredFourteenDH_5677187 : Nat.Prime 5677187 := by norm_num

private theorem prime_oneHundredFourteenDH_5699467 : Nat.Prime 5699467 := by norm_num

private theorem prime_oneHundredFourteenDH_5712059 : Nat.Prime 5712059 := by norm_num

private theorem prime_oneHundredFourteenDH_5743987 : Nat.Prime 5743987 := by norm_num

private theorem prime_oneHundredFourteenDH_5891813 : Nat.Prime 5891813 := by norm_num

private theorem prime_oneHundredFourteenDH_6252769 : Nat.Prime 6252769 := by norm_num

private theorem prime_oneHundredFourteenDH_6336347 : Nat.Prime 6336347 := by norm_num

private theorem prime_oneHundredFourteenDH_6860341 : Nat.Prime 6860341 := by norm_num

private theorem prime_oneHundredFourteenDH_6977483 : Nat.Prime 6977483 := by norm_num

private theorem prime_oneHundredFourteenDH_7361503 : Nat.Prime 7361503 := by norm_num

private theorem prime_oneHundredFourteenDH_7449241 : Nat.Prime 7449241 := by norm_num

private theorem prime_oneHundredFourteenDH_7506601 : Nat.Prime 7506601 := by norm_num

private theorem prime_oneHundredFourteenDH_7736101 : Nat.Prime 7736101 := by norm_num

private theorem prime_oneHundredFourteenDH_7825591 : Nat.Prime 7825591 := by norm_num

private theorem prime_oneHundredFourteenDH_7934737 : Nat.Prime 7934737 := by norm_num

private theorem prime_oneHundredFourteenDH_7968133 : Nat.Prime 7968133 := by norm_num

private theorem prime_oneHundredFourteenDH_8046989 : Nat.Prime 8046989 := by norm_num

private theorem prime_oneHundredFourteenDH_8584327 : Nat.Prime 8584327 := by norm_num

private theorem prime_oneHundredFourteenDH_9130651 : Nat.Prime 9130651 := by norm_num

private theorem prime_oneHundredFourteenDH_9332513 : Nat.Prime 9332513 := by norm_num

private theorem prime_oneHundredFourteenDH_9362069 : Nat.Prime 9362069 := by norm_num

private theorem prime_oneHundredFourteenDH_9579811 : Nat.Prime 9579811 := by norm_num

private theorem prime_oneHundredFourteenDH_10012193 : Nat.Prime 10012193 := by norm_num

private theorem prime_oneHundredFourteenDH_10034159 : Nat.Prime 10034159 := by norm_num

private theorem prime_oneHundredFourteenDH_10233161 : Nat.Prime 10233161 := by norm_num

private theorem prime_oneHundredFourteenDH_10247747 : Nat.Prime 10247747 := by norm_num

private theorem prime_oneHundredFourteenDH_10820141 : Nat.Prime 10820141 := by norm_num

private theorem prime_oneHundredFourteenDH_11896289 : Nat.Prime 11896289 := by norm_num

private theorem prime_oneHundredFourteenDH_12114797 : Nat.Prime 12114797 := by norm_num

private theorem prime_oneHundredFourteenDH_12193697 : Nat.Prime 12193697 := by norm_num

private theorem prime_oneHundredFourteenDH_12300311 : Nat.Prime 12300311 := by norm_num

private theorem prime_oneHundredFourteenDH_12603781 : Nat.Prime 12603781 := by norm_num

private theorem prime_oneHundredFourteenDH_12975191 : Nat.Prime 12975191 := by norm_num

private theorem prime_oneHundredFourteenDH_15229441 : Nat.Prime 15229441 := by norm_num

private theorem prime_oneHundredFourteenDH_16123559 : Nat.Prime 16123559 := by norm_num

private theorem prime_oneHundredFourteenDH_16420819 : Nat.Prime 16420819 := by norm_num

private theorem prime_oneHundredFourteenDH_16762453 : Nat.Prime 16762453 := by norm_num

private theorem prime_oneHundredFourteenDH_16885513 : Nat.Prime 16885513 := by norm_num

private theorem prime_oneHundredFourteenDH_17002049 : Nat.Prime 17002049 := by norm_num

private theorem prime_oneHundredFourteenDH_18723751 : Nat.Prime 18723751 := by norm_num

private theorem prime_oneHundredFourteenDH_20637977 : Nat.Prime 20637977 := by norm_num

private theorem prime_oneHundredFourteenDH_20951347 : Nat.Prime 20951347 := by norm_num

private theorem prime_oneHundredFourteenDH_26109053 : Nat.Prime 26109053 := by norm_num

private theorem prime_oneHundredFourteenDH_28581281 : Nat.Prime 28581281 := by norm_num

private theorem prime_oneHundredFourteenDH_28901293 : Nat.Prime 28901293 := by norm_num

private theorem prime_oneHundredFourteenDH_33287209 : Nat.Prime 33287209 := by
  apply lucas_primality 33287209 (11 : ZMod 33287209)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (67, 1), (127, 1), (163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (67, 1), (127, 1), (163, 1)] : List FactorBlock).map factorBlockValue).prod) = 33287209 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_67
      · exact prime_oneHundredFourteenDH_127
      · exact prime_oneHundredFourteenDH_163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 33287209) ^ 16643604 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (11 : ZMod 33287209) ^ 11095736 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (11 : ZMod 33287209) ^ 496824 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (11 : ZMod 33287209) ^ 262104 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (11 : ZMod 33287209) ^ 204216 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_33395759 : Nat.Prime 33395759 := by
  apply lucas_primality 33395759 (11 : ZMod 33395759)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 2), (137999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 2), (137999, 1)] : List FactorBlock).map factorBlockValue).prod) = 33395759 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_11
      · exact prime_oneHundredFourteenDH_137999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 33395759) ^ 16697879 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (11 : ZMod 33395759) ^ 3035978 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (11 : ZMod 33395759) ^ 242 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_33445129 : Nat.Prime 33445129 := by
  apply lucas_primality 33445129 (19 : ZMod 33445129)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (23, 1), (60589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (23, 1), (60589, 1)] : List FactorBlock).map factorBlockValue).prod) = 33445129 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_23
      · exact prime_oneHundredFourteenDH_60589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 33445129) ^ 16722564 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (19 : ZMod 33445129) ^ 11148376 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (19 : ZMod 33445129) ^ 1454136 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (19 : ZMod 33445129) ^ 552 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_33617411 : Nat.Prime 33617411 := by
  apply lucas_primality 33617411 (2 : ZMod 33617411)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (3361741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (3361741, 1)] : List FactorBlock).map factorBlockValue).prod) = 33617411 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_5
      · exact prime_oneHundredFourteenDH_3361741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 33617411) ^ 16808705 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 33617411) ^ 6723482 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 33617411) ^ 10 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_34063123 : Nat.Prime 34063123 := by
  apply lucas_primality 34063123 (2 : ZMod 34063123)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5677187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5677187, 1)] : List FactorBlock).map factorBlockValue).prod) = 34063123 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_5677187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 34063123) ^ 17031561 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 34063123) ^ 11354374 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 34063123) ^ 6 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_34072711 : Nat.Prime 34072711 := by
  apply lucas_primality 34072711 (6 : ZMod 34072711)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (162251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (162251, 1)] : List FactorBlock).map factorBlockValue).prod) = 34072711 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_5
      · exact prime_oneHundredFourteenDH_7
      · exact prime_oneHundredFourteenDH_162251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 34072711) ^ 17036355 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (6 : ZMod 34072711) ^ 11357570 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (6 : ZMod 34072711) ^ 6814542 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (6 : ZMod 34072711) ^ 4867530 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (6 : ZMod 34072711) ^ 210 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_35720623 : Nat.Prime 35720623 := by
  apply lucas_primality 35720623 (3 : ZMod 35720623)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 1), (53, 1), (1783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 1), (53, 1), (1783, 1)] : List FactorBlock).map factorBlockValue).prod) = 35720623 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_7
      · exact prime_oneHundredFourteenDH_53
      · exact prime_oneHundredFourteenDH_1783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 35720623) ^ 17860311 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 35720623) ^ 11906874 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 35720623) ^ 5102946 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 35720623) ^ 673974 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 35720623) ^ 20034 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_38026081 : Nat.Prime 38026081 := by
  apply lucas_primality 38026081 (23 : ZMod 38026081)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (5, 1), (26407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (5, 1), (26407, 1)] : List FactorBlock).map factorBlockValue).prod) = 38026081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_5
      · exact prime_oneHundredFourteenDH_26407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (23 : ZMod 38026081) ^ 19013040 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (23 : ZMod 38026081) ^ 12675360 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (23 : ZMod 38026081) ^ 7605216 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (23 : ZMod 38026081) ^ 1440 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_41462027 : Nat.Prime 41462027 := by
  apply lucas_primality 41462027 (2 : ZMod 41462027)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2293, 1), (9041, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2293, 1), (9041, 1)] : List FactorBlock).map factorBlockValue).prod) = 41462027 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_2293
      · exact prime_oneHundredFourteenDH_9041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 41462027) ^ 20731013 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 41462027) ^ 18082 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 41462027) ^ 4586 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_46968349 : Nat.Prime 46968349 := by
  apply lucas_primality 46968349 (6 : ZMod 46968349)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (17, 1), (31, 1), (1061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (17, 1), (31, 1), (1061, 1)] : List FactorBlock).map factorBlockValue).prod) = 46968349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_7
      · exact prime_oneHundredFourteenDH_17
      · exact prime_oneHundredFourteenDH_31
      · exact prime_oneHundredFourteenDH_1061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 46968349) ^ 23484174 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (6 : ZMod 46968349) ^ 15656116 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (6 : ZMod 46968349) ^ 6709764 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (6 : ZMod 46968349) ^ 2762844 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (6 : ZMod 46968349) ^ 1515108 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (6 : ZMod 46968349) ^ 44268 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_47275729 : Nat.Prime 47275729 := by
  apply lucas_primality 47275729 (11 : ZMod 47275729)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (984911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (984911, 1)] : List FactorBlock).map factorBlockValue).prod) = 47275729 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_984911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 47275729) ^ 23637864 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (11 : ZMod 47275729) ^ 15758576 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (11 : ZMod 47275729) ^ 48 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_55676329 : Nat.Prime 55676329 := by
  apply lucas_primality 55676329 (17 : ZMod 55676329)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (109, 1), (21283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (109, 1), (21283, 1)] : List FactorBlock).map factorBlockValue).prod) = 55676329 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_109
      · exact prime_oneHundredFourteenDH_21283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 55676329) ^ 27838164 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (17 : ZMod 55676329) ^ 18558776 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (17 : ZMod 55676329) ^ 510792 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (17 : ZMod 55676329) ^ 2616 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_55926539 : Nat.Prime 55926539 := by
  apply lucas_primality 55926539 (2 : ZMod 55926539)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (1471751, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (1471751, 1)] : List FactorBlock).map factorBlockValue).prod) = 55926539 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_19
      · exact prime_oneHundredFourteenDH_1471751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 55926539) ^ 27963269 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 55926539) ^ 2943502 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 55926539) ^ 38 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_56069599 : Nat.Prime 56069599 := by
  apply lucas_primality 56069599 (15 : ZMod 56069599)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (718841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (718841, 1)] : List FactorBlock).map factorBlockValue).prod) = 56069599 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_13
      · exact prime_oneHundredFourteenDH_718841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (15 : ZMod 56069599) ^ 28034799 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (15 : ZMod 56069599) ^ 18689866 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (15 : ZMod 56069599) ^ 4313046 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (15 : ZMod 56069599) ^ 78 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_59929613 : Nat.Prime 59929613 := by
  apply lucas_primality 59929613 (2 : ZMod 59929613)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1811, 1), (8273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1811, 1), (8273, 1)] : List FactorBlock).map factorBlockValue).prod) = 59929613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_1811
      · exact prime_oneHundredFourteenDH_8273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 59929613) ^ 29964806 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 59929613) ^ 33092 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 59929613) ^ 7244 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_65355881 : Nat.Prime 65355881 := by
  apply lucas_primality 65355881 (3 : ZMod 65355881)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (23, 1), (71039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (23, 1), (71039, 1)] : List FactorBlock).map factorBlockValue).prod) = 65355881 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_5
      · exact prime_oneHundredFourteenDH_23
      · exact prime_oneHundredFourteenDH_71039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 65355881) ^ 32677940 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 65355881) ^ 13071176 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 65355881) ^ 2841560 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 65355881) ^ 920 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_66708619 : Nat.Prime 66708619 := by
  apply lucas_primality 66708619 (3 : ZMod 66708619)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (71, 1), (156593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (71, 1), (156593, 1)] : List FactorBlock).map factorBlockValue).prod) = 66708619 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_71
      · exact prime_oneHundredFourteenDH_156593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 66708619) ^ 33354309 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 66708619) ^ 22236206 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 66708619) ^ 939558 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 66708619) ^ 426 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_70246711 : Nat.Prime 70246711 := by
  apply lucas_primality 70246711 (3 : ZMod 70246711)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (151, 1), (1723, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (151, 1), (1723, 1)] : List FactorBlock).map factorBlockValue).prod) = 70246711 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_5
      · exact prime_oneHundredFourteenDH_151
      · exact prime_oneHundredFourteenDH_1723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 70246711) ^ 35123355 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 70246711) ^ 23415570 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 70246711) ^ 14049342 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 70246711) ^ 465210 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 70246711) ^ 40770 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_72827129 : Nat.Prime 72827129 := by
  apply lucas_primality 72827129 (3 : ZMod 72827129)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (827581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (827581, 1)] : List FactorBlock).map factorBlockValue).prod) = 72827129 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_11
      · exact prime_oneHundredFourteenDH_827581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 72827129) ^ 36413564 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 72827129) ^ 6620648 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 72827129) ^ 88 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_76449433 : Nat.Prime 76449433 := by
  apply lucas_primality 76449433 (5 : ZMod 76449433)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (199, 1), (16007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (199, 1), (16007, 1)] : List FactorBlock).map factorBlockValue).prod) = 76449433 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_199
      · exact prime_oneHundredFourteenDH_16007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 76449433) ^ 38224716 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (5 : ZMod 76449433) ^ 25483144 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (5 : ZMod 76449433) ^ 384168 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (5 : ZMod 76449433) ^ 4776 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_86319059 : Nat.Prime 86319059 := by
  apply lucas_primality 86319059 (2 : ZMod 86319059)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (523, 1), (11789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (523, 1), (11789, 1)] : List FactorBlock).map factorBlockValue).prod) = 86319059 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_7
      · exact prime_oneHundredFourteenDH_523
      · exact prime_oneHundredFourteenDH_11789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 86319059) ^ 43159529 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 86319059) ^ 12331294 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 86319059) ^ 165046 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 86319059) ^ 7322 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_91454369 : Nat.Prime 91454369 := by
  apply lucas_primality 91454369 (3 : ZMod 91454369)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (2857949, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (2857949, 1)] : List FactorBlock).map factorBlockValue).prod) = 91454369 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_2857949
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 91454369) ^ 45727184 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 91454369) ^ 32 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_100885381 : Nat.Prime 100885381 := by
  apply lucas_primality 100885381 (2 : ZMod 100885381)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (1681423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (1681423, 1)] : List FactorBlock).map factorBlockValue).prod) = 100885381 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_5
      · exact prime_oneHundredFourteenDH_1681423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 100885381) ^ 50442690 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 100885381) ^ 33628460 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 100885381) ^ 20177076 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 100885381) ^ 60 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_101080961 : Nat.Prime 101080961 := by
  apply lucas_primality 101080961 (3 : ZMod 101080961)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (5, 1), (43, 1), (3673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (5, 1), (43, 1), (3673, 1)] : List FactorBlock).map factorBlockValue).prod) = 101080961 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_5
      · exact prime_oneHundredFourteenDH_43
      · exact prime_oneHundredFourteenDH_3673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 101080961) ^ 50540480 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 101080961) ^ 20216192 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 101080961) ^ 2350720 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 101080961) ^ 27520 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_102835853 : Nat.Prime 102835853 := by
  apply lucas_primality 102835853 (2 : ZMod 102835853)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (23, 1), (159683, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (23, 1), (159683, 1)] : List FactorBlock).map factorBlockValue).prod) = 102835853 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_7
      · exact prime_oneHundredFourteenDH_23
      · exact prime_oneHundredFourteenDH_159683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 102835853) ^ 51417926 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 102835853) ^ 14690836 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 102835853) ^ 4471124 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 102835853) ^ 644 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_108632453 : Nat.Prime 108632453 := by
  apply lucas_primality 108632453 (2 : ZMod 108632453)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (41, 1), (59, 1), (103, 1), (109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (41, 1), (59, 1), (103, 1), (109, 1)] : List FactorBlock).map factorBlockValue).prod) = 108632453 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_41
      · exact prime_oneHundredFourteenDH_59
      · exact prime_oneHundredFourteenDH_103
      · exact prime_oneHundredFourteenDH_109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 108632453) ^ 54316226 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 108632453) ^ 2649572 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 108632453) ^ 1841228 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 108632453) ^ 1054684 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 108632453) ^ 996628 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_108957133 : Nat.Prime 108957133 := by
  apply lucas_primality 108957133 (2 : ZMod 108957133)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (3026587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (3026587, 1)] : List FactorBlock).map factorBlockValue).prod) = 108957133 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_3026587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 108957133) ^ 54478566 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 108957133) ^ 36319044 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 108957133) ^ 36 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_111154033 : Nat.Prime 111154033 := by
  apply lucas_primality 111154033 (5 : ZMod 111154033)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 5), (11, 1), (23, 1), (113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 5), (11, 1), (23, 1), (113, 1)] : List FactorBlock).map factorBlockValue).prod) = 111154033 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_11
      · exact prime_oneHundredFourteenDH_23
      · exact prime_oneHundredFourteenDH_113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 111154033) ^ 55577016 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (5 : ZMod 111154033) ^ 37051344 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (5 : ZMod 111154033) ^ 10104912 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (5 : ZMod 111154033) ^ 4832784 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (5 : ZMod 111154033) ^ 983664 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_124375177 : Nat.Prime 124375177 := by
  apply lucas_primality 124375177 (5 : ZMod 124375177)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 5), (137, 1), (467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 5), (137, 1), (467, 1)] : List FactorBlock).map factorBlockValue).prod) = 124375177 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_137
      · exact prime_oneHundredFourteenDH_467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 124375177) ^ 62187588 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (5 : ZMod 124375177) ^ 41458392 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (5 : ZMod 124375177) ^ 907848 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (5 : ZMod 124375177) ^ 266328 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_125933891 : Nat.Prime 125933891 := by
  apply lucas_primality 125933891 (2 : ZMod 125933891)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (61, 1), (431, 1), (479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (61, 1), (431, 1), (479, 1)] : List FactorBlock).map factorBlockValue).prod) = 125933891 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_5
      · exact prime_oneHundredFourteenDH_61
      · exact prime_oneHundredFourteenDH_431
      · exact prime_oneHundredFourteenDH_479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 125933891) ^ 62966945 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 125933891) ^ 25186778 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 125933891) ^ 2064490 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 125933891) ^ 292190 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 125933891) ^ 262910 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_130246913 : Nat.Prime 130246913 := by
  apply lucas_primality 130246913 (3 : ZMod 130246913)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (251, 1), (2027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (251, 1), (2027, 1)] : List FactorBlock).map factorBlockValue).prod) = 130246913 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_251
      · exact prime_oneHundredFourteenDH_2027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 130246913) ^ 65123456 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 130246913) ^ 518912 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 130246913) ^ 64256 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_133148837 : Nat.Prime 133148837 := by
  apply lucas_primality 133148837 (2 : ZMod 133148837)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (33287209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (33287209, 1)] : List FactorBlock).map factorBlockValue).prod) = 133148837 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_33287209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 133148837) ^ 66574418 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 133148837) ^ 4 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_142714391 : Nat.Prime 142714391 := by
  apply lucas_primality 142714391 (7 : ZMod 142714391)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (13, 1), (31, 1), (5059, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (13, 1), (31, 1), (5059, 1)] : List FactorBlock).map factorBlockValue).prod) = 142714391 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_5
      · exact prime_oneHundredFourteenDH_7
      · exact prime_oneHundredFourteenDH_13
      · exact prime_oneHundredFourteenDH_31
      · exact prime_oneHundredFourteenDH_5059
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 142714391) ^ 71357195 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (7 : ZMod 142714391) ^ 28542878 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (7 : ZMod 142714391) ^ 20387770 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (7 : ZMod 142714391) ^ 10978030 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (7 : ZMod 142714391) ^ 4603690 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (7 : ZMod 142714391) ^ 28210 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_146058427 : Nat.Prime 146058427 := by
  apply lucas_primality 146058427 (3 : ZMod 146058427)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (1597, 1), (5081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (1597, 1), (5081, 1)] : List FactorBlock).map factorBlockValue).prod) = 146058427 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_1597
      · exact prime_oneHundredFourteenDH_5081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 146058427) ^ 73029213 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 146058427) ^ 48686142 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 146058427) ^ 91458 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 146058427) ^ 28746 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_191921437 : Nat.Prime 191921437 := by
  apply lucas_primality 191921437 (2 : ZMod 191921437)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 2), (108799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 2), (108799, 1)] : List FactorBlock).map factorBlockValue).prod) = 191921437 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_7
      · exact prime_oneHundredFourteenDH_108799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 191921437) ^ 95960718 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 191921437) ^ 63973812 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 191921437) ^ 27417348 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 191921437) ^ 1764 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_193897349 : Nat.Prime 193897349 := by
  apply lucas_primality 193897349 (2 : ZMod 193897349)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (797, 1), (60821, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (797, 1), (60821, 1)] : List FactorBlock).map factorBlockValue).prod) = 193897349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_797
      · exact prime_oneHundredFourteenDH_60821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 193897349) ^ 96948674 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 193897349) ^ 243284 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 193897349) ^ 3188 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_194084747 : Nat.Prime 194084747 := by
  apply lucas_primality 194084747 (2 : ZMod 194084747)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (109, 1), (251, 1), (3547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (109, 1), (251, 1), (3547, 1)] : List FactorBlock).map factorBlockValue).prod) = 194084747 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_109
      · exact prime_oneHundredFourteenDH_251
      · exact prime_oneHundredFourteenDH_3547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 194084747) ^ 97042373 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 194084747) ^ 1780594 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 194084747) ^ 773246 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 194084747) ^ 54718 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_219229811 : Nat.Prime 219229811 := by
  apply lucas_primality 219229811 (2 : ZMod 219229811)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (37, 1), (131, 1), (4523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (37, 1), (131, 1), (4523, 1)] : List FactorBlock).map factorBlockValue).prod) = 219229811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_5
      · exact prime_oneHundredFourteenDH_37
      · exact prime_oneHundredFourteenDH_131
      · exact prime_oneHundredFourteenDH_4523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 219229811) ^ 109614905 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 219229811) ^ 43845962 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 219229811) ^ 5925130 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 219229811) ^ 1673510 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 219229811) ^ 48470 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_267166073 : Nat.Prime 267166073 := by
  apply lucas_primality 267166073 (3 : ZMod 267166073)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (33395759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (33395759, 1)] : List FactorBlock).map factorBlockValue).prod) = 267166073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_33395759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 267166073) ^ 133583036 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 267166073) ^ 8 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_285306533 : Nat.Prime 285306533 := by
  apply lucas_primality 285306533 (2 : ZMod 285306533)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (593, 1), (17183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (593, 1), (17183, 1)] : List FactorBlock).map factorBlockValue).prod) = 285306533 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_7
      · exact prime_oneHundredFourteenDH_593
      · exact prime_oneHundredFourteenDH_17183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 285306533) ^ 142653266 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 285306533) ^ 40758076 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 285306533) ^ 481124 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 285306533) ^ 16604 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_288994799 : Nat.Prime 288994799 := by
  apply lucas_primality 288994799 (7 : ZMod 288994799)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 2), (79, 1), (6329, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 2), (79, 1), (6329, 1)] : List FactorBlock).map factorBlockValue).prod) = 288994799 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_17
      · exact prime_oneHundredFourteenDH_79
      · exact prime_oneHundredFourteenDH_6329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 288994799) ^ 144497399 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (7 : ZMod 288994799) ^ 16999694 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (7 : ZMod 288994799) ^ 3658162 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (7 : ZMod 288994799) ^ 45662 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_307468349 : Nat.Prime 307468349 := by
  apply lucas_primality 307468349 (2 : ZMod 307468349)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (41, 2), (4157, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (41, 2), (4157, 1)] : List FactorBlock).map factorBlockValue).prod) = 307468349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_11
      · exact prime_oneHundredFourteenDH_41
      · exact prime_oneHundredFourteenDH_4157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 307468349) ^ 153734174 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 307468349) ^ 27951668 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 307468349) ^ 7499228 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 307468349) ^ 73964 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_317803697 : Nat.Prime 317803697 := by
  apply lucas_primality 317803697 (3 : ZMod 317803697)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (23, 1), (107, 1), (1153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (23, 1), (107, 1), (1153, 1)] : List FactorBlock).map factorBlockValue).prod) = 317803697 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_7
      · exact prime_oneHundredFourteenDH_23
      · exact prime_oneHundredFourteenDH_107
      · exact prime_oneHundredFourteenDH_1153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 317803697) ^ 158901848 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 317803697) ^ 45400528 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 317803697) ^ 13817552 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 317803697) ^ 2970128 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 317803697) ^ 275632 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_360423779 : Nat.Prime 360423779 := by
  apply lucas_primality 360423779 (2 : ZMod 360423779)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (13, 1), (1260223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (13, 1), (1260223, 1)] : List FactorBlock).map factorBlockValue).prod) = 360423779 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_11
      · exact prime_oneHundredFourteenDH_13
      · exact prime_oneHundredFourteenDH_1260223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 360423779) ^ 180211889 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 360423779) ^ 32765798 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 360423779) ^ 27724906 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 360423779) ^ 286 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_466649147 : Nat.Prime 466649147 := by
  apply lucas_primality 466649147 (2 : ZMod 466649147)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (61, 1), (3824993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (61, 1), (3824993, 1)] : List FactorBlock).map factorBlockValue).prod) = 466649147 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_61
      · exact prime_oneHundredFourteenDH_3824993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 466649147) ^ 233324573 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 466649147) ^ 7649986 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 466649147) ^ 122 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_579546427 : Nat.Prime 579546427 := by
  apply lucas_primality 579546427 (2 : ZMod 579546427)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 2), (100511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 2), (100511, 1)] : List FactorBlock).map factorBlockValue).prod) = 579546427 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_31
      · exact prime_oneHundredFourteenDH_100511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 579546427) ^ 289773213 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 579546427) ^ 193182142 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 579546427) ^ 18695046 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 579546427) ^ 5766 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_597096427 : Nat.Prime 597096427 := by
  apply lucas_primality 597096427 (2 : ZMod 597096427)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (61, 1), (719, 1), (2269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (61, 1), (719, 1), (2269, 1)] : List FactorBlock).map factorBlockValue).prod) = 597096427 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_61
      · exact prime_oneHundredFourteenDH_719
      · exact prime_oneHundredFourteenDH_2269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 597096427) ^ 298548213 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 597096427) ^ 199032142 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 597096427) ^ 9788466 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 597096427) ^ 830454 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 597096427) ^ 263154 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_640433267 : Nat.Prime 640433267 := by
  apply lucas_primality 640433267 (2 : ZMod 640433267)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (19, 1), (61, 1), (25117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (19, 1), (61, 1), (25117, 1)] : List FactorBlock).map factorBlockValue).prod) = 640433267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_11
      · exact prime_oneHundredFourteenDH_19
      · exact prime_oneHundredFourteenDH_61
      · exact prime_oneHundredFourteenDH_25117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 640433267) ^ 320216633 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 58221206 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 33707014 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 10498906 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 25498 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_714027719 : Nat.Prime 714027719 := by
  apply lucas_primality 714027719 (11 : ZMod 714027719)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) = 714027719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_17203
      · exact prime_oneHundredFourteenDH_20753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 714027719) ^ 357013859 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 41506 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 34406 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_720847559 : Nat.Prime 720847559 := by
  apply lucas_primality 720847559 (11 : ZMod 720847559)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (360423779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (360423779, 1)] : List FactorBlock).map factorBlockValue).prod) = 720847559 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_360423779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (11 : ZMod 720847559) ^ 360423779 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (11 : ZMod 720847559) ^ 2 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_888404761 : Nat.Prime 888404761 := by
  apply lucas_primality 888404761 (11 : ZMod 888404761)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 4), (5, 1), (274199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 4), (5, 1), (274199, 1)] : List FactorBlock).map factorBlockValue).prod) = 888404761 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_5
      · exact prime_oneHundredFourteenDH_274199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 888404761) ^ 444202380 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (11 : ZMod 888404761) ^ 296134920 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (11 : ZMod 888404761) ^ 177680952 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (11 : ZMod 888404761) ^ 3240 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_896642093 : Nat.Prime 896642093 := by
  apply lucas_primality 896642093 (2 : ZMod 896642093)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (593, 1), (378011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (593, 1), (378011, 1)] : List FactorBlock).map factorBlockValue).prod) = 896642093 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_593
      · exact prime_oneHundredFourteenDH_378011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 896642093) ^ 448321046 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 896642093) ^ 1512044 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 896642093) ^ 2372 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_914124779 : Nat.Prime 914124779 := by
  apply lucas_primality 914124779 (2 : ZMod 914124779)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (1459, 1), (44753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (1459, 1), (44753, 1)] : List FactorBlock).map factorBlockValue).prod) = 914124779 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_7
      · exact prime_oneHundredFourteenDH_1459
      · exact prime_oneHundredFourteenDH_44753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 914124779) ^ 457062389 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 914124779) ^ 130589254 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 914124779) ^ 626542 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 914124779) ^ 20426 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_975025621 : Nat.Prime 975025621 := by
  apply lucas_primality 975025621 (2 : ZMod 975025621)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 1), (1805603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 1), (1805603, 1)] : List FactorBlock).map factorBlockValue).prod) = 975025621 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_5
      · exact prime_oneHundredFourteenDH_1805603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 975025621) ^ 487512810 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 975025621) ^ 325008540 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 975025621) ^ 195005124 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 975025621) ^ 540 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_980366801 : Nat.Prime 980366801 := by
  apply lucas_primality 980366801 (3 : ZMod 980366801)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 2), (7, 1), (37, 1), (9463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 2), (7, 1), (37, 1), (9463, 1)] : List FactorBlock).map factorBlockValue).prod) = 980366801 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_5
      · exact prime_oneHundredFourteenDH_7
      · exact prime_oneHundredFourteenDH_37
      · exact prime_oneHundredFourteenDH_9463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 980366801) ^ 490183400 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 980366801) ^ 196073360 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 980366801) ^ 140052400 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 980366801) ^ 26496400 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 980366801) ^ 103600 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_1044846631 : Nat.Prime 1044846631 := by
  apply lucas_primality 1044846631 (15 : ZMod 1044846631)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (31, 1), (197, 1), (1901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (31, 1), (197, 1), (1901, 1)] : List FactorBlock).map factorBlockValue).prod) = 1044846631 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_5
      · exact prime_oneHundredFourteenDH_31
      · exact prime_oneHundredFourteenDH_197
      · exact prime_oneHundredFourteenDH_1901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 1044846631) ^ 522423315 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (15 : ZMod 1044846631) ^ 348282210 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (15 : ZMod 1044846631) ^ 208969326 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (15 : ZMod 1044846631) ^ 33704730 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (15 : ZMod 1044846631) ^ 5303790 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (15 : ZMod 1044846631) ^ 549630 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_1096580227 : Nat.Prime 1096580227 := by
  apply lucas_primality 1096580227 (2 : ZMod 1096580227)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (26109053, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (26109053, 1)] : List FactorBlock).map factorBlockValue).prod) = 1096580227 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_7
      · exact prime_oneHundredFourteenDH_26109053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1096580227) ^ 548290113 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1096580227) ^ 365526742 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1096580227) ^ 156654318 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1096580227) ^ 42 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_1630123721 : Nat.Prime 1630123721 := by
  apply lucas_primality 1630123721 (3 : ZMod 1630123721)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (2069, 1), (19697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (2069, 1), (19697, 1)] : List FactorBlock).map factorBlockValue).prod) = 1630123721 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_5
      · exact prime_oneHundredFourteenDH_2069
      · exact prime_oneHundredFourteenDH_19697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1630123721) ^ 815061860 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1630123721) ^ 326024744 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1630123721) ^ 787880 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1630123721) ^ 82760 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_1847513149 : Nat.Prime 1847513149 := by
  apply lucas_primality 1847513149 (2 : ZMod 1847513149)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (17, 1), (811, 1), (859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (17, 1), (811, 1), (859, 1)] : List FactorBlock).map factorBlockValue).prod) = 1847513149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_13
      · exact prime_oneHundredFourteenDH_17
      · exact prime_oneHundredFourteenDH_811
      · exact prime_oneHundredFourteenDH_859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1847513149) ^ 923756574 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1847513149) ^ 615837716 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1847513149) ^ 142116396 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1847513149) ^ 108677244 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1847513149) ^ 2278068 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1847513149) ^ 2150772 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_2230285021 : Nat.Prime 2230285021 := by
  apply lucas_primality 2230285021 (2 : ZMod 2230285021)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (29, 1), (1281773, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (29, 1), (1281773, 1)] : List FactorBlock).map factorBlockValue).prod) = 2230285021 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_5
      · exact prime_oneHundredFourteenDH_29
      · exact prime_oneHundredFourteenDH_1281773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2230285021) ^ 1115142510 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2230285021) ^ 743428340 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2230285021) ^ 446057004 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2230285021) ^ 76906380 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2230285021) ^ 1740 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_2303408287 : Nat.Prime 2303408287 := by
  apply lucas_primality 2303408287 (11 : ZMod 2303408287)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (37, 1), (1152857, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (37, 1), (1152857, 1)] : List FactorBlock).map factorBlockValue).prod) = 2303408287 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_37
      · exact prime_oneHundredFourteenDH_1152857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 2303408287) ^ 1151704143 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (11 : ZMod 2303408287) ^ 767802762 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (11 : ZMod 2303408287) ^ 62254278 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (11 : ZMod 2303408287) ^ 1998 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_2708662711 : Nat.Prime 2708662711 := by
  apply lucas_primality 2708662711 (6 : ZMod 2708662711)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (13, 2), (534253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (13, 2), (534253, 1)] : List FactorBlock).map factorBlockValue).prod) = 2708662711 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_5
      · exact prime_oneHundredFourteenDH_13
      · exact prime_oneHundredFourteenDH_534253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 2708662711) ^ 1354331355 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (6 : ZMod 2708662711) ^ 902887570 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (6 : ZMod 2708662711) ^ 541732542 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (6 : ZMod 2708662711) ^ 208358670 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (6 : ZMod 2708662711) ^ 5070 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_2868527881 : Nat.Prime 2868527881 := by
  apply lucas_primality 2868527881 (17 : ZMod 2868527881)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (7968133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (7968133, 1)] : List FactorBlock).map factorBlockValue).prod) = 2868527881 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_5
      · exact prime_oneHundredFourteenDH_7968133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 2868527881) ^ 1434263940 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (17 : ZMod 2868527881) ^ 956175960 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (17 : ZMod 2868527881) ^ 573705576 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (17 : ZMod 2868527881) ^ 360 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_3515265851 : Nat.Prime 3515265851 := by
  apply lucas_primality 3515265851 (2 : ZMod 3515265851)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (4783, 1), (14699, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (4783, 1), (14699, 1)] : List FactorBlock).map factorBlockValue).prod) = 3515265851 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_5
      · exact prime_oneHundredFourteenDH_4783
      · exact prime_oneHundredFourteenDH_14699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3515265851) ^ 1757632925 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 3515265851) ^ 703053170 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 3515265851) ^ 734950 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 3515265851) ^ 239150 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_3869518907 : Nat.Prime 3869518907 := by
  apply lucas_primality 3869518907 (2 : ZMod 3869518907)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (3691, 1), (47653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (3691, 1), (47653, 1)] : List FactorBlock).map factorBlockValue).prod) = 3869518907 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_11
      · exact prime_oneHundredFourteenDH_3691
      · exact prime_oneHundredFourteenDH_47653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3869518907) ^ 1934759453 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 3869518907) ^ 351774446 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 3869518907) ^ 1048366 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 3869518907) ^ 81202 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_3904620173 : Nat.Prime 3904620173 := by
  apply lucas_primality 3904620173 (2 : ZMod 3904620173)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (821, 1), (1033, 1), (1151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (821, 1), (1033, 1), (1151, 1)] : List FactorBlock).map factorBlockValue).prod) = 3904620173 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_821
      · exact prime_oneHundredFourteenDH_1033
      · exact prime_oneHundredFourteenDH_1151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3904620173) ^ 1952310086 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 3904620173) ^ 4755932 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 3904620173) ^ 3779884 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 3904620173) ^ 3392372 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_3969714277 : Nat.Prime 3969714277 := by
  apply lucas_primality 3969714277 (2 : ZMod 3969714277)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (11, 2), (911321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (11, 2), (911321, 1)] : List FactorBlock).map factorBlockValue).prod) = 3969714277 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_11
      · exact prime_oneHundredFourteenDH_911321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3969714277) ^ 1984857138 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 3969714277) ^ 1323238092 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 3969714277) ^ 360883116 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 3969714277) ^ 4356 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_4133214713 : Nat.Prime 4133214713 := by
  apply lucas_primality 4133214713 (3 : ZMod 4133214713)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (46968349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (46968349, 1)] : List FactorBlock).map factorBlockValue).prod) = 4133214713 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_11
      · exact prime_oneHundredFourteenDH_46968349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 4133214713) ^ 2066607356 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 4133214713) ^ 375746792 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 4133214713) ^ 88 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_4959861037 : Nat.Prime 4959861037 := by
  apply lucas_primality 4959861037 (2 : ZMod 4959861037)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (23, 1), (97, 1), (14251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (23, 1), (97, 1), (14251, 1)] : List FactorBlock).map factorBlockValue).prod) = 4959861037 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_13
      · exact prime_oneHundredFourteenDH_23
      · exact prime_oneHundredFourteenDH_97
      · exact prime_oneHundredFourteenDH_14251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4959861037) ^ 2479930518 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 4959861037) ^ 1653287012 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 4959861037) ^ 381527772 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 4959861037) ^ 215646132 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 4959861037) ^ 51132588 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 4959861037) ^ 348036 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_5029015027 : Nat.Prime 5029015027 := by
  apply lucas_primality 5029015027 (2 : ZMod 5029015027)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (3701, 1), (32353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (3701, 1), (32353, 1)] : List FactorBlock).map factorBlockValue).prod) = 5029015027 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_7
      · exact prime_oneHundredFourteenDH_3701
      · exact prime_oneHundredFourteenDH_32353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5029015027) ^ 2514507513 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 5029015027) ^ 1676338342 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 5029015027) ^ 718430718 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 5029015027) ^ 1358826 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 5029015027) ^ 155442 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_5324400491 : Nat.Prime 5324400491 := by
  apply lucas_primality 5324400491 (2 : ZMod 5324400491)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (6959, 1), (76511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (6959, 1), (76511, 1)] : List FactorBlock).map factorBlockValue).prod) = 5324400491 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_5
      · exact prime_oneHundredFourteenDH_6959
      · exact prime_oneHundredFourteenDH_76511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5324400491) ^ 2662200245 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 5324400491) ^ 1064880098 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 5324400491) ^ 765110 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 5324400491) ^ 69590 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_5934853481 : Nat.Prime 5934853481 := by
  apply lucas_primality 5934853481 (3 : ZMod 5934853481)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (29, 1), (61, 1), (83873, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (29, 1), (61, 1), (83873, 1)] : List FactorBlock).map factorBlockValue).prod) = 5934853481 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_5
      · exact prime_oneHundredFourteenDH_29
      · exact prime_oneHundredFourteenDH_61
      · exact prime_oneHundredFourteenDH_83873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 5934853481) ^ 2967426740 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 5934853481) ^ 1186970696 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 5934853481) ^ 204650120 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 5934853481) ^ 97292680 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 5934853481) ^ 70760 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_6037638679 : Nat.Prime 6037638679 := by
  apply lucas_primality 6037638679 (3 : ZMod 6037638679)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) = 6037638679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_31
      · exact prime_oneHundredFourteenDH_10820141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6037638679) ^ 3018819339 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 2012546226 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 194762538 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 558 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_6303638423 : Nat.Prime 6303638423 := by
  apply lucas_primality 6303638423 (5 : ZMod 6303638423)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (53, 1), (89, 1), (18059, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (53, 1), (89, 1), (18059, 1)] : List FactorBlock).map factorBlockValue).prod) = 6303638423 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_37
      · exact prime_oneHundredFourteenDH_53
      · exact prime_oneHundredFourteenDH_89
      · exact prime_oneHundredFourteenDH_18059
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 6303638423) ^ 3151819211 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (5 : ZMod 6303638423) ^ 170368606 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (5 : ZMod 6303638423) ^ 118936574 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (5 : ZMod 6303638423) ^ 70827398 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (5 : ZMod 6303638423) ^ 349058 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_6314588711 : Nat.Prime 6314588711 := by
  apply lucas_primality 6314588711 (7 : ZMod 6314588711)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (31, 1), (149, 1), (136709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (31, 1), (149, 1), (136709, 1)] : List FactorBlock).map factorBlockValue).prod) = 6314588711 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_5
      · exact prime_oneHundredFourteenDH_31
      · exact prime_oneHundredFourteenDH_149
      · exact prime_oneHundredFourteenDH_136709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 6314588711) ^ 3157294355 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (7 : ZMod 6314588711) ^ 1262917742 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (7 : ZMod 6314588711) ^ 203696410 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (7 : ZMod 6314588711) ^ 42379790 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (7 : ZMod 6314588711) ^ 46190 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_6622312097 : Nat.Prime 6622312097 := by
  apply lucas_primality 6622312097 (3 : ZMod 6622312097)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (37, 1), (271, 1), (20639, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (37, 1), (271, 1), (20639, 1)] : List FactorBlock).map factorBlockValue).prod) = 6622312097 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_37
      · exact prime_oneHundredFourteenDH_271
      · exact prime_oneHundredFourteenDH_20639
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6622312097) ^ 3311156048 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 6622312097) ^ 178981408 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 6622312097) ^ 24436576 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 6622312097) ^ 320864 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_6847356793 : Nat.Prime 6847356793 := by
  apply lucas_primality 6847356793 (5 : ZMod 6847356793)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (285306533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (285306533, 1)] : List FactorBlock).map factorBlockValue).prod) = 6847356793 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_285306533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 6847356793) ^ 3423678396 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (5 : ZMod 6847356793) ^ 2282452264 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (5 : ZMod 6847356793) ^ 24 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_7371456913 : Nat.Prime 7371456913 := by
  apply lucas_primality 7371456913 (5 : ZMod 7371456913)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (41, 1), (1248553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (41, 1), (1248553, 1)] : List FactorBlock).map factorBlockValue).prod) = 7371456913 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_41
      · exact prime_oneHundredFourteenDH_1248553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 7371456913) ^ 3685728456 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (5 : ZMod 7371456913) ^ 2457152304 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (5 : ZMod 7371456913) ^ 179791632 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (5 : ZMod 7371456913) ^ 5904 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_7847598419 : Nat.Prime 7847598419 := by
  apply lucas_primality 7847598419 (2 : ZMod 7847598419)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (29, 1), (12300311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (29, 1), (12300311, 1)] : List FactorBlock).map factorBlockValue).prod) = 7847598419 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_11
      · exact prime_oneHundredFourteenDH_29
      · exact prime_oneHundredFourteenDH_12300311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7847598419) ^ 3923799209 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 7847598419) ^ 713418038 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 7847598419) ^ 270606842 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 7847598419) ^ 638 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_8138000777 : Nat.Prime 8138000777 := by
  apply lucas_primality 8138000777 (3 : ZMod 8138000777)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17, 1), (43, 1), (1391587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17, 1), (43, 1), (1391587, 1)] : List FactorBlock).map factorBlockValue).prod) = 8138000777 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_17
      · exact prime_oneHundredFourteenDH_43
      · exact prime_oneHundredFourteenDH_1391587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 8138000777) ^ 4069000388 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 8138000777) ^ 478705928 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 8138000777) ^ 189255832 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 8138000777) ^ 5848 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_8289830111 : Nat.Prime 8289830111 := by
  apply lucas_primality 8289830111 (17 : ZMod 8289830111)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (233, 1), (3557867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (233, 1), (3557867, 1)] : List FactorBlock).map factorBlockValue).prod) = 8289830111 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_5
      · exact prime_oneHundredFourteenDH_233
      · exact prime_oneHundredFourteenDH_3557867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 8289830111) ^ 4144915055 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (17 : ZMod 8289830111) ^ 1657966022 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (17 : ZMod 8289830111) ^ 35578670 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (17 : ZMod 8289830111) ^ 2330 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_8822442547 : Nat.Prime 8822442547 := by
  apply lucas_primality 8822442547 (2 : ZMod 8822442547)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (103, 1), (1213, 1), (3923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (103, 1), (1213, 1), (3923, 1)] : List FactorBlock).map factorBlockValue).prod) = 8822442547 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_103
      · exact prime_oneHundredFourteenDH_1213
      · exact prime_oneHundredFourteenDH_3923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8822442547) ^ 4411221273 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 8822442547) ^ 2940814182 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 8822442547) ^ 85654782 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 8822442547) ^ 7273242 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 8822442547) ^ 2248902 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_11635980787 : Nat.Prime 11635980787 := by
  apply lucas_primality 11635980787 (2 : ZMod 11635980787)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (17, 1), (38026081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (17, 1), (38026081, 1)] : List FactorBlock).map factorBlockValue).prod) = 11635980787 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_17
      · exact prime_oneHundredFourteenDH_38026081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 11635980787) ^ 5817990393 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 11635980787) ^ 3878660262 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 11635980787) ^ 684469458 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 11635980787) ^ 306 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_12629177423 : Nat.Prime 12629177423 := by
  apply lucas_primality 12629177423 (5 : ZMod 12629177423)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (6314588711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (6314588711, 1)] : List FactorBlock).map factorBlockValue).prod) = 12629177423 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_6314588711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 12629177423) ^ 6314588711 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (5 : ZMod 12629177423) ^ 2 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_12749982383 : Nat.Prime 12749982383 := by
  apply lucas_primality 12749982383 (5 : ZMod 12749982383)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1153, 1), (5529047, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1153, 1), (5529047, 1)] : List FactorBlock).map factorBlockValue).prod) = 12749982383 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_1153
      · exact prime_oneHundredFourteenDH_5529047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 12749982383) ^ 6374991191 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (5 : ZMod 12749982383) ^ 11058094 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (5 : ZMod 12749982383) ^ 2306 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_12910955093 : Nat.Prime 12910955093 := by
  apply lucas_primality 12910955093 (2 : ZMod 12910955093)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (29, 1), (263, 1), (60457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (29, 1), (263, 1), (60457, 1)] : List FactorBlock).map factorBlockValue).prod) = 12910955093 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_7
      · exact prime_oneHundredFourteenDH_29
      · exact prime_oneHundredFourteenDH_263
      · exact prime_oneHundredFourteenDH_60457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 12910955093) ^ 6455477546 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 12910955093) ^ 1844422156 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 12910955093) ^ 445205348 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 12910955093) ^ 49091084 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 12910955093) ^ 213556 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_13132498471 : Nat.Prime 13132498471 := by
  apply lucas_primality 13132498471 (3 : ZMod 13132498471)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (13, 1), (17, 1), (19, 1), (53, 1), (281, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (13, 1), (17, 1), (19, 1), (53, 1), (281, 1)] : List FactorBlock).map factorBlockValue).prod) = 13132498471 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_5
      · exact prime_oneHundredFourteenDH_7
      · exact prime_oneHundredFourteenDH_13
      · exact prime_oneHundredFourteenDH_17
      · exact prime_oneHundredFourteenDH_19
      · exact prime_oneHundredFourteenDH_53
      · exact prime_oneHundredFourteenDH_281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 13132498471) ^ 6566249235 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 13132498471) ^ 4377499490 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 13132498471) ^ 2626499694 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 13132498471) ^ 1876071210 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 13132498471) ^ 1010192190 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 13132498471) ^ 772499910 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 13132498471) ^ 691184130 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 13132498471) ^ 247782990 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 13132498471) ^ 46734870 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_14543450219 : Nat.Prime 14543450219 := by
  apply lucas_primality 14543450219 (2 : ZMod 14543450219)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (41, 1), (16123559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (41, 1), (16123559, 1)] : List FactorBlock).map factorBlockValue).prod) = 14543450219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_11
      · exact prime_oneHundredFourteenDH_41
      · exact prime_oneHundredFourteenDH_16123559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 14543450219) ^ 7271725109 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 14543450219) ^ 1322131838 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 14543450219) ^ 354718298 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 14543450219) ^ 902 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_14646372071 : Nat.Prime 14646372071 := by
  apply lucas_primality 14646372071 (7 : ZMod 14646372071)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (133148837, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (133148837, 1)] : List FactorBlock).map factorBlockValue).prod) = 14646372071 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_5
      · exact prime_oneHundredFourteenDH_11
      · exact prime_oneHundredFourteenDH_133148837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 14646372071) ^ 7323186035 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (7 : ZMod 14646372071) ^ 2929274414 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (7 : ZMod 14646372071) ^ 1331488370 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (7 : ZMod 14646372071) ^ 110 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_15991285699 : Nat.Prime 15991285699 := by
  apply lucas_primality 15991285699 (3 : ZMod 15991285699)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (888404761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (888404761, 1)] : List FactorBlock).map factorBlockValue).prod) = 15991285699 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_888404761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 15991285699) ^ 7995642849 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 15991285699) ^ 5330428566 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 15991285699) ^ 18 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_19481132537 : Nat.Prime 19481132537 := by
  apply lucas_primality 19481132537 (3 : ZMod 19481132537)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (349, 1), (6977483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (349, 1), (6977483, 1)] : List FactorBlock).map factorBlockValue).prod) = 19481132537 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_349
      · exact prime_oneHundredFourteenDH_6977483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 19481132537) ^ 9740566268 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 19481132537) ^ 55819864 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 19481132537) ^ 2792 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_23427721039 : Nat.Prime 23427721039 := by
  apply lucas_primality 23427721039 (3 : ZMod 23427721039)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (3904620173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (3904620173, 1)] : List FactorBlock).map factorBlockValue).prod) = 23427721039 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_3904620173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 23427721039) ^ 11713860519 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 23427721039) ^ 7809240346 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 23427721039) ^ 6 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_36393530653 : Nat.Prime 36393530653 := by
  apply lucas_primality 36393530653 (2 : ZMod 36393530653)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5009, 1), (201823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5009, 1), (201823, 1)] : List FactorBlock).map factorBlockValue).prod) = 36393530653 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_5009
      · exact prime_oneHundredFourteenDH_201823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 36393530653) ^ 18196765326 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 36393530653) ^ 12131176884 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 36393530653) ^ 7265628 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 36393530653) ^ 180324 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_39933114467 : Nat.Prime 39933114467 := by
  apply lucas_primality 39933114467 (5 : ZMod 39933114467)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (4801, 1), (594119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (4801, 1), (594119, 1)] : List FactorBlock).map factorBlockValue).prod) = 39933114467 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_7
      · exact prime_oneHundredFourteenDH_4801
      · exact prime_oneHundredFourteenDH_594119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 39933114467) ^ 19966557233 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (5 : ZMod 39933114467) ^ 5704730638 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (5 : ZMod 39933114467) ^ 8317666 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (5 : ZMod 39933114467) ^ 67214 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_44444387353 : Nat.Prime 44444387353 := by
  apply lucas_primality 44444387353 (15 : ZMod 44444387353)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (73, 1), (167, 1), (151903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (73, 1), (167, 1), (151903, 1)] : List FactorBlock).map factorBlockValue).prod) = 44444387353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_73
      · exact prime_oneHundredFourteenDH_167
      · exact prime_oneHundredFourteenDH_151903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 44444387353) ^ 22222193676 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (15 : ZMod 44444387353) ^ 14814795784 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (15 : ZMod 44444387353) ^ 608827224 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (15 : ZMod 44444387353) ^ 266134056 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (15 : ZMod 44444387353) ^ 292584 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_45896446097 : Nat.Prime 45896446097 := by
  apply lucas_primality 45896446097 (3 : ZMod 45896446097)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (2868527881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (2868527881, 1)] : List FactorBlock).map factorBlockValue).prod) = 45896446097 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_2868527881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 45896446097) ^ 22948223048 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 45896446097) ^ 16 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_47681467189 : Nat.Prime 47681467189 := by
  apply lucas_primality 47681467189 (13 : ZMod 47681467189)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (4217, 1), (942247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (4217, 1), (942247, 1)] : List FactorBlock).map factorBlockValue).prod) = 47681467189 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_4217
      · exact prime_oneHundredFourteenDH_942247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 47681467189) ^ 23840733594 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (13 : ZMod 47681467189) ^ 15893822396 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (13 : ZMod 47681467189) ^ 11306964 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (13 : ZMod 47681467189) ^ 50604 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_50285095027 : Nat.Prime 50285095027 := by
  apply lucas_primality 50285095027 (3 : ZMod 50285095027)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 1), (288994799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 1), (288994799, 1)] : List FactorBlock).map factorBlockValue).prod) = 50285095027 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_29
      · exact prime_oneHundredFourteenDH_288994799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 50285095027) ^ 25142547513 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 50285095027) ^ 16761698342 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 50285095027) ^ 1733968794 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 50285095027) ^ 174 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_55538756671 : Nat.Prime 55538756671 := by
  apply lucas_primality 55538756671 (3 : ZMod 55538756671)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (859, 1), (2155171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (859, 1), (2155171, 1)] : List FactorBlock).map factorBlockValue).prod) = 55538756671 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_5
      · exact prime_oneHundredFourteenDH_859
      · exact prime_oneHundredFourteenDH_2155171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 55538756671) ^ 27769378335 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 55538756671) ^ 18512918890 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 55538756671) ^ 11107751334 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 55538756671) ^ 64655130 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 55538756671) ^ 25770 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_68068992679 : Nat.Prime 68068992679 := by
  apply lucas_primality 68068992679 (7 : ZMod 68068992679)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (597096427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (597096427, 1)] : List FactorBlock).map factorBlockValue).prod) = 68068992679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_19
      · exact prime_oneHundredFourteenDH_597096427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 68068992679) ^ 34034496339 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (7 : ZMod 68068992679) ^ 22689664226 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (7 : ZMod 68068992679) ^ 3582578562 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (7 : ZMod 68068992679) ^ 114 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_78585370601 : Nat.Prime 78585370601 := by
  apply lucas_primality 78585370601 (3 : ZMod 78585370601)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (11, 1), (35720623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (11, 1), (35720623, 1)] : List FactorBlock).map factorBlockValue).prod) = 78585370601 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_5
      · exact prime_oneHundredFourteenDH_11
      · exact prime_oneHundredFourteenDH_35720623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 78585370601) ^ 39292685300 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 78585370601) ^ 15717074120 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 78585370601) ^ 7144124600 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 78585370601) ^ 2200 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_79302919123 : Nat.Prime 79302919123 := by
  apply lucas_primality 79302919123 (2 : ZMod 79302919123)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (29, 1), (139, 1), (193, 1), (809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (29, 1), (139, 1), (193, 1), (809, 1)] : List FactorBlock).map factorBlockValue).prod) = 79302919123 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_7
      · exact prime_oneHundredFourteenDH_29
      · exact prime_oneHundredFourteenDH_139
      · exact prime_oneHundredFourteenDH_193
      · exact prime_oneHundredFourteenDH_809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 79302919123) ^ 39651459561 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 79302919123) ^ 26434306374 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 79302919123) ^ 11328988446 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 79302919123) ^ 2734583418 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 79302919123) ^ 570524598 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 79302919123) ^ 410895954 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 79302919123) ^ 98025858 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_80173913761 : Nat.Prime 80173913761 := by
  apply lucas_primality 80173913761 (17 : ZMod 80173913761)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (5, 1), (55676329, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (5, 1), (55676329, 1)] : List FactorBlock).map factorBlockValue).prod) = 80173913761 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_5
      · exact prime_oneHundredFourteenDH_55676329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 80173913761) ^ 40086956880 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (17 : ZMod 80173913761) ^ 26724637920 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (17 : ZMod 80173913761) ^ 16034782752 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (17 : ZMod 80173913761) ^ 1440 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_82057035997 : Nat.Prime 82057035997 := by
  apply lucas_primality 82057035997 (2 : ZMod 82057035997)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (13, 1), (109, 1), (1608583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (13, 1), (109, 1), (1608583, 1)] : List FactorBlock).map factorBlockValue).prod) = 82057035997 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_13
      · exact prime_oneHundredFourteenDH_109
      · exact prime_oneHundredFourteenDH_1608583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 82057035997) ^ 41028517998 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 82057035997) ^ 27352345332 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 82057035997) ^ 6312079692 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 82057035997) ^ 752816844 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 82057035997) ^ 51012 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_88631475817 : Nat.Prime 88631475817 := by
  apply lucas_primality 88631475817 (5 : ZMod 88631475817)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 1), (43, 1), (67, 1), (151, 1), (653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 1), (43, 1), (67, 1), (151, 1), (653, 1)] : List FactorBlock).map factorBlockValue).prod) = 88631475817 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_13
      · exact prime_oneHundredFourteenDH_43
      · exact prime_oneHundredFourteenDH_67
      · exact prime_oneHundredFourteenDH_151
      · exact prime_oneHundredFourteenDH_653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 88631475817) ^ 44315737908 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (5 : ZMod 88631475817) ^ 29543825272 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (5 : ZMod 88631475817) ^ 6817805832 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (5 : ZMod 88631475817) ^ 2061197112 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (5 : ZMod 88631475817) ^ 1322857848 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (5 : ZMod 88631475817) ^ 586963416 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (5 : ZMod 88631475817) ^ 135729672 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_98895963457 : Nat.Prime 98895963457 := by
  apply lucas_primality 98895963457 (5 : ZMod 98895963457)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (83, 1), (2068607, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (83, 1), (2068607, 1)] : List FactorBlock).map factorBlockValue).prod) = 98895963457 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_83
      · exact prime_oneHundredFourteenDH_2068607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 98895963457) ^ 49447981728 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (5 : ZMod 98895963457) ^ 32965321152 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (5 : ZMod 98895963457) ^ 1191517632 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (5 : ZMod 98895963457) ^ 47808 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_99674756429 : Nat.Prime 99674756429 := by
  apply lucas_primality 99674756429 (2 : ZMod 99674756429)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (19, 1), (100885381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (19, 1), (100885381, 1)] : List FactorBlock).map factorBlockValue).prod) = 99674756429 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_13
      · exact prime_oneHundredFourteenDH_19
      · exact prime_oneHundredFourteenDH_100885381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 99674756429) ^ 49837378214 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 99674756429) ^ 7667288956 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 99674756429) ^ 5246039812 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 99674756429) ^ 988 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_103637575981 : Nat.Prime 103637575981 := by
  apply lucas_primality 103637575981 (2 : ZMod 103637575981)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 1), (191921437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 1), (191921437, 1)] : List FactorBlock).map factorBlockValue).prod) = 103637575981 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_5
      · exact prime_oneHundredFourteenDH_191921437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 103637575981) ^ 51818787990 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 103637575981) ^ 34545858660 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 103637575981) ^ 20727515196 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 103637575981) ^ 540 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_107202114853 : Nat.Prime 107202114853 := by
  apply lucas_primality 107202114853 (5 : ZMod 107202114853)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (17, 1), (263, 1), (397, 1), (719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (17, 1), (263, 1), (397, 1), (719, 1)] : List FactorBlock).map factorBlockValue).prod) = 107202114853 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_7
      · exact prime_oneHundredFourteenDH_17
      · exact prime_oneHundredFourteenDH_263
      · exact prime_oneHundredFourteenDH_397
      · exact prime_oneHundredFourteenDH_719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 107202114853) ^ 53601057426 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (5 : ZMod 107202114853) ^ 35734038284 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (5 : ZMod 107202114853) ^ 15314587836 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (5 : ZMod 107202114853) ^ 6306006756 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (5 : ZMod 107202114853) ^ 407612604 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (5 : ZMod 107202114853) ^ 270030516 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (5 : ZMod 107202114853) ^ 149098908 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_118356756277 : Nat.Prime 118356756277 := by
  apply lucas_primality 118356756277 (2 : ZMod 118356756277)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (896642093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (896642093, 1)] : List FactorBlock).map factorBlockValue).prod) = 118356756277 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_11
      · exact prime_oneHundredFourteenDH_896642093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 118356756277) ^ 59178378138 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 118356756277) ^ 39452252092 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 118356756277) ^ 10759705116 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 118356756277) ^ 132 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_121607020321 : Nat.Prime 121607020321 := by
  apply lucas_primality 121607020321 (7 : ZMod 121607020321)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 1), (43, 1), (5891813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 1), (43, 1), (5891813, 1)] : List FactorBlock).map factorBlockValue).prod) = 121607020321 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_5
      · exact prime_oneHundredFourteenDH_43
      · exact prime_oneHundredFourteenDH_5891813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 121607020321) ^ 60803510160 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (7 : ZMod 121607020321) ^ 40535673440 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (7 : ZMod 121607020321) ^ 24321404064 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (7 : ZMod 121607020321) ^ 2828070240 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (7 : ZMod 121607020321) ^ 20640 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_142480273139 : Nat.Prime 142480273139 := by
  apply lucas_primality 142480273139 (2 : ZMod 142480273139)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (211, 1), (1093, 1), (44129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (211, 1), (1093, 1), (44129, 1)] : List FactorBlock).map factorBlockValue).prod) = 142480273139 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_7
      · exact prime_oneHundredFourteenDH_211
      · exact prime_oneHundredFourteenDH_1093
      · exact prime_oneHundredFourteenDH_44129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 142480273139) ^ 71240136569 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 142480273139) ^ 20354324734 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 142480273139) ^ 675261958 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 142480273139) ^ 130357066 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 142480273139) ^ 3228722 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_150870450811 : Nat.Prime 150870450811 := by
  apply lucas_primality 150870450811 (3 : ZMod 150870450811)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (5029015027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (5029015027, 1)] : List FactorBlock).map factorBlockValue).prod) = 150870450811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_5
      · exact prime_oneHundredFourteenDH_5029015027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 150870450811) ^ 75435225405 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 150870450811) ^ 50290150270 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 150870450811) ^ 30174090162 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 150870450811) ^ 30 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_229090782587 : Nat.Prime 229090782587 := by
  apply lucas_primality 229090782587 (2 : ZMod 229090782587)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1327, 1), (86319059, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1327, 1), (86319059, 1)] : List FactorBlock).map factorBlockValue).prod) = 229090782587 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_1327
      · exact prime_oneHundredFourteenDH_86319059
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 229090782587) ^ 114545391293 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 229090782587) ^ 172638118 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 229090782587) ^ 2654 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_243364641461 : Nat.Prime 243364641461 := by
  apply lucas_primality 243364641461 (2 : ZMod 243364641461)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (19, 1), (640433267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (19, 1), (640433267, 1)] : List FactorBlock).map factorBlockValue).prod) = 243364641461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_5
      · exact prime_oneHundredFourteenDH_19
      · exact prime_oneHundredFourteenDH_640433267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 243364641461) ^ 121682320730 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 243364641461) ^ 48672928292 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 243364641461) ^ 12808665340 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 243364641461) ^ 380 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_249263846203 : Nat.Prime 249263846203 := by
  apply lucas_primality 249263846203 (3 : ZMod 249263846203)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (5934853481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (5934853481, 1)] : List FactorBlock).map factorBlockValue).prod) = 249263846203 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_7
      · exact prime_oneHundredFourteenDH_5934853481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 249263846203) ^ 124631923101 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 249263846203) ^ 83087948734 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 249263846203) ^ 35609120886 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 249263846203) ^ 42 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_289625811203 : Nat.Prime 289625811203 := by
  apply lucas_primality 289625811203 (2 : ZMod 289625811203)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13, 1), (23, 1), (29, 1), (1361, 1), (1753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13, 1), (23, 1), (29, 1), (1361, 1), (1753, 1)] : List FactorBlock).map factorBlockValue).prod) = 289625811203 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_7
      · exact prime_oneHundredFourteenDH_13
      · exact prime_oneHundredFourteenDH_23
      · exact prime_oneHundredFourteenDH_29
      · exact prime_oneHundredFourteenDH_1361
      · exact prime_oneHundredFourteenDH_1753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 289625811203) ^ 144812905601 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 289625811203) ^ 41375115886 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 289625811203) ^ 22278908554 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 289625811203) ^ 12592426574 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 289625811203) ^ 9987096938 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 289625811203) ^ 212803682 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 289625811203) ^ 165217234 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_354533931209 : Nat.Prime 354533931209 := by
  apply lucas_primality 354533931209 (3 : ZMod 354533931209)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (155723, 1), (284587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (155723, 1), (284587, 1)] : List FactorBlock).map factorBlockValue).prod) = 354533931209 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_155723
      · exact prime_oneHundredFourteenDH_284587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 354533931209) ^ 177266965604 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 354533931209) ^ 2276696 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 354533931209) ^ 1245784 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_357488612183 : Nat.Prime 357488612183 := by
  apply lucas_primality 357488612183 (5 : ZMod 357488612183)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (197, 1), (601, 1), (116131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (197, 1), (601, 1), (116131, 1)] : List FactorBlock).map factorBlockValue).prod) = 357488612183 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_13
      · exact prime_oneHundredFourteenDH_197
      · exact prime_oneHundredFourteenDH_601
      · exact prime_oneHundredFourteenDH_116131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 357488612183) ^ 178744306091 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (5 : ZMod 357488612183) ^ 27499124014 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (5 : ZMod 357488612183) ^ 1814663006 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (5 : ZMod 357488612183) ^ 594822982 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (5 : ZMod 357488612183) ^ 3078322 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_390524800313 : Nat.Prime 390524800313 := by
  apply lucas_primality 390524800313 (3 : ZMod 390524800313)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (23, 1), (743, 1), (2856551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (23, 1), (743, 1), (2856551, 1)] : List FactorBlock).map factorBlockValue).prod) = 390524800313 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_23
      · exact prime_oneHundredFourteenDH_743
      · exact prime_oneHundredFourteenDH_2856551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 390524800313) ^ 195262400156 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 390524800313) ^ 16979339144 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 390524800313) ^ 525605384 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 390524800313) ^ 136712 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_419501118209 : Nat.Prime 419501118209 := by
  apply lucas_primality 419501118209 (3 : ZMod 419501118209)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (109, 1), (2819, 1), (5333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (109, 1), (2819, 1), (5333, 1)] : List FactorBlock).map factorBlockValue).prod) = 419501118209 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_109
      · exact prime_oneHundredFourteenDH_2819
      · exact prime_oneHundredFourteenDH_5333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 419501118209) ^ 209750559104 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 419501118209) ^ 3848634112 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 419501118209) ^ 148812032 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 419501118209) ^ 78661376 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_438698392081 : Nat.Prime 438698392081 := by
  apply lucas_primality 438698392081 (28 : ZMod 438698392081)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (13, 1), (1187, 1), (118457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (13, 1), (1187, 1), (118457, 1)] : List FactorBlock).map factorBlockValue).prod) = 438698392081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_5
      · exact prime_oneHundredFourteenDH_13
      · exact prime_oneHundredFourteenDH_1187
      · exact prime_oneHundredFourteenDH_118457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (28 : ZMod 438698392081) ^ 219349196040 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (28 : ZMod 438698392081) ^ 146232797360 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (28 : ZMod 438698392081) ^ 87739678416 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (28 : ZMod 438698392081) ^ 33746030160 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (28 : ZMod 438698392081) ^ 369585840 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (28 : ZMod 438698392081) ^ 3703440 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_472986682277 : Nat.Prime 472986682277 := by
  apply lucas_primality 472986682277 (2 : ZMod 472986682277)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (113, 1), (269, 1), (659, 1), (5903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (113, 1), (269, 1), (659, 1), (5903, 1)] : List FactorBlock).map factorBlockValue).prod) = 472986682277 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_113
      · exact prime_oneHundredFourteenDH_269
      · exact prime_oneHundredFourteenDH_659
      · exact prime_oneHundredFourteenDH_5903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 472986682277) ^ 236493341138 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 472986682277) ^ 4185722852 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 472986682277) ^ 1758314804 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 472986682277) ^ 717733964 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 472986682277) ^ 80126492 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_496473482581 : Nat.Prime 496473482581 := by
  apply lucas_primality 496473482581 (7 : ZMod 496473482581)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (283, 1), (823, 1), (35527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (283, 1), (823, 1), (35527, 1)] : List FactorBlock).map factorBlockValue).prod) = 496473482581 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_5
      · exact prime_oneHundredFourteenDH_283
      · exact prime_oneHundredFourteenDH_823
      · exact prime_oneHundredFourteenDH_35527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 496473482581) ^ 248236741290 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (7 : ZMod 496473482581) ^ 165491160860 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (7 : ZMod 496473482581) ^ 99294696516 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (7 : ZMod 496473482581) ^ 1754323260 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (7 : ZMod 496473482581) ^ 603248460 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (7 : ZMod 496473482581) ^ 13974540 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_521791248119 : Nat.Prime 521791248119 := by
  apply lucas_primality 521791248119 (7 : ZMod 521791248119)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (5324400491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (5324400491, 1)] : List FactorBlock).map factorBlockValue).prod) = 521791248119 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_7
      · exact prime_oneHundredFourteenDH_5324400491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 521791248119) ^ 260895624059 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (7 : ZMod 521791248119) ^ 74541606874 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (7 : ZMod 521791248119) ^ 98 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_526203192223 : Nat.Prime 526203192223 := by
  apply lucas_primality 526203192223 (3 : ZMod 526203192223)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (263, 1), (111154033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (263, 1), (111154033, 1)] : List FactorBlock).map factorBlockValue).prod) = 526203192223 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_263
      · exact prime_oneHundredFourteenDH_111154033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 526203192223) ^ 263101596111 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 526203192223) ^ 175401064074 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 526203192223) ^ 2000772594 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 526203192223) ^ 4734 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_676699753217 : Nat.Prime 676699753217 := by
  apply lucas_primality 676699753217 (3 : ZMod 676699753217)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (53, 1), (197, 1), (409, 1), (619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (53, 1), (197, 1), (409, 1), (619, 1)] : List FactorBlock).map factorBlockValue).prod) = 676699753217 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_53
      · exact prime_oneHundredFourteenDH_197
      · exact prime_oneHundredFourteenDH_409
      · exact prime_oneHundredFourteenDH_619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 676699753217) ^ 338349876608 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 676699753217) ^ 12767919872 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 676699753217) ^ 3435024128 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 676699753217) ^ 1654522624 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 676699753217) ^ 1093214464 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_697346079103 : Nat.Prime 697346079103 := by
  apply lucas_primality 697346079103 (3 : ZMod 697346079103)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (71, 1), (11689, 1), (46681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (71, 1), (11689, 1), (46681, 1)] : List FactorBlock).map factorBlockValue).prod) = 697346079103 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_71
      · exact prime_oneHundredFourteenDH_11689
      · exact prime_oneHundredFourteenDH_46681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 697346079103) ^ 348673039551 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 697346079103) ^ 232448693034 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 697346079103) ^ 9821775762 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 697346079103) ^ 59658318 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 697346079103) ^ 14938542 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_776900746001 : Nat.Prime 776900746001 := by
  apply lucas_primality 776900746001 (3 : ZMod 776900746001)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 3), (139, 1), (2794607, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 3), (139, 1), (2794607, 1)] : List FactorBlock).map factorBlockValue).prod) = 776900746001 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_5
      · exact prime_oneHundredFourteenDH_139
      · exact prime_oneHundredFourteenDH_2794607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 776900746001) ^ 388450373000 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 776900746001) ^ 155380149200 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 776900746001) ^ 5589214000 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 776900746001) ^ 278000 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_781049600627 : Nat.Prime 781049600627 := by
  apply lucas_primality 781049600627 (2 : ZMod 781049600627)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (390524800313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (390524800313, 1)] : List FactorBlock).map factorBlockValue).prod) = 781049600627 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_390524800313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 781049600627) ^ 390524800313 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 781049600627) ^ 2 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_812260148269 : Nat.Prime 812260148269 := by
  apply lucas_primality 812260148269 (2 : ZMod 812260148269)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (257, 1), (3347, 1), (78691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (257, 1), (3347, 1), (78691, 1)] : List FactorBlock).map factorBlockValue).prod) = 812260148269 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_257
      · exact prime_oneHundredFourteenDH_3347
      · exact prime_oneHundredFourteenDH_78691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 812260148269) ^ 406130074134 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 812260148269) ^ 270753382756 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 812260148269) ^ 3160545324 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 812260148269) ^ 242683044 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 812260148269) ^ 10322148 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_1072021148531 : Nat.Prime 1072021148531 := by
  apply lucas_primality 1072021148531 (2 : ZMod 1072021148531)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (107202114853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (107202114853, 1)] : List FactorBlock).map factorBlockValue).prod) = 1072021148531 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_5
      · exact prime_oneHundredFourteenDH_107202114853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1072021148531) ^ 536010574265 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1072021148531) ^ 214404229706 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1072021148531) ^ 10 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_1343585305739 : Nat.Prime 1343585305739 := by
  apply lucas_primality 1343585305739 (2 : ZMod 1343585305739)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (53, 1), (975025621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (53, 1), (975025621, 1)] : List FactorBlock).map factorBlockValue).prod) = 1343585305739 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_13
      · exact prime_oneHundredFourteenDH_53
      · exact prime_oneHundredFourteenDH_975025621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1343585305739) ^ 671792652869 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1343585305739) ^ 103352715826 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1343585305739) ^ 25350666146 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1343585305739) ^ 1378 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_1443130447699 : Nat.Prime 1443130447699 := by
  apply lucas_primality 1443130447699 (2 : ZMod 1443130447699)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (80173913761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (80173913761, 1)] : List FactorBlock).map factorBlockValue).prod) = 1443130447699 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_80173913761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1443130447699) ^ 721565223849 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1443130447699) ^ 481043482566 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1443130447699) ^ 18 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_1611100927811 : Nat.Prime 1611100927811 := by
  apply lucas_primality 1611100927811 (2 : ZMod 1611100927811)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (14646372071, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (14646372071, 1)] : List FactorBlock).map factorBlockValue).prod) = 1611100927811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_5
      · exact prime_oneHundredFourteenDH_11
      · exact prime_oneHundredFourteenDH_14646372071
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1611100927811) ^ 805550463905 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1611100927811) ^ 322220185562 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1611100927811) ^ 146463720710 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1611100927811) ^ 110 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_3639353065301 : Nat.Prime 3639353065301 := by
  apply lucas_primality 3639353065301 (2 : ZMod 3639353065301)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (36393530653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (36393530653, 1)] : List FactorBlock).map factorBlockValue).prod) = 3639353065301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_5
      · exact prime_oneHundredFourteenDH_36393530653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3639353065301) ^ 1819676532650 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 3639353065301) ^ 727870613060 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 3639353065301) ^ 100 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_3899136783133 : Nat.Prime 3899136783133 := by
  apply lucas_primality 3899136783133 (13 : ZMod 3899136783133)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (19, 1), (83, 1), (181, 1), (379451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (19, 1), (83, 1), (181, 1), (379451, 1)] : List FactorBlock).map factorBlockValue).prod) = 3899136783133 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_19
      · exact prime_oneHundredFourteenDH_83
      · exact prime_oneHundredFourteenDH_181
      · exact prime_oneHundredFourteenDH_379451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 3899136783133) ^ 1949568391566 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (13 : ZMod 3899136783133) ^ 1299712261044 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (13 : ZMod 3899136783133) ^ 205217725428 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (13 : ZMod 3899136783133) ^ 46977551604 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (13 : ZMod 3899136783133) ^ 21542192172 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (13 : ZMod 3899136783133) ^ 10275732 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_9026940933193 : Nat.Prime 9026940933193 := by
  apply lucas_primality 9026940933193 (15 : ZMod 9026940933193)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (13, 1), (4133214713, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (13, 1), (4133214713, 1)] : List FactorBlock).map factorBlockValue).prod) = 9026940933193 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_7
      · exact prime_oneHundredFourteenDH_13
      · exact prime_oneHundredFourteenDH_4133214713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 9026940933193) ^ 4513470466596 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (15 : ZMod 9026940933193) ^ 3008980311064 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (15 : ZMod 9026940933193) ^ 1289562990456 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (15 : ZMod 9026940933193) ^ 694380071784 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (15 : ZMod 9026940933193) ^ 2184 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_10403988322733 : Nat.Prime 10403988322733 := by
  apply lucas_primality 10403988322733 (2 : ZMod 10403988322733)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1303, 1), (2383, 1), (837667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1303, 1), (2383, 1), (837667, 1)] : List FactorBlock).map factorBlockValue).prod) = 10403988322733 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_1303
      · exact prime_oneHundredFourteenDH_2383
      · exact prime_oneHundredFourteenDH_837667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 10403988322733) ^ 5201994161366 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 10403988322733) ^ 7984641844 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 10403988322733) ^ 4365920404 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 10403988322733) ^ 12420196 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_12215682868351 : Nat.Prime 12215682868351 := by
  apply lucas_primality 12215682868351 (6 : ZMod 12215682868351)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (13, 2), (23, 1), (20951347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (13, 2), (23, 1), (20951347, 1)] : List FactorBlock).map factorBlockValue).prod) = 12215682868351 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_5
      · exact prime_oneHundredFourteenDH_13
      · exact prime_oneHundredFourteenDH_23
      · exact prime_oneHundredFourteenDH_20951347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 12215682868351) ^ 6107841434175 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (6 : ZMod 12215682868351) ^ 4071894289450 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (6 : ZMod 12215682868351) ^ 2443136573670 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (6 : ZMod 12215682868351) ^ 939667912950 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (6 : ZMod 12215682868351) ^ 531116646450 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (6 : ZMod 12215682868351) ^ 583050 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_13071266057611 : Nat.Prime 13071266057611 := by
  apply lucas_primality 13071266057611 (3 : ZMod 13071266057611)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (457, 1), (317803697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (457, 1), (317803697, 1)] : List FactorBlock).map factorBlockValue).prod) = 13071266057611 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_5
      · exact prime_oneHundredFourteenDH_457
      · exact prime_oneHundredFourteenDH_317803697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 13071266057611) ^ 6535633028805 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 13071266057611) ^ 4357088685870 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 13071266057611) ^ 2614253211522 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 13071266057611) ^ 28602332730 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 13071266057611) ^ 41130 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_13971226936099 : Nat.Prime 13971226936099 := by
  apply lucas_primality 13971226936099 (2 : ZMod 13971226936099)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (21617, 1), (6336347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (21617, 1), (6336347, 1)] : List FactorBlock).map factorBlockValue).prod) = 13971226936099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_17
      · exact prime_oneHundredFourteenDH_21617
      · exact prime_oneHundredFourteenDH_6336347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 13971226936099) ^ 6985613468049 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 13971226936099) ^ 4657075645366 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 13971226936099) ^ 821836878594 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 13971226936099) ^ 646307394 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 13971226936099) ^ 2204934 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_13995766681093 : Nat.Prime 13995766681093 := by
  apply lucas_primality 13995766681093 (2 : ZMod 13995766681093)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (55538756671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (55538756671, 1)] : List FactorBlock).map factorBlockValue).prod) = 13995766681093 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_7
      · exact prime_oneHundredFourteenDH_55538756671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 13995766681093) ^ 6997883340546 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 13995766681093) ^ 4665255560364 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 13995766681093) ^ 1999395240156 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 13995766681093) ^ 252 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_14083911874787 : Nat.Prime 14083911874787 := by
  apply lucas_primality 14083911874787 (2 : ZMod 14083911874787)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (61, 1), (733, 1), (12114797, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (61, 1), (733, 1), (12114797, 1)] : List FactorBlock).map factorBlockValue).prod) = 14083911874787 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_13
      · exact prime_oneHundredFourteenDH_61
      · exact prime_oneHundredFourteenDH_733
      · exact prime_oneHundredFourteenDH_12114797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 14083911874787) ^ 7041955937393 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 14083911874787) ^ 1083377836522 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 14083911874787) ^ 230883801226 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 14083911874787) ^ 19214068042 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 14083911874787) ^ 1162538 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_14334243066613 : Nat.Prime 14334243066613 := by
  apply lucas_primality 14334243066613 (2 : ZMod 14334243066613)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (7, 2), (2708662711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (7, 2), (2708662711, 1)] : List FactorBlock).map factorBlockValue).prod) = 14334243066613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_7
      · exact prime_oneHundredFourteenDH_2708662711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 14334243066613) ^ 7167121533306 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 14334243066613) ^ 4778081022204 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 14334243066613) ^ 2047749009516 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 14334243066613) ^ 5292 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_15875148888199 : Nat.Prime 15875148888199 := by
  apply lucas_primality 15875148888199 (19 : ZMod 15875148888199)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (131, 2), (157, 1), (327343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (131, 2), (157, 1), (327343, 1)] : List FactorBlock).map factorBlockValue).prod) = 15875148888199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_131
      · exact prime_oneHundredFourteenDH_157
      · exact prime_oneHundredFourteenDH_327343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 15875148888199) ^ 7937574444099 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (19 : ZMod 15875148888199) ^ 5291716296066 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (19 : ZMod 15875148888199) ^ 121184342658 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (19 : ZMod 15875148888199) ^ 101115598014 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (19 : ZMod 15875148888199) ^ 48496986 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_16783876450529 : Nat.Prime 16783876450529 := by
  apply lucas_primality 16783876450529 (3 : ZMod 16783876450529)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (11, 1), (47681467189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (11, 1), (47681467189, 1)] : List FactorBlock).map factorBlockValue).prod) = 16783876450529 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_11
      · exact prime_oneHundredFourteenDH_47681467189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 16783876450529) ^ 8391938225264 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 16783876450529) ^ 1525806950048 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 16783876450529) ^ 352 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_24919378088863 : Nat.Prime 24919378088863 := by
  apply lucas_primality 24919378088863 (3 : ZMod 24919378088863)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (553277, 1), (7506601, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (553277, 1), (7506601, 1)] : List FactorBlock).map factorBlockValue).prod) = 24919378088863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_553277
      · exact prime_oneHundredFourteenDH_7506601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 24919378088863) ^ 12459689044431 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 24919378088863) ^ 8306459362954 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 24919378088863) ^ 45039606 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 24919378088863) ^ 3319662 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_26255962099621 : Nat.Prime 26255962099621 := by
  apply lucas_primality 26255962099621 (6 : ZMod 26255962099621)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (11, 1), (38351, 1), (345769, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (11, 1), (38351, 1), (345769, 1)] : List FactorBlock).map factorBlockValue).prod) = 26255962099621 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_5
      · exact prime_oneHundredFourteenDH_11
      · exact prime_oneHundredFourteenDH_38351
      · exact prime_oneHundredFourteenDH_345769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 26255962099621) ^ 13127981049810 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (6 : ZMod 26255962099621) ^ 8751987366540 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (6 : ZMod 26255962099621) ^ 5251192419924 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (6 : ZMod 26255962099621) ^ 2386905645420 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (6 : ZMod 26255962099621) ^ 684622620 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (6 : ZMod 26255962099621) ^ 75934980 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_28899454756129 : Nat.Prime 28899454756129 := by
  apply lucas_primality 28899454756129 (7 : ZMod 28899454756129)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (11, 1), (3449, 1), (7934737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (11, 1), (3449, 1), (7934737, 1)] : List FactorBlock).map factorBlockValue).prod) = 28899454756129 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_11
      · exact prime_oneHundredFourteenDH_3449
      · exact prime_oneHundredFourteenDH_7934737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 28899454756129) ^ 14449727378064 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (7 : ZMod 28899454756129) ^ 9633151585376 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (7 : ZMod 28899454756129) ^ 2627223159648 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (7 : ZMod 28899454756129) ^ 8379082272 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (7 : ZMod 28899454756129) ^ 3642144 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_35481804872093 : Nat.Prime 35481804872093 := by
  apply lucas_primality 35481804872093 (3 : ZMod 35481804872093)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (521791248119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (521791248119, 1)] : List FactorBlock).map factorBlockValue).prod) = 35481804872093 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_17
      · exact prime_oneHundredFourteenDH_521791248119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 35481804872093) ^ 17740902436046 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 35481804872093) ^ 2087164992476 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 35481804872093) ^ 68 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_43689666467129 : Nat.Prime 43689666467129 := by
  apply lucas_primality 43689666467129 (3 : ZMod 43689666467129)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (496473482581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (496473482581, 1)] : List FactorBlock).map factorBlockValue).prod) = 43689666467129 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_11
      · exact prime_oneHundredFourteenDH_496473482581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 43689666467129) ^ 21844833233564 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 43689666467129) ^ 3971787860648 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 43689666467129) ^ 88 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_44443611821879 : Nat.Prime 44443611821879 := by
  apply lucas_primality 44443611821879 (7 : ZMod 44443611821879)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (97, 1), (229090782587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (97, 1), (229090782587, 1)] : List FactorBlock).map factorBlockValue).prod) = 44443611821879 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_97
      · exact prime_oneHundredFourteenDH_229090782587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 44443611821879) ^ 22221805910939 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (7 : ZMod 44443611821879) ^ 458181565174 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (7 : ZMod 44443611821879) ^ 194 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_45752552594669 : Nat.Prime 45752552594669 := by
  apply lucas_primality 45752552594669 (2 : ZMod 45752552594669)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (47, 1), (243364641461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (47, 1), (243364641461, 1)] : List FactorBlock).map factorBlockValue).prod) = 45752552594669 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_47
      · exact prime_oneHundredFourteenDH_243364641461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 45752552594669) ^ 22876276297334 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 45752552594669) ^ 973458565844 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 45752552594669) ^ 188 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_70753820440643 : Nat.Prime 70753820440643 := by
  apply lucas_primality 70753820440643 (2 : ZMod 70753820440643)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (431, 1), (54833, 1), (1496927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (431, 1), (54833, 1), (1496927, 1)] : List FactorBlock).map factorBlockValue).prod) = 70753820440643 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_431
      · exact prime_oneHundredFourteenDH_54833
      · exact prime_oneHundredFourteenDH_1496927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 70753820440643) ^ 35376910220321 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 70753820440643) ^ 164161996382 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 70753820440643) ^ 1290351074 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 70753820440643) ^ 47266046 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_80306230930837 : Nat.Prime 80306230930837 := by
  apply lucas_primality 80306230930837 (5 : ZMod 80306230930837)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (1489, 1), (15467, 1), (17093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (1489, 1), (15467, 1), (17093, 1)] : List FactorBlock).map factorBlockValue).prod) = 80306230930837 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_17
      · exact prime_oneHundredFourteenDH_1489
      · exact prime_oneHundredFourteenDH_15467
      · exact prime_oneHundredFourteenDH_17093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 80306230930837) ^ 40153115465418 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (5 : ZMod 80306230930837) ^ 26768743643612 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (5 : ZMod 80306230930837) ^ 4723895937108 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (5 : ZMod 80306230930837) ^ 53932995924 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (5 : ZMod 80306230930837) ^ 5192101308 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (5 : ZMod 80306230930837) ^ 4698194052 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_89272272147727 : Nat.Prime 89272272147727 := by
  apply lucas_primality 89272272147727 (3 : ZMod 89272272147727)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (113, 1), (373, 1), (3739, 1), (4969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (113, 1), (373, 1), (3739, 1), (4969, 1)] : List FactorBlock).map factorBlockValue).prod) = 89272272147727 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_19
      · exact prime_oneHundredFourteenDH_113
      · exact prime_oneHundredFourteenDH_373
      · exact prime_oneHundredFourteenDH_3739
      · exact prime_oneHundredFourteenDH_4969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 89272272147727) ^ 44636136073863 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 89272272147727) ^ 29757424049242 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 89272272147727) ^ 4698540639354 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 89272272147727) ^ 790020107502 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 89272272147727) ^ 239335850262 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 89272272147727) ^ 23875975434 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 89272272147727) ^ 17965842654 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_93234650302289 : Nat.Prime 93234650302289 := by
  apply lucas_primality 93234650302289 (3 : ZMod 93234650302289)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (11, 1), (107, 1), (45503, 1), (108803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (11, 1), (107, 1), (45503, 1), (108803, 1)] : List FactorBlock).map factorBlockValue).prod) = 93234650302289 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_11
      · exact prime_oneHundredFourteenDH_107
      · exact prime_oneHundredFourteenDH_45503
      · exact prime_oneHundredFourteenDH_108803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 93234650302289) ^ 46617325151144 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 93234650302289) ^ 8475877300208 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 93234650302289) ^ 871351871984 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 93234650302289) ^ 2048978096 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 93234650302289) ^ 856912496 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_98934870722059 : Nat.Prime 98934870722059 := by
  apply lucas_primality 98934870722059 (11 : ZMod 98934870722059)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (89, 1), (8822442547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (89, 1), (8822442547, 1)] : List FactorBlock).map factorBlockValue).prod) = 98934870722059 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_7
      · exact prime_oneHundredFourteenDH_89
      · exact prime_oneHundredFourteenDH_8822442547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 98934870722059) ^ 49467435361029 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (11 : ZMod 98934870722059) ^ 32978290240686 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (11 : ZMod 98934870722059) ^ 14133552960294 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (11 : ZMod 98934870722059) ^ 1111627760922 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (11 : ZMod 98934870722059) ^ 11214 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_107173596754699 : Nat.Prime 107173596754699 := by
  apply lucas_primality 107173596754699 (2 : ZMod 107173596754699)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1117, 1), (15991285699, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1117, 1), (15991285699, 1)] : List FactorBlock).map factorBlockValue).prod) = 107173596754699 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_1117
      · exact prime_oneHundredFourteenDH_15991285699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 107173596754699) ^ 53586798377349 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 107173596754699) ^ 35724532251566 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 107173596754699) ^ 95947714194 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 107173596754699) ^ 6702 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_112520467429637 : Nat.Prime 112520467429637 := by
  apply lucas_primality 112520467429637 (2 : ZMod 112520467429637)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (59, 1), (107, 1), (157, 1), (311, 1), (13037, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (59, 1), (107, 1), (157, 1), (311, 1), (13037, 1)] : List FactorBlock).map factorBlockValue).prod) = 112520467429637 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_7
      · exact prime_oneHundredFourteenDH_59
      · exact prime_oneHundredFourteenDH_107
      · exact prime_oneHundredFourteenDH_157
      · exact prime_oneHundredFourteenDH_311
      · exact prime_oneHundredFourteenDH_13037
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 112520467429637) ^ 56260233714818 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 112520467429637) ^ 16074352489948 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 112520467429637) ^ 1907126566604 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 112520467429637) ^ 1051593153548 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 112520467429637) ^ 716690875348 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 112520467429637) ^ 361802146076 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 112520467429637) ^ 8630855828 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_184306195621687 : Nat.Prime 184306195621687 := by
  apply lucas_primality 184306195621687 (3 : ZMod 184306195621687)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (53003, 1), (579546427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (53003, 1), (579546427, 1)] : List FactorBlock).map factorBlockValue).prod) = 184306195621687 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_53003
      · exact prime_oneHundredFourteenDH_579546427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 184306195621687) ^ 92153097810843 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 184306195621687) ^ 61435398540562 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 184306195621687) ^ 3477278562 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 184306195621687) ^ 318018 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_210815417418539 : Nat.Prime 210815417418539 := by
  apply lucas_primality 210815417418539 (2 : ZMod 210815417418539)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (359, 1), (8779, 1), (33445129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (359, 1), (8779, 1), (33445129, 1)] : List FactorBlock).map factorBlockValue).prod) = 210815417418539 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_359
      · exact prime_oneHundredFourteenDH_8779
      · exact prime_oneHundredFourteenDH_33445129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 210815417418539) ^ 105407708709269 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 210815417418539) ^ 587229574982 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 210815417418539) ^ 24013602622 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 210815417418539) ^ 6303322 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_312984363615887 : Nat.Prime 312984363615887 := by
  apply lucas_primality 312984363615887 (5 : ZMod 312984363615887)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 1), (3639353065301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 1), (3639353065301, 1)] : List FactorBlock).map factorBlockValue).prod) = 312984363615887 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_43
      · exact prime_oneHundredFourteenDH_3639353065301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 312984363615887) ^ 156492181807943 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (5 : ZMod 312984363615887) ^ 7278706130602 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (5 : ZMod 312984363615887) ^ 86 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_366020420757353 : Nat.Prime 366020420757353 := by
  apply lucas_primality 366020420757353 (3 : ZMod 366020420757353)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (45752552594669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (45752552594669, 1)] : List FactorBlock).map factorBlockValue).prod) = 366020420757353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_45752552594669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 366020420757353) ^ 183010210378676 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 366020420757353) ^ 8 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_426591041781631 : Nat.Prime 426591041781631 := by
  apply lucas_primality 426591041781631 (3 : ZMod 426591041781631)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (19, 1), (47, 2), (2693, 1), (11437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (19, 1), (47, 2), (2693, 1), (11437, 1)] : List FactorBlock).map factorBlockValue).prod) = 426591041781631 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_5
      · exact prime_oneHundredFourteenDH_11
      · exact prime_oneHundredFourteenDH_19
      · exact prime_oneHundredFourteenDH_47
      · exact prime_oneHundredFourteenDH_2693
      · exact prime_oneHundredFourteenDH_11437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 426591041781631) ^ 213295520890815 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 426591041781631) ^ 142197013927210 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 426591041781631) ^ 85318208356326 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 426591041781631) ^ 38781003798330 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 426591041781631) ^ 22452160093770 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 426591041781631) ^ 9076405144290 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 426591041781631) ^ 158407367910 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 426591041781631) ^ 37299207990 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_487995060087097 : Nat.Prime 487995060087097 := by
  apply lucas_primality 487995060087097 (5 : ZMod 487995060087097)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (2591, 1), (7847598419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (2591, 1), (7847598419, 1)] : List FactorBlock).map factorBlockValue).prod) = 487995060087097 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_2591
      · exact prime_oneHundredFourteenDH_7847598419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 487995060087097) ^ 243997530043548 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (5 : ZMod 487995060087097) ^ 162665020029032 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (5 : ZMod 487995060087097) ^ 188342362056 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (5 : ZMod 487995060087097) ^ 62184 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_539588349053437 : Nat.Prime 539588349053437 := by
  apply lucas_primality 539588349053437 (5 : ZMod 539588349053437)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (688013, 1), (65355881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (688013, 1), (65355881, 1)] : List FactorBlock).map factorBlockValue).prod) = 539588349053437 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_688013
      · exact prime_oneHundredFourteenDH_65355881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 539588349053437) ^ 269794174526718 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (5 : ZMod 539588349053437) ^ 179862783017812 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (5 : ZMod 539588349053437) ^ 784270572 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (5 : ZMod 539588349053437) ^ 8256156 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_575990512578109 : Nat.Prime 575990512578109 := by
  apply lucas_primality 575990512578109 (6 : ZMod 575990512578109)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (15313, 1), (1044846631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (15313, 1), (1044846631, 1)] : List FactorBlock).map factorBlockValue).prod) = 575990512578109 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_15313
      · exact prime_oneHundredFourteenDH_1044846631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 575990512578109) ^ 287995256289054 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (6 : ZMod 575990512578109) ^ 191996837526036 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (6 : ZMod 575990512578109) ^ 37614478716 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (6 : ZMod 575990512578109) ^ 551268 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_625249011082109 : Nat.Prime 625249011082109 := by
  apply lucas_primality 625249011082109 (2 : ZMod 625249011082109)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (19, 1), (71, 1), (181, 1), (91454369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (19, 1), (71, 1), (181, 1), (91454369, 1)] : List FactorBlock).map factorBlockValue).prod) = 625249011082109 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_7
      · exact prime_oneHundredFourteenDH_19
      · exact prime_oneHundredFourteenDH_71
      · exact prime_oneHundredFourteenDH_181
      · exact prime_oneHundredFourteenDH_91454369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 625249011082109) ^ 312624505541054 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 625249011082109) ^ 89321287297444 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 625249011082109) ^ 32907842688532 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 625249011082109) ^ 8806324099748 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 625249011082109) ^ 3454414425868 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 625249011082109) ^ 6836732 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_861517452837871 : Nat.Prime 861517452837871 := by
  apply lucas_primality 861517452837871 (3 : ZMod 861517452837871)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 5), (5, 1), (354533931209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 5), (5, 1), (354533931209, 1)] : List FactorBlock).map factorBlockValue).prod) = 861517452837871 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_5
      · exact prime_oneHundredFourteenDH_354533931209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 861517452837871) ^ 430758726418935 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 861517452837871) ^ 287172484279290 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 861517452837871) ^ 172303490567574 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 861517452837871) ^ 2430 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_870684648627301 : Nat.Prime 870684648627301 := by
  apply lucas_primality 870684648627301 (2 : ZMod 870684648627301)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (13, 1), (17, 1), (13132498471, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (13, 1), (17, 1), (13132498471, 1)] : List FactorBlock).map factorBlockValue).prod) = 870684648627301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_5
      · exact prime_oneHundredFourteenDH_13
      · exact prime_oneHundredFourteenDH_17
      · exact prime_oneHundredFourteenDH_13132498471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 870684648627301) ^ 435342324313650 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 870684648627301) ^ 290228216209100 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 870684648627301) ^ 174136929725460 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 870684648627301) ^ 66975742202100 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 870684648627301) ^ 51216744036900 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 870684648627301) ^ 66300 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_949577232649231 : Nat.Prime 949577232649231 := by
  apply lucas_primality 949577232649231 (6 : ZMod 949577232649231)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (1363847, 1), (7736101, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (1363847, 1), (7736101, 1)] : List FactorBlock).map factorBlockValue).prod) = 949577232649231 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_5
      · exact prime_oneHundredFourteenDH_1363847
      · exact prime_oneHundredFourteenDH_7736101
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 949577232649231) ^ 474788616324615 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (6 : ZMod 949577232649231) ^ 316525744216410 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (6 : ZMod 949577232649231) ^ 189915446529846 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (6 : ZMod 949577232649231) ^ 696249090 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (6 : ZMod 949577232649231) ^ 122746230 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_1115331887063311 : Nat.Prime 1115331887063311 := by
  apply lucas_primality 1115331887063311 (7 : ZMod 1115331887063311)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 2), (19, 1), (39933114467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 2), (19, 1), (39933114467, 1)] : List FactorBlock).map factorBlockValue).prod) = 1115331887063311 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_5
      · exact prime_oneHundredFourteenDH_7
      · exact prime_oneHundredFourteenDH_19
      · exact prime_oneHundredFourteenDH_39933114467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1115331887063311) ^ 557665943531655 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (7 : ZMod 1115331887063311) ^ 371777295687770 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (7 : ZMod 1115331887063311) ^ 223066377412662 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (7 : ZMod 1115331887063311) ^ 159333126723330 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (7 : ZMod 1115331887063311) ^ 58701678266490 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (7 : ZMod 1115331887063311) ^ 27930 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_2062209187598081 : Nat.Prime 2062209187598081 := by
  apply lucas_primality 2062209187598081 (3 : ZMod 2062209187598081)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (5, 1), (1611100927811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (5, 1), (1611100927811, 1)] : List FactorBlock).map factorBlockValue).prod) = 2062209187598081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_5
      · exact prime_oneHundredFourteenDH_1611100927811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2062209187598081) ^ 1031104593799040 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 2062209187598081) ^ 412441837519616 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 2062209187598081) ^ 1280 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_2139920090441051 : Nat.Prime 2139920090441051 := by
  apply lucas_primality 2139920090441051 (2 : ZMod 2139920090441051)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (83, 1), (347, 1), (653, 1), (2275657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (83, 1), (347, 1), (653, 1), (2275657, 1)] : List FactorBlock).map factorBlockValue).prod) = 2139920090441051 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_5
      · exact prime_oneHundredFourteenDH_83
      · exact prime_oneHundredFourteenDH_347
      · exact prime_oneHundredFourteenDH_653
      · exact prime_oneHundredFourteenDH_2275657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2139920090441051) ^ 1069960045220525 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2139920090441051) ^ 427984018088210 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2139920090441051) ^ 25782169764350 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2139920090441051) ^ 6166916687150 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2139920090441051) ^ 3277059862850 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 2139920090441051) ^ 940352650 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_2780093878793993 : Nat.Prime 2780093878793993 := by
  apply lucas_primality 2780093878793993 (3 : ZMod 2780093878793993)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (31, 1), (1201183, 1), (9332513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (31, 1), (1201183, 1), (9332513, 1)] : List FactorBlock).map factorBlockValue).prod) = 2780093878793993 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_31
      · exact prime_oneHundredFourteenDH_1201183
      · exact prime_oneHundredFourteenDH_9332513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2780093878793993) ^ 1390046939396996 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 2780093878793993) ^ 89680447703032 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 2780093878793993) ^ 2314463224 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 2780093878793993) ^ 297893384 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_5993243223051079 : Nat.Prime 5993243223051079 := by
  apply lucas_primality 5993243223051079 (3 : ZMod 5993243223051079)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (97, 1), (467, 1), (3319, 1), (738197, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (97, 1), (467, 1), (3319, 1), (738197, 1)] : List FactorBlock).map factorBlockValue).prod) = 5993243223051079 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_97
      · exact prime_oneHundredFourteenDH_467
      · exact prime_oneHundredFourteenDH_3319
      · exact prime_oneHundredFourteenDH_738197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 5993243223051079) ^ 2996621611525539 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 5993243223051079) ^ 1997747741017026 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 5993243223051079) ^ 61786012608774 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 5993243223051079) ^ 12833497265634 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 5993243223051079) ^ 1805737638762 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 5993243223051079) ^ 8118758574 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_6145560041686553 : Nat.Prime 6145560041686553 := by
  apply lucas_primality 6145560041686553 (3 : ZMod 6145560041686553)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (23, 1), (151, 1), (197, 2), (5699467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (23, 1), (151, 1), (197, 2), (5699467, 1)] : List FactorBlock).map factorBlockValue).prod) = 6145560041686553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_23
      · exact prime_oneHundredFourteenDH_151
      · exact prime_oneHundredFourteenDH_197
      · exact prime_oneHundredFourteenDH_5699467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 6145560041686553) ^ 3072780020843276 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 6145560041686553) ^ 267198262682024 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 6145560041686553) ^ 40699073123752 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 6145560041686553) ^ 31195736252216 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 6145560041686553) ^ 1078269256 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_13515990461248871 : Nat.Prime 13515990461248871 := by
  apply lucas_primality 13515990461248871 (7 : ZMod 13515990461248871)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (419, 1), (3229, 1), (142714391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (419, 1), (3229, 1), (142714391, 1)] : List FactorBlock).map factorBlockValue).prod) = 13515990461248871 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_5
      · exact prime_oneHundredFourteenDH_7
      · exact prime_oneHundredFourteenDH_419
      · exact prime_oneHundredFourteenDH_3229
      · exact prime_oneHundredFourteenDH_142714391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 13515990461248871) ^ 6757995230624435 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (7 : ZMod 13515990461248871) ^ 2703198092249774 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (7 : ZMod 13515990461248871) ^ 1930855780178410 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (7 : ZMod 13515990461248871) ^ 32257733797730 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (7 : ZMod 13515990461248871) ^ 4185813088030 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (7 : ZMod 13515990461248871) ^ 94706570 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_14654090252041987 : Nat.Prime 14654090252041987 := by
  apply lucas_primality 14654090252041987 (5 : ZMod 14654090252041987)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (223, 1), (859, 1), (12749982383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (223, 1), (859, 1), (12749982383, 1)] : List FactorBlock).map factorBlockValue).prod) = 14654090252041987 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_223
      · exact prime_oneHundredFourteenDH_859
      · exact prime_oneHundredFourteenDH_12749982383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 14654090252041987) ^ 7327045126020993 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (5 : ZMod 14654090252041987) ^ 4884696750680662 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (5 : ZMod 14654090252041987) ^ 65713409201982 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (5 : ZMod 14654090252041987) ^ 17059476428454 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (5 : ZMod 14654090252041987) ^ 1149342 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_14765453512034683 : Nat.Prime 14765453512034683 := by
  apply lucas_primality 14765453512034683 (2 : ZMod 14765453512034683)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2692093, 1), (914124779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2692093, 1), (914124779, 1)] : List FactorBlock).map factorBlockValue).prod) = 14765453512034683 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_2692093
      · exact prime_oneHundredFourteenDH_914124779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 14765453512034683) ^ 7382726756017341 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 14765453512034683) ^ 4921817837344894 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 14765453512034683) ^ 5484748674 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 14765453512034683) ^ 16152558 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_20007968354627489 : Nat.Prime 20007968354627489 := by
  apply lucas_primality 20007968354627489 (3 : ZMod 20007968354627489)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (625249011082109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (625249011082109, 1)] : List FactorBlock).map factorBlockValue).prod) = 20007968354627489 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_625249011082109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 20007968354627489) ^ 10003984177313744 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 20007968354627489) ^ 32 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_26516431262501417 : Nat.Prime 26516431262501417 := by
  apply lucas_primality 26516431262501417 (3 : ZMod 26516431262501417)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (6299, 1), (526203192223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (6299, 1), (526203192223, 1)] : List FactorBlock).map factorBlockValue).prod) = 26516431262501417 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_6299
      · exact prime_oneHundredFourteenDH_526203192223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 26516431262501417) ^ 13258215631250708 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 26516431262501417) ^ 4209625537784 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 26516431262501417) ^ 50392 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_30227997071821729 : Nat.Prime 30227997071821729 := by
  apply lucas_primality 30227997071821729 (7 : ZMod 30227997071821729)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (173, 1), (181787, 1), (10012193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (173, 1), (181787, 1), (10012193, 1)] : List FactorBlock).map factorBlockValue).prod) = 30227997071821729 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_173
      · exact prime_oneHundredFourteenDH_181787
      · exact prime_oneHundredFourteenDH_10012193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 30227997071821729) ^ 15113998535910864 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (7 : ZMod 30227997071821729) ^ 10075999023940576 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (7 : ZMod 30227997071821729) ^ 174728306773536 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (7 : ZMod 30227997071821729) ^ 166282501344 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (7 : ZMod 30227997071821729) ^ 3019118496 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_43370541694507613 : Nat.Prime 43370541694507613 := by
  apply lucas_primality 43370541694507613 (2 : ZMod 43370541694507613)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (17, 2), (727, 1), (3969714277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (17, 2), (727, 1), (3969714277, 1)] : List FactorBlock).map factorBlockValue).prod) = 43370541694507613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_13
      · exact prime_oneHundredFourteenDH_17
      · exact prime_oneHundredFourteenDH_727
      · exact prime_oneHundredFourteenDH_3969714277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 43370541694507613) ^ 21685270847253806 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 43370541694507613) ^ 3336195514962124 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 43370541694507613) ^ 2551208334971036 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 43370541694507613) ^ 59656866154756 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 43370541694507613) ^ 10925356 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_47254495754060453 : Nat.Prime 47254495754060453 := by
  apply lucas_primality 47254495754060453 (2 : ZMod 47254495754060453)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (13, 1), (425653, 1), (194084747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (13, 1), (425653, 1), (194084747, 1)] : List FactorBlock).map factorBlockValue).prod) = 47254495754060453 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_11
      · exact prime_oneHundredFourteenDH_13
      · exact prime_oneHundredFourteenDH_425653
      · exact prime_oneHundredFourteenDH_194084747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 47254495754060453) ^ 23627247877030226 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 47254495754060453) ^ 4295863250369132 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 47254495754060453) ^ 3634961211850804 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 47254495754060453) ^ 111016475284 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 47254495754060453) ^ 243473516 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_51043989240621001 : Nat.Prime 51043989240621001 := by
  apply lucas_primality 51043989240621001 (34 : ZMod 51043989240621001)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (5, 3), (13, 1), (23, 1), (127, 1), (239, 1), (208309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (5, 3), (13, 1), (23, 1), (127, 1), (239, 1), (208309, 1)] : List FactorBlock).map factorBlockValue).prod) = 51043989240621001 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_5
      · exact prime_oneHundredFourteenDH_13
      · exact prime_oneHundredFourteenDH_23
      · exact prime_oneHundredFourteenDH_127
      · exact prime_oneHundredFourteenDH_239
      · exact prime_oneHundredFourteenDH_208309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (34 : ZMod 51043989240621001) ^ 25521994620310500 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (34 : ZMod 51043989240621001) ^ 17014663080207000 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (34 : ZMod 51043989240621001) ^ 10208797848124200 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (34 : ZMod 51043989240621001) ^ 3926460710817000 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (34 : ZMod 51043989240621001) ^ 2219303880027000 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (34 : ZMod 51043989240621001) ^ 401921175123000 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (34 : ZMod 51043989240621001) ^ 213573176739000 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (34 : ZMod 51043989240621001) ^ 245039769000 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_661124425155551569 : Nat.Prime 661124425155551569 := by
  apply lucas_primality 661124425155551569 (17 : ZMod 661124425155551569)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (23, 1), (467, 1), (142480273139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (23, 1), (467, 1), (142480273139, 1)] : List FactorBlock).map factorBlockValue).prod) = 661124425155551569 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_23
      · exact prime_oneHundredFourteenDH_467
      · exact prime_oneHundredFourteenDH_142480273139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 661124425155551569) ^ 330562212577775784 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (17 : ZMod 661124425155551569) ^ 220374808385183856 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (17 : ZMod 661124425155551569) ^ 28744540224154416 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (17 : ZMod 661124425155551569) ^ 1415683993909104 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (17 : ZMod 661124425155551569) ^ 4640112 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_841983229614766891 : Nat.Prime 841983229614766891 := by
  apply lucas_primality 841983229614766891 (3 : ZMod 841983229614766891)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (113, 1), (35481804872093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (113, 1), (35481804872093, 1)] : List FactorBlock).map factorBlockValue).prod) = 841983229614766891 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_5
      · exact prime_oneHundredFourteenDH_7
      · exact prime_oneHundredFourteenDH_113
      · exact prime_oneHundredFourteenDH_35481804872093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 841983229614766891) ^ 420991614807383445 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 841983229614766891) ^ 280661076538255630 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 841983229614766891) ^ 168396645922953378 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 841983229614766891) ^ 120283318516395270 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 841983229614766891) ^ 7451179023139530 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 841983229614766891) ^ 23730 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_983795084090656741 : Nat.Prime 983795084090656741 := by
  apply lucas_primality 983795084090656741 (2 : ZMod 983795084090656741)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 1), (7, 1), (113, 1), (22397, 1), (102835853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 1), (7, 1), (113, 1), (22397, 1), (102835853, 1)] : List FactorBlock).map factorBlockValue).prod) = 983795084090656741 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_5
      · exact prime_oneHundredFourteenDH_7
      · exact prime_oneHundredFourteenDH_113
      · exact prime_oneHundredFourteenDH_22397
      · exact prime_oneHundredFourteenDH_102835853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 983795084090656741) ^ 491897542045328370 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 983795084090656741) ^ 327931694696885580 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 983795084090656741) ^ 196759016818131348 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 983795084090656741) ^ 140542154870093820 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 983795084090656741) ^ 8706151186642980 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 983795084090656741) ^ 43925306250420 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 983795084090656741) ^ 9566654580 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_1298224515520902401 : Nat.Prime 1298224515520902401 := by
  apply lucas_primality 1298224515520902401 (3 : ZMod 1298224515520902401)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (5, 2), (1630933, 1), (124375177, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (5, 2), (1630933, 1), (124375177, 1)] : List FactorBlock).map factorBlockValue).prod) = 1298224515520902401 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_5
      · exact prime_oneHundredFourteenDH_1630933
      · exact prime_oneHundredFourteenDH_124375177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1298224515520902401) ^ 649112257760451200 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1298224515520902401) ^ 259644903104180480 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1298224515520902401) ^ 796001132800 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1298224515520902401) ^ 10437971200 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_1514098279224436817 : Nat.Prime 1514098279224436817 := by
  apply lucas_primality 1514098279224436817 (3 : ZMod 1514098279224436817)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (37, 1), (32251, 1), (79302919123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (37, 1), (32251, 1), (79302919123, 1)] : List FactorBlock).map factorBlockValue).prod) = 1514098279224436817 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_37
      · exact prime_oneHundredFourteenDH_32251
      · exact prime_oneHundredFourteenDH_79302919123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1514098279224436817) ^ 757049139612218408 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1514098279224436817) ^ 40921575114173968 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1514098279224436817) ^ 46947328120816 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 1514098279224436817) ^ 19092592 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_2220502305087140441 : Nat.Prime 2220502305087140441 := by
  apply lucas_primality 2220502305087140441 (3 : ZMod 2220502305087140441)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (101, 1), (191, 1), (48017, 1), (59929613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (101, 1), (191, 1), (48017, 1), (59929613, 1)] : List FactorBlock).map factorBlockValue).prod) = 2220502305087140441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_5
      · exact prime_oneHundredFourteenDH_101
      · exact prime_oneHundredFourteenDH_191
      · exact prime_oneHundredFourteenDH_48017
      · exact prime_oneHundredFourteenDH_59929613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2220502305087140441) ^ 1110251152543570220 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 444100461017428088 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 21985171337496440 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 11625666518780840 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 46244086575320 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 37051837880 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_2703428958055696769 : Nat.Prime 2703428958055696769 := by
  apply lucas_primality 2703428958055696769 (3 : ZMod 2703428958055696769)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (263, 1), (80306230930837, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (263, 1), (80306230930837, 1)] : List FactorBlock).map factorBlockValue).prod) = 2703428958055696769 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_263
      · exact prime_oneHundredFourteenDH_80306230930837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2703428958055696769) ^ 1351714479027848384 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 2703428958055696769) ^ 10279197559147136 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 2703428958055696769) ^ 33664 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_3384267788357002951 : Nat.Prime 3384267788357002951 := by
  apply lucas_primality 3384267788357002951 (3 : ZMod 3384267788357002951)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (13, 1), (997, 1), (364691, 1), (4773203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (13, 1), (997, 1), (364691, 1), (4773203, 1)] : List FactorBlock).map factorBlockValue).prod) = 3384267788357002951 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_5
      · exact prime_oneHundredFourteenDH_13
      · exact prime_oneHundredFourteenDH_997
      · exact prime_oneHundredFourteenDH_364691
      · exact prime_oneHundredFourteenDH_4773203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3384267788357002951) ^ 1692133894178501475 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 3384267788357002951) ^ 1128089262785667650 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 3384267788357002951) ^ 676853557671400590 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 3384267788357002951) ^ 260328291412077150 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 3384267788357002951) ^ 3394451141782350 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 3384267788357002951) ^ 9279822612450 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 3384267788357002951) ^ 709014007650 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_4982181100062557317 : Nat.Prime 4982181100062557317 := by
  apply lucas_primality 4982181100062557317 (2 : ZMod 4982181100062557317)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (16661, 1), (24919378088863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (16661, 1), (24919378088863, 1)] : List FactorBlock).map factorBlockValue).prod) = 4982181100062557317 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_16661
      · exact prime_oneHundredFourteenDH_24919378088863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4982181100062557317) ^ 2491090550031278658 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 4982181100062557317) ^ 1660727033354185772 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 4982181100062557317) ^ 299032537066356 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 4982181100062557317) ^ 199932 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_5983106634054978683 : Nat.Prime 5983106634054978683 := by
  apply lucas_primality 5983106634054978683 (2 : ZMod 5983106634054978683)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (46687, 1), (6252769, 1), (10247747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (46687, 1), (6252769, 1), (10247747, 1)] : List FactorBlock).map factorBlockValue).prod) = 5983106634054978683 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_46687
      · exact prime_oneHundredFourteenDH_6252769
      · exact prime_oneHundredFourteenDH_10247747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5983106634054978683) ^ 2991553317027489341 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 5983106634054978683) ^ 128153589522886 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 5983106634054978683) ^ 956873128378 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 5983106634054978683) ^ 583846052606 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_6205241104008965969 : Nat.Prime 6205241104008965969 := by
  apply lucas_primality 6205241104008965969 (3 : ZMod 6205241104008965969)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (17, 1), (19, 1), (89, 1), (5857, 1), (2303408287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (17, 1), (19, 1), (89, 1), (5857, 1), (2303408287, 1)] : List FactorBlock).map factorBlockValue).prod) = 6205241104008965969 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_17
      · exact prime_oneHundredFourteenDH_19
      · exact prime_oneHundredFourteenDH_89
      · exact prime_oneHundredFourteenDH_5857
      · exact prime_oneHundredFourteenDH_2303408287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 6205241104008965969) ^ 3102620552004482984 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 6205241104008965969) ^ 365014182588762704 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 6205241104008965969) ^ 326591637053103472 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 6205241104008965969) ^ 69721810157404112 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 6205241104008965969) ^ 1059457248422224 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 6205241104008965969) ^ 2693938864 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_9267293713540077043 : Nat.Prime 9267293713540077043 := by
  apply lucas_primality 9267293713540077043 (2 : ZMod 9267293713540077043)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (79, 1), (349, 1), (823, 1), (68068992679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (79, 1), (349, 1), (823, 1), (68068992679, 1)] : List FactorBlock).map factorBlockValue).prod) = 9267293713540077043 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_79
      · exact prime_oneHundredFourteenDH_349
      · exact prime_oneHundredFourteenDH_823
      · exact prime_oneHundredFourteenDH_68068992679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9267293713540077043) ^ 4633646856770038521 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 9267293713540077043) ^ 3089097904513359014 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 9267293713540077043) ^ 117307515361266798 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 9267293713540077043) ^ 26553850182063258 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 9267293713540077043) ^ 11260381182916254 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 9267293713540077043) ^ 136145598 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_9315739240638183151 : Nat.Prime 9315739240638183151 := by
  apply lucas_primality 9315739240638183151 (3 : ZMod 9315739240638183151)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (7, 1), (307, 1), (28899454756129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (7, 1), (307, 1), (28899454756129, 1)] : List FactorBlock).map factorBlockValue).prod) = 9315739240638183151 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_5
      · exact prime_oneHundredFourteenDH_7
      · exact prime_oneHundredFourteenDH_307
      · exact prime_oneHundredFourteenDH_28899454756129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 9315739240638183151) ^ 4657869620319091575 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 9315739240638183151) ^ 3105246413546061050 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 9315739240638183151) ^ 1863147848127636630 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 9315739240638183151) ^ 1330819891519740450 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 9315739240638183151) ^ 30344427493935450 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 9315739240638183151) ^ 322350 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_12480445510527170173 : Nat.Prime 12480445510527170173 := by
  apply lucas_primality 12480445510527170173 (2 : ZMod 12480445510527170173)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (509, 1), (1597, 1), (4789, 1), (267166073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (509, 1), (1597, 1), (4789, 1), (267166073, 1)] : List FactorBlock).map factorBlockValue).prod) = 12480445510527170173 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_509
      · exact prime_oneHundredFourteenDH_1597
      · exact prime_oneHundredFourteenDH_4789
      · exact prime_oneHundredFourteenDH_267166073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 12480445510527170173) ^ 6240222755263585086 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 12480445510527170173) ^ 4160148503509056724 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 12480445510527170173) ^ 24519539313412908 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 12480445510527170173) ^ 7814931440530476 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 12480445510527170173) ^ 2606065047092748 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 12480445510527170173) ^ 46714185564 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_13967230684837612571 : Nat.Prime 13967230684837612571 := by
  apply lucas_primality 13967230684837612571 (2 : ZMod 13967230684837612571)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (239, 1), (857, 1), (3691, 1), (1847513149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (239, 1), (857, 1), (3691, 1), (1847513149, 1)] : List FactorBlock).map factorBlockValue).prod) = 13967230684837612571 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_5
      · exact prime_oneHundredFourteenDH_239
      · exact prime_oneHundredFourteenDH_857
      · exact prime_oneHundredFourteenDH_3691
      · exact prime_oneHundredFourteenDH_1847513149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 13967230684837612571) ^ 6983615342418806285 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 13967230684837612571) ^ 2793446136967522514 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 13967230684837612571) ^ 58440295752458630 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 13967230684837612571) ^ 16297818768772010 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 13967230684837612571) ^ 3784131857176270 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 13967230684837612571) ^ 7560016930 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_38295590219153007821 : Nat.Prime 38295590219153007821 := by
  apply lucas_primality 38295590219153007821 (2 : ZMod 38295590219153007821)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (1801, 1), (3511, 1), (510199, 1), (593519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (1801, 1), (3511, 1), (510199, 1), (593519, 1)] : List FactorBlock).map factorBlockValue).prod) = 38295590219153007821 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_5
      · exact prime_oneHundredFourteenDH_1801
      · exact prime_oneHundredFourteenDH_3511
      · exact prime_oneHundredFourteenDH_510199
      · exact prime_oneHundredFourteenDH_593519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 38295590219153007821) ^ 19147795109576503910 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 38295590219153007821) ^ 7659118043830601564 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 38295590219153007821) ^ 21263514835731820 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 38295590219153007821) ^ 10907317066121620 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 38295590219153007821) ^ 75060104428180 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 38295590219153007821) ^ 64522938977780 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_38423841679234991431 : Nat.Prime 38423841679234991431 := by
  apply lucas_primality 38423841679234991431 (3 : ZMod 38423841679234991431)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (11, 1), (197, 1), (1901, 1), (103637575981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (11, 1), (197, 1), (1901, 1), (103637575981, 1)] : List FactorBlock).map factorBlockValue).prod) = 38423841679234991431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_5
      · exact prime_oneHundredFourteenDH_11
      · exact prime_oneHundredFourteenDH_197
      · exact prime_oneHundredFourteenDH_1901
      · exact prime_oneHundredFourteenDH_103637575981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 38423841679234991431) ^ 19211920839617495715 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 38423841679234991431) ^ 12807947226411663810 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 38423841679234991431) ^ 7684768335846998286 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 38423841679234991431) ^ 3493076516294090130 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 38423841679234991431) ^ 195044881620482190 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 38423841679234991431) ^ 20212436443574430 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 38423841679234991431) ^ 370752030 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_40327196370831666377 : Nat.Prime 40327196370831666377 := by
  apply lucas_primality 40327196370831666377 (3 : ZMod 40327196370831666377)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7449241, 1), (676699753217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7449241, 1), (676699753217, 1)] : List FactorBlock).map factorBlockValue).prod) = 40327196370831666377 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_7449241
      · exact prime_oneHundredFourteenDH_676699753217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 40327196370831666377) ^ 20163598185415833188 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 40327196370831666377) ^ 5413598025736 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 40327196370831666377) ^ 59593928 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_45814288364731121923 : Nat.Prime 45814288364731121923 := by
  apply lucas_primality 45814288364731121923 (2 : ZMod 45814288364731121923)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (53, 1), (89, 1), (539588349053437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (53, 1), (89, 1), (539588349053437, 1)] : List FactorBlock).map factorBlockValue).prod) = 45814288364731121923 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_53
      · exact prime_oneHundredFourteenDH_89
      · exact prime_oneHundredFourteenDH_539588349053437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 45814288364731121923) ^ 22907144182365560961 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 45814288364731121923) ^ 15271429454910373974 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 45814288364731121923) ^ 864420535183606074 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 45814288364731121923) ^ 514767284996978898 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 45814288364731121923) ^ 84906 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_92128134824741186389 : Nat.Prime 92128134824741186389 := by
  apply lucas_primality 92128134824741186389 (2 : ZMod 92128134824741186389)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (61, 1), (5993243223051079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (61, 1), (5993243223051079, 1)] : List FactorBlock).map factorBlockValue).prod) = 92128134824741186389 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_7
      · exact prime_oneHundredFourteenDH_61
      · exact prime_oneHundredFourteenDH_5993243223051079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 92128134824741186389) ^ 46064067412370593194 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 92128134824741186389) ^ 30709378274913728796 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 92128134824741186389) ^ 13161162117820169484 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 92128134824741186389) ^ 1510297292208871908 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 92128134824741186389) ^ 15372 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_256223811061086791179 : Nat.Prime 256223811061086791179 := by
  apply lucas_primality 256223811061086791179 (2 : ZMod 256223811061086791179)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (6863, 1), (366020420757353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (6863, 1), (366020420757353, 1)] : List FactorBlock).map factorBlockValue).prod) = 256223811061086791179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_17
      · exact prime_oneHundredFourteenDH_6863
      · exact prime_oneHundredFourteenDH_366020420757353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 256223811061086791179) ^ 128111905530543395589 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 85407937020362263726 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 15071988885946281834 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 37334082917250006 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 700026 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_289542354222801077537 : Nat.Prime 289542354222801077537 := by
  apply lucas_primality 289542354222801077537 (3 : ZMod 289542354222801077537)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (12975191, 1), (697346079103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (12975191, 1), (697346079103, 1)] : List FactorBlock).map factorBlockValue).prod) = 289542354222801077537 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_12975191
      · exact prime_oneHundredFourteenDH_697346079103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 289542354222801077537) ^ 144771177111400538768 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 289542354222801077537) ^ 22315074531296 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 289542354222801077537) ^ 415206112 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_368512539298964745557 : Nat.Prime 368512539298964745557 := by
  apply lucas_primality 368512539298964745557 (2 : ZMod 368512539298964745557)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (92128134824741186389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (92128134824741186389, 1)] : List FactorBlock).map factorBlockValue).prod) = 368512539298964745557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_92128134824741186389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 368512539298964745557) ^ 184256269649482372778 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 368512539298964745557) ^ 4 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_488441478919661500867 : Nat.Prime 488441478919661500867 := by
  apply lucas_primality 488441478919661500867 (3 : ZMod 488441478919661500867)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (241, 1), (2089, 1), (147457, 1), (1096580227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (241, 1), (2089, 1), (147457, 1), (1096580227, 1)] : List FactorBlock).map factorBlockValue).prod) = 488441478919661500867 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_241
      · exact prime_oneHundredFourteenDH_2089
      · exact prime_oneHundredFourteenDH_147457
      · exact prime_oneHundredFourteenDH_1096580227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 488441478919661500867) ^ 244220739459830750433 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 488441478919661500867) ^ 162813826306553833622 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 488441478919661500867) ^ 2026728128297350626 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 488441478919661500867) ^ 233815930550340594 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 488441478919661500867) ^ 3312433312217538 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 488441478919661500867) ^ 445422475158 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_614781466867759862897 : Nat.Prime 614781466867759862897 := by
  apply lucas_primality 614781466867759862897 (3 : ZMod 614781466867759862897)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (38423841679234991431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (38423841679234991431, 1)] : List FactorBlock).map factorBlockValue).prod) = 614781466867759862897 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_38423841679234991431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 614781466867759862897) ^ 307390733433879931448 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 614781466867759862897) ^ 16 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_1205269042013298899237 : Nat.Prime 1205269042013298899237 := by
  apply lucas_primality 1205269042013298899237 (2 : ZMod 1205269042013298899237)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (1549, 1), (47713, 1), (341461, 1), (519119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (1549, 1), (47713, 1), (341461, 1), (519119, 1)] : List FactorBlock).map factorBlockValue).prod) = 1205269042013298899237 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_23
      · exact prime_oneHundredFourteenDH_1549
      · exact prime_oneHundredFourteenDH_47713
      · exact prime_oneHundredFourteenDH_341461
      · exact prime_oneHundredFourteenDH_519119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1205269042013298899237) ^ 602634521006649449618 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1205269042013298899237) ^ 52403001826665169532 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1205269042013298899237) ^ 778094927058294964 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1205269042013298899237) ^ 25260810303550372 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1205269042013298899237) ^ 3529741440496276 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1205269042013298899237) ^ 2321758675782044 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_1465261596365849555473 : Nat.Prime 1465261596365849555473 := by
  apply lucas_primality 1465261596365849555473 (5 : ZMod 1465261596365849555473)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 4), (31, 1), (173, 1), (210815417418539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 4), (31, 1), (173, 1), (210815417418539, 1)] : List FactorBlock).map factorBlockValue).prod) = 1465261596365849555473 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_31
      · exact prime_oneHundredFourteenDH_173
      · exact prime_oneHundredFourteenDH_210815417418539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1465261596365849555473) ^ 732630798182924777736 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1465261596365849555473) ^ 488420532121949851824 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1465261596365849555473) ^ 47266503108575792112 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1465261596365849555473) ^ 8469720210207222864 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (5 : ZMod 1465261596365849555473) ^ 6950448 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_1579017477960970406459 : Nat.Prime 1579017477960970406459 := by
  apply lucas_primality 1579017477960970406459 (2 : ZMod 1579017477960970406459)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (353, 1), (599, 1), (797, 1), (62081, 1), (6860341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (353, 1), (599, 1), (797, 1), (62081, 1), (6860341, 1)] : List FactorBlock).map factorBlockValue).prod) = 1579017477960970406459 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_11
      · exact prime_oneHundredFourteenDH_353
      · exact prime_oneHundredFourteenDH_599
      · exact prime_oneHundredFourteenDH_797
      · exact prime_oneHundredFourteenDH_62081
      · exact prime_oneHundredFourteenDH_6860341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1579017477960970406459) ^ 789508738980485203229 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1579017477960970406459) ^ 143547043450997309678 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1579017477960970406459) ^ 4473137331334193786 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1579017477960970406459) ^ 2636089278732838742 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1579017477960970406459) ^ 1981201352523174914 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1579017477960970406459) ^ 25434794509769018 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1579017477960970406459) ^ 230166033723538 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_2440686704550964295047 : Nat.Prime 2440686704550964295047 := by
  apply lucas_primality 2440686704550964295047 (13 : ZMod 2440686704550964295047)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 2), (67, 1), (467, 1), (6793, 1), (6622312097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 2), (67, 1), (467, 1), (6793, 1), (6622312097, 1)] : List FactorBlock).map factorBlockValue).prod) = 2440686704550964295047 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_17
      · exact prime_oneHundredFourteenDH_67
      · exact prime_oneHundredFourteenDH_467
      · exact prime_oneHundredFourteenDH_6793
      · exact prime_oneHundredFourteenDH_6622312097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 2440686704550964295047) ^ 1220343352275482147523 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (13 : ZMod 2440686704550964295047) ^ 813562234850321431682 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (13 : ZMod 2440686704550964295047) ^ 143569806150056723238 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (13 : ZMod 2440686704550964295047) ^ 36428159769417377538 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (13 : ZMod 2440686704550964295047) ^ 5226309859852171938 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (13 : ZMod 2440686704550964295047) ^ 359294377234059222 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (13 : ZMod 2440686704550964295047) ^ 368555070918 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_3074685732733041494149 : Nat.Prime 3074685732733041494149 := by
  apply lucas_primality 3074685732733041494149 (2 : ZMod 3074685732733041494149)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (256223811061086791179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (256223811061086791179, 1)] : List FactorBlock).map factorBlockValue).prod) = 3074685732733041494149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_256223811061086791179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3074685732733041494149) ^ 1537342866366520747074 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 3074685732733041494149) ^ 1024895244244347164716 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 3074685732733041494149) ^ 12 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_4335982710033791550947 : Nat.Prime 4335982710033791550947 := by
  apply lucas_primality 4335982710033791550947 (2 : ZMod 4335982710033791550947)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (42473, 1), (51043989240621001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (42473, 1), (51043989240621001, 1)] : List FactorBlock).map factorBlockValue).prod) = 4335982710033791550947 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_42473
      · exact prime_oneHundredFourteenDH_51043989240621001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4335982710033791550947) ^ 2167991355016895775473 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 4335982710033791550947) ^ 102087978481242002 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 4335982710033791550947) ^ 84946 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_7488998344362023941087 : Nat.Prime 7488998344362023941087 := by
  apply lucas_primality 7488998344362023941087 (3 : ZMod 7488998344362023941087)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (3515265851, 1), (118356756277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (3515265851, 1), (118356756277, 1)] : List FactorBlock).map factorBlockValue).prod) = 7488998344362023941087 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_3515265851
      · exact prime_oneHundredFourteenDH_118356756277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 7488998344362023941087) ^ 3744499172181011970543 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 7488998344362023941087) ^ 2496332781454007980362 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 7488998344362023941087) ^ 2130421612986 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 7488998344362023941087) ^ 63274785318 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_10149320156863857812093 : Nat.Prime 10149320156863857812093 := by
  apply lucas_primality 10149320156863857812093 (2 : ZMod 10149320156863857812093)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (61, 1), (5399, 1), (662111, 1), (11635980787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (61, 1), (5399, 1), (662111, 1), (11635980787, 1)] : List FactorBlock).map factorBlockValue).prod) = 10149320156863857812093 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_61
      · exact prime_oneHundredFourteenDH_5399
      · exact prime_oneHundredFourteenDH_662111
      · exact prime_oneHundredFourteenDH_11635980787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 10149320156863857812093) ^ 5074660078431928906046 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 10149320156863857812093) ^ 166382297653505865772 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 10149320156863857812093) ^ 1879851853466171108 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 10149320156863857812093) ^ 15328729105639172 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 10149320156863857812093) ^ 872235898516 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_10909611845244380568449 : Nat.Prime 10909611845244380568449 := by
  apply lucas_primality 10909611845244380568449 (3 : ZMod 10909611845244380568449)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (157, 1), (66708619, 1), (8138000777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (157, 1), (66708619, 1), (8138000777, 1)] : List FactorBlock).map factorBlockValue).prod) = 10909611845244380568449 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_157
      · exact prime_oneHundredFourteenDH_66708619
      · exact prime_oneHundredFourteenDH_8138000777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 10909611845244380568449) ^ 5454805922622190284224 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 10909611845244380568449) ^ 69487973536588411264 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 10909611845244380568449) ^ 163541263614592 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 10909611845244380568449) ^ 1340576407424 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_39000451930099816262347 : Nat.Prime 39000451930099816262347 := by
  apply lucas_primality 39000451930099816262347 (2 : ZMod 39000451930099816262347)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (53, 1), (137737, 1), (98934870722059, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (53, 1), (137737, 1), (98934870722059, 1)] : List FactorBlock).map factorBlockValue).prod) = 39000451930099816262347 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_53
      · exact prime_oneHundredFourteenDH_137737
      · exact prime_oneHundredFourteenDH_98934870722059
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 39000451930099816262347) ^ 19500225965049908131173 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 39000451930099816262347) ^ 13000150643366605420782 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 39000451930099816262347) ^ 735857583586788986082 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 39000451930099816262347) ^ 283151600006532858 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 39000451930099816262347) ^ 394203294 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_58557153974234966796209 : Nat.Prime 58557153974234966796209 := by
  apply lucas_primality 58557153974234966796209 (3 : ZMod 58557153974234966796209)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (67, 1), (18049, 1), (782123, 1), (3869518907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (67, 1), (18049, 1), (782123, 1), (3869518907, 1)] : List FactorBlock).map factorBlockValue).prod) = 58557153974234966796209 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_67
      · exact prime_oneHundredFourteenDH_18049
      · exact prime_oneHundredFourteenDH_782123
      · exact prime_oneHundredFourteenDH_3869518907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 58557153974234966796209) ^ 29278576987117483398104 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 58557153974234966796209) ^ 873987372749775623824 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 58557153974234966796209) ^ 3244343397098729392 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 58557153974234966796209) ^ 74869494918618896 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 58557153974234966796209) ^ 15132928764944 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_119460484679241354778471 : Nat.Prime 119460484679241354778471 := by
  apply lucas_primality 119460484679241354778471 (11 : ZMod 119460484679241354778471)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (457, 1), (1429, 1), (248543, 1), (2230285021, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (457, 1), (1429, 1), (248543, 1), (2230285021, 1)] : List FactorBlock).map factorBlockValue).prod) = 119460484679241354778471 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_5
      · exact prime_oneHundredFourteenDH_11
      · exact prime_oneHundredFourteenDH_457
      · exact prime_oneHundredFourteenDH_1429
      · exact prime_oneHundredFourteenDH_248543
      · exact prime_oneHundredFourteenDH_2230285021
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 119460484679241354778471) ^ 59730242339620677389235 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (11 : ZMod 119460484679241354778471) ^ 39820161559747118259490 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (11 : ZMod 119460484679241354778471) ^ 23892096935848270955694 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (11 : ZMod 119460484679241354778471) ^ 10860044061749214070770 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (11 : ZMod 119460484679241354778471) ^ 261401498204029222710 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (11 : ZMod 119460484679241354778471) ^ 83597260097439716430 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (11 : ZMod 119460484679241354778471) ^ 480643126860307290 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (11 : ZMod 119460484679241354778471) ^ 53562878087070 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_188163388806285993734741 : Nat.Prime 188163388806285993734741 := by
  apply lucas_primality 188163388806285993734741 (2 : ZMod 188163388806285993734741)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (23, 1), (743, 1), (1759, 1), (312984363615887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (23, 1), (743, 1), (1759, 1), (312984363615887, 1)] : List FactorBlock).map factorBlockValue).prod) = 188163388806285993734741 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_5
      · exact prime_oneHundredFourteenDH_23
      · exact prime_oneHundredFourteenDH_743
      · exact prime_oneHundredFourteenDH_1759
      · exact prime_oneHundredFourteenDH_312984363615887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 188163388806285993734741) ^ 94081694403142996867370 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 188163388806285993734741) ^ 37632677761257198746948 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 188163388806285993734741) ^ 8181016904621130162380 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 188163388806285993734741) ^ 253248167976158807180 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 188163388806285993734741) ^ 106971795796637858860 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 188163388806285993734741) ^ 601191020 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_606399823574740199479417 : Nat.Prime 606399823574740199479417 := by
  apply lucas_primality 606399823574740199479417 (5 : ZMod 606399823574740199479417)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (41, 1), (103, 1), (5983106634054978683, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (41, 1), (103, 1), (5983106634054978683, 1)] : List FactorBlock).map factorBlockValue).prod) = 606399823574740199479417 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_41
      · exact prime_oneHundredFourteenDH_103
      · exact prime_oneHundredFourteenDH_5983106634054978683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 606399823574740199479417) ^ 303199911787370099739708 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (5 : ZMod 606399823574740199479417) ^ 202133274524913399826472 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (5 : ZMod 606399823574740199479417) ^ 14790239599383907304376 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (5 : ZMod 606399823574740199479417) ^ 5887376927910099024072 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (5 : ZMod 606399823574740199479417) ^ 101352 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_878899926231809511221431 : Nat.Prime 878899926231809511221431 := by
  apply lucas_primality 878899926231809511221431 (6 : ZMod 878899926231809511221431)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 1), (797, 1), (125287, 1), (13971226936099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 1), (797, 1), (125287, 1), (13971226936099, 1)] : List FactorBlock).map factorBlockValue).prod) = 878899926231809511221431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_5
      · exact prime_oneHundredFourteenDH_7
      · exact prime_oneHundredFourteenDH_797
      · exact prime_oneHundredFourteenDH_125287
      · exact prime_oneHundredFourteenDH_13971226936099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 878899926231809511221431) ^ 439449963115904755610715 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (6 : ZMod 878899926231809511221431) ^ 292966642077269837073810 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (6 : ZMod 878899926231809511221431) ^ 175779985246361902244286 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (6 : ZMod 878899926231809511221431) ^ 125557132318829930174490 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (6 : ZMod 878899926231809511221431) ^ 1102760258760112310190 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (6 : ZMod 878899926231809511221431) ^ 7015092756884668890 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (6 : ZMod 878899926231809511221431) ^ 62907855570 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_1954840379249293022601677 : Nat.Prime 1954840379249293022601677 := by
  apply lucas_primality 1954840379249293022601677 (2 : ZMod 1954840379249293022601677)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (373, 1), (125933891, 1), (10403988322733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (373, 1), (125933891, 1), (10403988322733, 1)] : List FactorBlock).map factorBlockValue).prod) = 1954840379249293022601677 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_373
      · exact prime_oneHundredFourteenDH_125933891
      · exact prime_oneHundredFourteenDH_10403988322733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1954840379249293022601677) ^ 977420189624646511300838 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1954840379249293022601677) ^ 5240858925601321776412 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1954840379249293022601677) ^ 15522750577517636 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1954840379249293022601677) ^ 187893365372 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_5272196244238841994065687 : Nat.Prime 5272196244238841994065687 := by
  apply lucas_primality 5272196244238841994065687 (5 : ZMod 5272196244238841994065687)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23427721039, 1), (112520467429637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23427721039, 1), (112520467429637, 1)] : List FactorBlock).map factorBlockValue).prod) = 5272196244238841994065687 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_23427721039
      · exact prime_oneHundredFourteenDH_112520467429637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 5272196244238841994065687) ^ 2636098122119420997032843 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (5 : ZMod 5272196244238841994065687) ^ 225040934859274 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (5 : ZMod 5272196244238841994065687) ^ 46855442078 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_126315299707330606125862439 : Nat.Prime 126315299707330606125862439 := by
  apply lucas_primality 126315299707330606125862439 (17 : ZMod 126315299707330606125862439)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (113, 1), (229, 1), (2440686704550964295047, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (113, 1), (229, 1), (2440686704550964295047, 1)] : List FactorBlock).map factorBlockValue).prod) = 126315299707330606125862439 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_113
      · exact prime_oneHundredFourteenDH_229
      · exact prime_oneHundredFourteenDH_2440686704550964295047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 126315299707330606125862439) ^ 63157649853665303062931219 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (17 : ZMod 126315299707330606125862439) ^ 1117834510684341647131526 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (17 : ZMod 126315299707330606125862439) ^ 551595195228517930680622 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (17 : ZMod 126315299707330606125862439) ^ 51754 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_149587596878714491383235541 : Nat.Prime 149587596878714491383235541 := by
  apply lucas_primality 149587596878714491383235541 (2 : ZMod 149587596878714491383235541)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (97, 1), (709, 1), (720847559, 1), (150870450811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (97, 1), (709, 1), (720847559, 1), (150870450811, 1)] : List FactorBlock).map factorBlockValue).prod) = 149587596878714491383235541 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_5
      · exact prime_oneHundredFourteenDH_97
      · exact prime_oneHundredFourteenDH_709
      · exact prime_oneHundredFourteenDH_720847559
      · exact prime_oneHundredFourteenDH_150870450811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 149587596878714491383235541) ^ 74793798439357245691617770 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 149587596878714491383235541) ^ 29917519375742898276647108 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 149587596878714491383235541) ^ 1542140174007365890548820 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 149587596878714491383235541) ^ 210983916613137505477060 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 149587596878714491383235541) ^ 207516270272498060 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 149587596878714491383235541) ^ 991496983502140 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_173907644887382911917800287 : Nat.Prime 173907644887382911917800287 := by
  apply lucas_primality 173907644887382911917800287 (5 : ZMod 173907644887382911917800287)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (587, 1), (967, 1), (3216511, 1), (15875148888199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (587, 1), (967, 1), (3216511, 1), (15875148888199, 1)] : List FactorBlock).map factorBlockValue).prod) = 173907644887382911917800287 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_587
      · exact prime_oneHundredFourteenDH_967
      · exact prime_oneHundredFourteenDH_3216511
      · exact prime_oneHundredFourteenDH_15875148888199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 173907644887382911917800287) ^ 86953822443691455958900143 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (5 : ZMod 173907644887382911917800287) ^ 57969214962460970639266762 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (5 : ZMod 173907644887382911917800287) ^ 296265153130124211103578 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (5 : ZMod 173907644887382911917800287) ^ 179842445591916144692658 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (5 : ZMod 173907644887382911917800287) ^ 54067169329557061026 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (5 : ZMod 173907644887382911917800287) ^ 10954709534514 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_174132331767082373044309073 : Nat.Prime 174132331767082373044309073 := by
  apply lucas_primality 174132331767082373044309073 (3 : ZMod 174132331767082373044309073)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (43, 1), (101, 1), (269, 1), (9315739240638183151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (43, 1), (101, 1), (269, 1), (9315739240638183151, 1)] : List FactorBlock).map factorBlockValue).prod) = 174132331767082373044309073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_43
      · exact prime_oneHundredFourteenDH_101
      · exact prime_oneHundredFourteenDH_269
      · exact prime_oneHundredFourteenDH_9315739240638183151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 174132331767082373044309073) ^ 87066165883541186522154536 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 174132331767082373044309073) ^ 4049589110862380768472304 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 174132331767082373044309073) ^ 1724082492743389832121872 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 174132331767082373044309073) ^ 647332088353466070796688 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 174132331767082373044309073) ^ 18692272 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_254779630978680069444792481 : Nat.Prime 254779630978680069444792481 := by
  apply lucas_primality 254779630978680069444792481 (23 : ZMod 254779630978680069444792481)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 1), (13, 1), (37, 1), (971, 1), (1201, 1), (2647, 1), (357488612183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 1), (13, 1), (37, 1), (971, 1), (1201, 1), (2647, 1), (357488612183, 1)] : List FactorBlock).map factorBlockValue).prod) = 254779630978680069444792481 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_5
      · exact prime_oneHundredFourteenDH_13
      · exact prime_oneHundredFourteenDH_37
      · exact prime_oneHundredFourteenDH_971
      · exact prime_oneHundredFourteenDH_1201
      · exact prime_oneHundredFourteenDH_2647
      · exact prime_oneHundredFourteenDH_357488612183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 254779630978680069444792481) ^ 127389815489340034722396240 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (23 : ZMod 254779630978680069444792481) ^ 84926543659560023148264160 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (23 : ZMod 254779630978680069444792481) ^ 50955926195736013888958496 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (23 : ZMod 254779630978680069444792481) ^ 19598433152206159188060960 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (23 : ZMod 254779630978680069444792481) ^ 6885935972396758633643040 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (23 : ZMod 254779630978680069444792481) ^ 262388909349824994278880 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (23 : ZMod 254779630978680069444792481) ^ 212139576168759425016480 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (23 : ZMod 254779630978680069444792481) ^ 96252221752429191327840 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (23 : ZMod 254779630978680069444792481) ^ 712692998590560 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_418566536607831542659301933 : Nat.Prime 418566536607831542659301933 := by
  apply lucas_primality 418566536607831542659301933 (2 : ZMod 418566536607831542659301933)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1787, 1), (58557153974234966796209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1787, 1), (58557153974234966796209, 1)] : List FactorBlock).map factorBlockValue).prod) = 418566536607831542659301933 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_1787
      · exact prime_oneHundredFourteenDH_58557153974234966796209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 418566536607831542659301933) ^ 209283268303915771329650966 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 418566536607831542659301933) ^ 234228615896939867184836 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 418566536607831542659301933) ^ 7148 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_942506467047005291862204353 : Nat.Prime 942506467047005291862204353 := by
  apply lucas_primality 942506467047005291862204353 (3 : ZMod 942506467047005291862204353)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (1451, 1), (10149320156863857812093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (1451, 1), (10149320156863857812093, 1)] : List FactorBlock).map factorBlockValue).prod) = 942506467047005291862204353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_1451
      · exact prime_oneHundredFourteenDH_10149320156863857812093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 942506467047005291862204353) ^ 471253233523502645931102176 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 942506467047005291862204353) ^ 649556490039286899973952 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 942506467047005291862204353) ^ 92864 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_1497538053196908408181058027 : Nat.Prime 1497538053196908408181058027 := by
  apply lucas_primality 1497538053196908408181058027 (2 : ZMod 1497538053196908408181058027)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1703297, 1), (4959861037, 1), (88631475817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1703297, 1), (4959861037, 1), (88631475817, 1)] : List FactorBlock).map factorBlockValue).prod) = 1497538053196908408181058027 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_1703297
      · exact prime_oneHundredFourteenDH_4959861037
      · exact prime_oneHundredFourteenDH_88631475817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1497538053196908408181058027) ^ 748769026598454204090529013 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1497538053196908408181058027) ^ 879199607113092084458 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1497538053196908408181058027) ^ 301931453729337298 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 1497538053196908408181058027) ^ 16896232849477978 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_2246307079795362612271587041 : Nat.Prime 2246307079795362612271587041 := by
  apply lucas_primality 2246307079795362612271587041 (6 : ZMod 2246307079795362612271587041)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (19, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (19, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 2246307079795362612271587041 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_5
      · exact prime_oneHundredFourteenDH_19
      · exact prime_oneHundredFourteenDH_171401
      · exact prime_oneHundredFourteenDH_714027719
      · exact prime_oneHundredFourteenDH_6037638679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 2246307079795362612271587041) ^ 1123153539897681306135793520 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (6 : ZMod 2246307079795362612271587041) ^ 449261415959072522454317408 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (6 : ZMod 2246307079795362612271587041) ^ 118226688410282242751136160 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (6 : ZMod 2246307079795362612271587041) ^ 13105565777302131331040 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (6 : ZMod 2246307079795362612271587041) ^ 3145966213946608160 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (6 : ZMod 2246307079795362612271587041) ^ 372050597795529760 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_2695568495754435134725904449 : Nat.Prime 2695568495754435134725904449 := by
  apply lucas_primality 2695568495754435134725904449 (7 : ZMod 2695568495754435134725904449)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (19, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (19, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 2695568495754435134725904449 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_19
      · exact prime_oneHundredFourteenDH_171401
      · exact prime_oneHundredFourteenDH_714027719
      · exact prime_oneHundredFourteenDH_6037638679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 2695568495754435134725904449) ^ 1347784247877217567362952224 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (7 : ZMod 2695568495754435134725904449) ^ 898522831918145044908634816 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (7 : ZMod 2695568495754435134725904449) ^ 141872026092338691301363392 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (7 : ZMod 2695568495754435134725904449) ^ 15726678932762557597248 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (7 : ZMod 2695568495754435134725904449) ^ 3775159456735929792 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (7 : ZMod 2695568495754435134725904449) ^ 446460717354635712 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_22463070797953626122715870413 : Nat.Prime 22463070797953626122715870413 := by
  apply lucas_primality 22463070797953626122715870413 (2 : ZMod 22463070797953626122715870413)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (32603, 1), (7488998344362023941087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (32603, 1), (7488998344362023941087, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953626122715870413 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_23
      · exact prime_oneHundredFourteenDH_32603
      · exact prime_oneHundredFourteenDH_7488998344362023941087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 22463070797953626122715870413) ^ 11231535398976813061357935206 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 22463070797953626122715870413) ^ 976655252084940266205037844 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 22463070797953626122715870413) ^ 688987847681306202580004 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 22463070797953626122715870413) ^ 2999476 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_26955684957544351347259044497 : Nat.Prime 26955684957544351347259044497 := by
  apply lucas_primality 26955684957544351347259044497 (3 : ZMod 26955684957544351347259044497)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (863, 1), (156419, 1), (12480445510527170173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (863, 1), (156419, 1), (12480445510527170173, 1)] : List FactorBlock).map factorBlockValue).prod) = 26955684957544351347259044497 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_863
      · exact prime_oneHundredFourteenDH_156419
      · exact prime_oneHundredFourteenDH_12480445510527170173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 26955684957544351347259044497) ^ 13477842478772175673629522248 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 26955684957544351347259044497) ^ 31234860900978390900647792 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 26955684957544351347259044497) ^ 172329991609359165748784 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (3 : ZMod 26955684957544351347259044497) ^ 2159833552 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_33694606196930439184073805601 : Nat.Prime 33694606196930439184073805601 := by
  apply lucas_primality 33694606196930439184073805601 (7 : ZMod 33694606196930439184073805601)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 2), (19, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 2), (19, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 33694606196930439184073805601 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_5
      · exact prime_oneHundredFourteenDH_19
      · exact prime_oneHundredFourteenDH_171401
      · exact prime_oneHundredFourteenDH_714027719
      · exact prime_oneHundredFourteenDH_6037638679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 33694606196930439184073805601) ^ 16847303098465219592036902800 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (7 : ZMod 33694606196930439184073805601) ^ 11231535398976813061357935200 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (7 : ZMod 33694606196930439184073805601) ^ 6738921239386087836814761120 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (7 : ZMod 33694606196930439184073805601) ^ 1773400326154233641267042400 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (7 : ZMod 33694606196930439184073805601) ^ 196583486659531969965600 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (7 : ZMod 33694606196930439184073805601) ^ 47189493209199122400 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (7 : ZMod 33694606196930439184073805601) ^ 5580758966932946400 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_44926141595907252245431740803 : Nat.Prime 44926141595907252245431740803 := by
  apply lucas_primality 44926141595907252245431740803 (2 : ZMod 44926141595907252245431740803)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1489, 1), (74197, 1), (125471, 1), (28901293, 1), (56069599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1489, 1), (74197, 1), (125471, 1), (28901293, 1), (56069599, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907252245431740803 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_1489
      · exact prime_oneHundredFourteenDH_74197
      · exact prime_oneHundredFourteenDH_125471
      · exact prime_oneHundredFourteenDH_28901293
      · exact prime_oneHundredFourteenDH_56069599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 44926141595907252245431740803) ^ 22463070797953626122715870401 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 44926141595907252245431740803) ^ 30172022562731532737026018 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 44926141595907252245431740803) ^ 605498087468593773945466 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 44926141595907252245431740803) ^ 358059962827324658649662 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 44926141595907252245431740803) ^ 1554468223823316563914 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (2 : ZMod 44926141595907252245431740803) ^ 801256695199608119998 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem prime_oneHundredFourteenDH_134778424787721756736295222431 : Nat.Prime 134778424787721756736295222431 := by
  apply lucas_primality 134778424787721756736295222431 (15 : ZMod 134778424787721756736295222431)
  · rw [← oneHundredFourteenDHFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (1497538053196908408181058027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (1497538053196908408181058027, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFourteenDH_2
      · exact prime_oneHundredFourteenDH_3
      · exact prime_oneHundredFourteenDH_5
      · exact prime_oneHundredFourteenDH_1497538053196908408181058027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (15 : ZMod 134778424787721756736295222431) ^ 67389212393860878368147611215 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (15 : ZMod 134778424787721756736295222431) ^ 44926141595907252245431740810 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (15 : ZMod 134778424787721756736295222431) ^ 26955684957544351347259044486 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide
    · change (15 : ZMod 134778424787721756736295222431) ^ 90 ≠ 1
      rw [← oneHundredFourteenDHFastPow_eq_pow]
      decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222400 : Nat.totient 134778424787721756736295222400 = 34049087556049349416194048000 := by
  rw [← show ((([(2, 7), (3, 1), (5, 2), (19, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222400 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_2, prime_oneHundredFourteenDH_3, prime_oneHundredFourteenDH_5, prime_oneHundredFourteenDH_19, prime_oneHundredFourteenDH_171401, prime_oneHundredFourteenDH_714027719, prime_oneHundredFourteenDH_6037638679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222401 : Nat.totient 134778424787721756736295222401 = 117540035869467661279862796288 := by
  rw [← show ((([(13, 1), (37, 1), (47, 1), (127, 1), (16885513, 1), (2780093878793993, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222401 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_13, prime_oneHundredFourteenDH_37, prime_oneHundredFourteenDH_47, prime_oneHundredFourteenDH_127, prime_oneHundredFourteenDH_16885513, prime_oneHundredFourteenDH_2780093878793993]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222402 : Nat.totient 134778424787721756736295222402 = 60398378688376119728596896000 := by
  rw [← show ((([(2, 1), (11, 1), (71, 1), (38317, 1), (573197, 1), (55926539, 1), (70246711, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222402 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_2, prime_oneHundredFourteenDH_11, prime_oneHundredFourteenDH_71, prime_oneHundredFourteenDH_38317, prime_oneHundredFourteenDH_573197, prime_oneHundredFourteenDH_55926539, prime_oneHundredFourteenDH_70246711]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222403 : Nat.totient 134778424787721756736295222403 = 85945657128456834495602027520 := by
  rw [← show ((([(3, 2), (23, 1), (17002049, 1), (38295590219153007821, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222403 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_3, prime_oneHundredFourteenDH_23, prime_oneHundredFourteenDH_17002049, prime_oneHundredFourteenDH_38295590219153007821]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222404 : Nat.totient 134778424787721756736295222404 = 67389212393860878368147611200 := by
  rw [← show ((([(2, 2), (33694606196930439184073805601, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222404 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_2, prime_oneHundredFourteenDH_33694606196930439184073805601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222405 : Nat.totient 134778424787721756736295222405 = 92419491282998749787588711040 := by
  rw [← show ((([(5, 1), (7, 1), (9026940933193, 1), (426591041781631, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222405 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_5, prime_oneHundredFourteenDH_7, prime_oneHundredFourteenDH_9026940933193, prime_oneHundredFourteenDH_426591041781631]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222406 : Nat.totient 134778424787721756736295222406 = 44895004313142031616294737920 := by
  rw [← show ((([(2, 1), (3, 1), (1489, 1), (74197, 1), (125471, 1), (28901293, 1), (56069599, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222406 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_2, prime_oneHundredFourteenDH_3, prime_oneHundredFourteenDH_1489, prime_oneHundredFourteenDH_74197, prime_oneHundredFourteenDH_125471, prime_oneHundredFourteenDH_28901293, prime_oneHundredFourteenDH_56069599]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222407 : Nat.totient 134778424787721756736295222407 = 124355627377099880899534940160 := by
  rw [← show ((([(17, 1), (59, 1), (389, 1), (5563, 1), (72077, 1), (861517452837871, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222407 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_17, prime_oneHundredFourteenDH_59, prime_oneHundredFourteenDH_389, prime_oneHundredFourteenDH_5563, prime_oneHundredFourteenDH_72077, prime_oneHundredFourteenDH_861517452837871]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222408 : Nat.totient 134778424787721756736295222408 = 67389210726926955218560709760 := by
  rw [← show ((([(2, 3), (41462027, 1), (1630123721, 1), (249263846203, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222408 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_2, prime_oneHundredFourteenDH_41462027, prime_oneHundredFourteenDH_1630123721, prime_oneHundredFourteenDH_249263846203]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222409 : Nat.totient 134778424787721756736295222409 = 89852283191814504490863481604 := by
  rw [← show ((([(3, 1), (44926141595907252245431740803, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222409 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_3, prime_oneHundredFourteenDH_44926141595907252245431740803]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222410 : Nat.totient 134778424787721756736295222410 = 53824538801260786995608832000 := by
  rw [← show ((([(2, 1), (5, 1), (947, 1), (1801, 1), (7371456913, 1), (1072021148531, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222410 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_2, prime_oneHundredFourteenDH_5, prime_oneHundredFourteenDH_947, prime_oneHundredFourteenDH_1801, prime_oneHundredFourteenDH_7371456913, prime_oneHundredFourteenDH_1072021148531]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222411 : Nat.totient 134778424787721756736295222411 = 134778388787482286140318776960 := by
  rw [← show ((([(3744023, 1), (82057035997, 1), (438698392081, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222411 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_3744023, prime_oneHundredFourteenDH_82057035997, prime_oneHundredFourteenDH_438698392081]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222412 : Nat.totient 134778424787721756736295222412 = 38313057029537256826720896000 := by
  rw [← show ((([(2, 2), (3, 3), (7, 1), (277, 1), (743, 1), (9091, 1), (201451, 1), (472986682277, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222412 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_2, prime_oneHundredFourteenDH_3, prime_oneHundredFourteenDH_7, prime_oneHundredFourteenDH_277, prime_oneHundredFourteenDH_743, prime_oneHundredFourteenDH_9091, prime_oneHundredFourteenDH_201451, prime_oneHundredFourteenDH_472986682277]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222413 : Nat.totient 134778424787721756736295222413 = 121262687719037381880827940480 := by
  rw [← show ((([(11, 1), (97, 1), (126315299707330606125862439, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222413 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_11, prime_oneHundredFourteenDH_97, prime_oneHundredFourteenDH_126315299707330606125862439]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222414 : Nat.totient 134778424787721756736295222414 = 62175886625019329947264435200 := by
  rw [← show ((([(2, 1), (13, 1), (2203, 1), (47881, 1), (12603781, 1), (3899136783133, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222414 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_2, prime_oneHundredFourteenDH_13, prime_oneHundredFourteenDH_2203, prime_oneHundredFourteenDH_47881, prime_oneHundredFourteenDH_12603781, prime_oneHundredFourteenDH_3899136783133]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222415 : Nat.totient 134778424787721756736295222415 = 71881618199082079427819568000 := by
  rw [← show ((([(3, 1), (5, 1), (470501, 1), (1293367, 1), (14765453512034683, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222415 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_3, prime_oneHundredFourteenDH_5, prime_oneHundredFourteenDH_470501, prime_oneHundredFourteenDH_1293367, prime_oneHundredFourteenDH_14765453512034683]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222416 : Nat.totient 134778424787721756736295222416 = 65713556580694634941946265600 := by
  rw [← show ((([(2, 4), (43, 1), (607, 1), (2527477, 1), (130246913, 1), (980366801, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222416 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_2, prime_oneHundredFourteenDH_43, prime_oneHundredFourteenDH_607, prime_oneHundredFourteenDH_2527477, prime_oneHundredFourteenDH_130246913, prime_oneHundredFourteenDH_980366801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222417 : Nat.totient 134778424787721756736295222417 = 134778424778454463008211695156 := by
  rw [← show ((([(14543450219, 1), (9267293713540077043, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222417 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_14543450219, prime_oneHundredFourteenDH_9267293713540077043]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222418 : Nat.totient 134778424787721756736295222418 = 43263708090025369354334044160 := by
  rw [← show ((([(2, 1), (3, 1), (29, 1), (383, 1), (101080961, 1), (20007968354627489, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222418 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_2, prime_oneHundredFourteenDH_3, prime_oneHundredFourteenDH_29, prime_oneHundredFourteenDH_383, prime_oneHundredFourteenDH_101080961, prime_oneHundredFourteenDH_20007968354627489]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222419 : Nat.totient 134778424787721756736295222419 = 109349213222056812148125434880 := by
  rw [← show ((([(7, 1), (19, 1), (1153, 1), (878899926231809511221431, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222419 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_7, prime_oneHundredFourteenDH_19, prime_oneHundredFourteenDH_1153, prime_oneHundredFourteenDH_878899926231809511221431]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222420 : Nat.totient 134778424787721756736295222420 = 53906518716500104772922164736 := by
  rw [← show ((([(2, 2), (5, 1), (11113, 1), (606399823574740199479417, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222420 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_2, prime_oneHundredFourteenDH_5, prime_oneHundredFourteenDH_11113, prime_oneHundredFourteenDH_606399823574740199479417]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222421 : Nat.totient 134778424787721756736295222421 = 87660764089366061336610816000 := by
  rw [← show ((([(3, 2), (41, 1), (419501118209, 1), (870684648627301, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222421 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_3, prime_oneHundredFourteenDH_41, prime_oneHundredFourteenDH_419501118209, prime_oneHundredFourteenDH_870684648627301]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222422 : Nat.totient 134778424787721756736295222422 = 66641619007912290984290670624 := by
  rw [← show ((([(2, 1), (107, 1), (1063, 1), (1213, 1), (488441478919661500867, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222422 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_2, prime_oneHundredFourteenDH_107, prime_oneHundredFourteenDH_1063, prime_oneHundredFourteenDH_1213, prime_oneHundredFourteenDH_488441478919661500867]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222423 : Nat.totient 134778424787721756736295222423 = 132568682255189945581947079680 := by
  rw [← show ((([(61, 1), (509569, 1), (4335982710033791550947, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222423 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_61, prime_oneHundredFourteenDH_509569, prime_oneHundredFourteenDH_4335982710033791550947]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222424 : Nat.totient 134778424787721756736295222424 = 38246316029829497118121021440 := by
  rw [← show ((([(2, 3), (3, 1), (11, 2), (17, 1), (199, 1), (193897349, 1), (70753820440643, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222424 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_2, prime_oneHundredFourteenDH_3, prime_oneHundredFourteenDH_11, prime_oneHundredFourteenDH_17, prime_oneHundredFourteenDH_199, prime_oneHundredFourteenDH_193897349, prime_oneHundredFourteenDH_70753820440643]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222425 : Nat.totient 134778424787721756736295222425 = 104344586932429747150680171600 := by
  rw [← show ((([(5, 2), (31, 1), (173907644887382911917800287, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222425 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_5, prime_oneHundredFourteenDH_31, prime_oneHundredFourteenDH_173907644887382911917800287]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222426 : Nat.totient 134778424787721756736295222426 = 55250782832233763631027855024 := by
  rw [← show ((([(2, 1), (7, 1), (23, 1), (418566536607831542659301933, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222426 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_2, prime_oneHundredFourteenDH_7, prime_oneHundredFourteenDH_23, prime_oneHundredFourteenDH_418566536607831542659301933]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222427 : Nat.totient 134778424787721756736295222427 = 82640860907359258097721244800 := by
  rw [← show ((([(3, 1), (13, 1), (283, 1), (12479, 1), (9130651, 1), (107173596754699, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222427 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_3, prime_oneHundredFourteenDH_13, prime_oneHundredFourteenDH_283, prime_oneHundredFourteenDH_12479, prime_oneHundredFourteenDH_9130651, prime_oneHundredFourteenDH_107173596754699]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222428 : Nat.totient 134778424787721756736295222428 = 67388954368402561562840957760 := by
  rw [← show ((([(2, 2), (271367, 1), (7825591, 1), (108632453, 1), (146058427, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222428 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_2, prime_oneHundredFourteenDH_271367, prime_oneHundredFourteenDH_7825591, prime_oneHundredFourteenDH_108632453, prime_oneHundredFourteenDH_146058427]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222429 : Nat.totient 134778424787721756736295222429 = 134336388718315824317608815792 := by
  rw [← show ((([(307, 1), (44507, 1), (12629177423, 1), (781049600627, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222429 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_307, prime_oneHundredFourteenDH_44507, prime_oneHundredFourteenDH_12629177423, prime_oneHundredFourteenDH_781049600627]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222430 : Nat.totient 134778424787721756736295222430 = 35940913276725801796345392624 := by
  rw [← show ((([(2, 1), (3, 2), (5, 1), (1497538053196908408181058027, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222430 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_2, prime_oneHundredFourteenDH_3, prime_oneHundredFourteenDH_5, prime_oneHundredFourteenDH_1497538053196908408181058027]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222431 : Nat.totient 134778424787721756736295222431 = 134778424787721756736295222430 := by
  rw [← show ((([(134778424787721756736295222431, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222431 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_134778424787721756736295222431]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222432 : Nat.totient 134778424787721756736295222432 = 67389109939069634633731672320 := by
  rw [← show ((([(2, 5), (670693, 1), (34072711, 1), (184306195621687, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222432 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_2, prime_oneHundredFourteenDH_670693, prime_oneHundredFourteenDH_34072711, prime_oneHundredFourteenDH_184306195621687]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222433 : Nat.totient 134778424787721756736295222433 = 76643801626284978231953479680 := by
  rw [← show ((([(3, 1), (7, 1), (211, 1), (21227, 1), (49529, 1), (52147, 1), (96589, 1), (5743987, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222433 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_3, prime_oneHundredFourteenDH_7, prime_oneHundredFourteenDH_211, prime_oneHundredFourteenDH_21227, prime_oneHundredFourteenDH_49529, prime_oneHundredFourteenDH_52147, prime_oneHundredFourteenDH_96589, prime_oneHundredFourteenDH_5743987]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222434 : Nat.totient 134778424787721756736295222434 = 65303460193598128428628680000 := by
  rw [← show ((([(2, 1), (67, 1), (103, 1), (151, 1), (814327, 1), (9579811, 1), (8289830111, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222434 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_2, prime_oneHundredFourteenDH_67, prime_oneHundredFourteenDH_103, prime_oneHundredFourteenDH_151, prime_oneHundredFourteenDH_814327, prime_oneHundredFourteenDH_9579811, prime_oneHundredFourteenDH_8289830111]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222435 : Nat.totient 134778424787721756736295222435 = 96341775143138863722717696000 := by
  rw [← show ((([(5, 1), (11, 1), (101, 1), (137, 1), (307468349, 1), (575990512578109, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222435 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_5, prime_oneHundredFourteenDH_11, prime_oneHundredFourteenDH_101, prime_oneHundredFourteenDH_137, prime_oneHundredFourteenDH_307468349, prime_oneHundredFourteenDH_575990512578109]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222436 : Nat.totient 134778424787721756736295222436 = 44926012513582464566845670400 := by
  rw [← show ((([(2, 2), (3, 1), (352333, 1), (28581281, 1), (1115331887063311, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222436 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_2, prime_oneHundredFourteenDH_3, prime_oneHundredFourteenDH_352333, prime_oneHundredFourteenDH_28581281, prime_oneHundredFourteenDH_1115331887063311]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222437 : Nat.totient 134778424787721756736295222437 = 132498855790970335089655864320 := by
  rw [← show ((([(73, 1), (313, 1), (15461, 1), (8584327, 1), (44443611821879, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222437 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_73, prime_oneHundredFourteenDH_313, prime_oneHundredFourteenDH_15461, prime_oneHundredFourteenDH_8584327, prime_oneHundredFourteenDH_44443611821879]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222438 : Nat.totient 134778424787721756736295222438 = 62114948757588075450769615104 := by
  rw [← show ((([(2, 1), (19, 1), (37, 1), (31177, 1), (3074685732733041494149, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222438 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_2, prime_oneHundredFourteenDH_19, prime_oneHundredFourteenDH_37, prime_oneHundredFourteenDH_31177, prime_oneHundredFourteenDH_3074685732733041494149]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222439 : Nat.totient 134778424787721756736295222439 = 89852283191703869789430454848 := by
  rw [← show ((([(3, 3), (812260148269, 1), (6145560041686553, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222439 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_3, prime_oneHundredFourteenDH_812260148269, prime_oneHundredFourteenDH_6145560041686553]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222440 : Nat.totient 134778424787721756736295222440 = 42655099783863062473673859072 := by
  rw [← show ((([(2, 3), (5, 1), (7, 2), (13, 1), (852437, 1), (6205241104008965969, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222440 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_2, prime_oneHundredFourteenDH_5, prime_oneHundredFourteenDH_7, prime_oneHundredFourteenDH_13, prime_oneHundredFourteenDH_852437, prime_oneHundredFourteenDH_6205241104008965969]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222441 : Nat.totient 134778424787721756736295222441 = 124456880603090456830851969280 := by
  rw [← show ((([(17, 1), (53, 1), (149587596878714491383235541, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222441 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_17, prime_oneHundredFourteenDH_53, prime_oneHundredFourteenDH_149587596878714491383235541]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222442 : Nat.totient 134778424787721756736295222442 = 44922231915148753659386514480 := by
  rw [← show ((([(2, 1), (3, 1), (11491, 1), (1954840379249293022601677, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222442 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_2, prime_oneHundredFourteenDH_3, prime_oneHundredFourteenDH_11491, prime_oneHundredFourteenDH_1954840379249293022601677]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222443 : Nat.totient 134778424787721756736295222443 = 134769131645308598706997542528 := by
  rw [← show ((([(14503, 1), (99674756429, 1), (93234650302289, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222443 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_14503, prime_oneHundredFourteenDH_99674756429, prime_oneHundredFourteenDH_93234650302289]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222444 : Nat.totient 134778424787721756736295222444 = 67061431770560328167061336000 := by
  rw [← show ((([(2, 2), (331, 1), (541, 1), (188163388806285993734741, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222444 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_2, prime_oneHundredFourteenDH_331, prime_oneHundredFourteenDH_541, prime_oneHundredFourteenDH_188163388806285993734741]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222445 : Nat.totient 134778424787721756736295222445 = 71684907075546494707187654400 := by
  rw [← show ((([(3, 1), (5, 1), (479, 1), (1531, 1), (466649147, 1), (26255962099621, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222445 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_3, prime_oneHundredFourteenDH_5, prime_oneHundredFourteenDH_479, prime_oneHundredFourteenDH_1531, prime_oneHundredFourteenDH_466649147, prime_oneHundredFourteenDH_26255962099621]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222446 : Nat.totient 134778424787721756736295222446 = 61261725753208551557494985400 := by
  rw [← show ((([(2, 1), (11, 1), (51283, 1), (119460484679241354778471, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222446 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_2, prime_oneHundredFourteenDH_11, prime_oneHundredFourteenDH_51283, prime_oneHundredFourteenDH_119460484679241354778471]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222447 : Nat.totient 134778424787721756736295222447 = 111540659864116732661175781248 := by
  rw [← show ((([(7, 1), (29, 1), (2904623, 1), (3282203, 1), (4241059, 1), (16420819, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222447 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_7, prime_oneHundredFourteenDH_29, prime_oneHundredFourteenDH_2904623, prime_oneHundredFourteenDH_3282203, prime_oneHundredFourteenDH_4241059, prime_oneHundredFourteenDH_16420819]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222448 : Nat.totient 134778424787721756736295222448 = 43890783864968268320956416000 := by
  rw [← show ((([(2, 4), (3, 2), (47, 1), (563, 1), (40771, 1), (283277, 1), (299281, 1), (10233161, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222448 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_2, prime_oneHundredFourteenDH_3, prime_oneHundredFourteenDH_47, prime_oneHundredFourteenDH_563, prime_oneHundredFourteenDH_40771, prime_oneHundredFourteenDH_283277, prime_oneHundredFourteenDH_299281, prime_oneHundredFourteenDH_10233161]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222449 : Nat.totient 134778424787721756736295222449 = 128918493275212115139064994880 := by
  rw [← show ((([(23, 2), (254779630978680069444792481, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222449 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_23, prime_oneHundredFourteenDH_254779630978680069444792481]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222450 : Nat.totient 134778424787721756736295222450 = 53911369915088702694518088960 := by
  rw [← show ((([(2, 1), (5, 2), (2695568495754435134725904449, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222450 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_2, prime_oneHundredFourteenDH_5, prime_oneHundredFourteenDH_2695568495754435134725904449]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222451 : Nat.totient 134778424787721756736295222451 = 88713210619052538715703589888 := by
  rw [← show ((([(3, 1), (79, 1), (52127, 1), (10909611845244380568449, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222451 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_3, prime_oneHundredFourteenDH_79, prime_oneHundredFourteenDH_52127, prime_oneHundredFourteenDH_10909611845244380568449]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222452 : Nat.totient 134778424787721756736295222452 = 67389212393774135730957104000 := by
  rw [← show ((([(2, 2), (776900746001, 1), (43370541694507613, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222452 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_2, prime_oneHundredFourteenDH_776900746001, prime_oneHundredFourteenDH_43370541694507613]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222453 : Nat.totient 134778424787721756736295222453 = 124410853632035519092949451264 := by
  rw [← show ((([(13, 1), (6847356793, 1), (1514098279224436817, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222453 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_13, prime_oneHundredFourteenDH_6847356793, prime_oneHundredFourteenDH_1514098279224436817]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222454 : Nat.totient 134778424787721756736295222454 = 38497316647274909505850195200 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (7817, 1), (9887, 1), (19403, 1), (2139920090441051, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222454 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_2, prime_oneHundredFourteenDH_3, prime_oneHundredFourteenDH_7, prime_oneHundredFourteenDH_7817, prime_oneHundredFourteenDH_9887, prime_oneHundredFourteenDH_19403, prime_oneHundredFourteenDH_2139920090441051]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222455 : Nat.totient 134778424787721756736295222455 = 107822739830169104267221555200 := by
  rw [← show ((([(5, 1), (13071266057611, 1), (2062209187598081, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222455 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_5, prime_oneHundredFourteenDH_13071266057611, prime_oneHundredFourteenDH_2062209187598081]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222456 : Nat.totient 134778424787721756736295222456 = 65206658677222800346884986880 := by
  rw [← show ((([(2, 3), (31, 1), (7489, 1), (50285095027, 1), (1443130447699, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222456 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_2, prime_oneHundredFourteenDH_31, prime_oneHundredFourteenDH_7489, prime_oneHundredFourteenDH_50285095027, prime_oneHundredFourteenDH_1443130447699]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222457 : Nat.totient 134778424787721756736295222457 = 77215775579529726775957632000 := by
  rw [← show ((([(3, 2), (11, 1), (19, 1), (461, 1), (69997, 1), (2220502305087140441, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222457 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_3, prime_oneHundredFourteenDH_11, prime_oneHundredFourteenDH_19, prime_oneHundredFourteenDH_461, prime_oneHundredFourteenDH_69997, prime_oneHundredFourteenDH_2220502305087140441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222458 : Nat.totient 134778424787721756736295222458 = 63195677816757613203583825920 := by
  rw [← show ((([(2, 1), (17, 1), (281, 1), (16879, 1), (9362069, 1), (89272272147727, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222458 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_2, prime_oneHundredFourteenDH_17, prime_oneHundredFourteenDH_281, prime_oneHundredFourteenDH_16879, prime_oneHundredFourteenDH_9362069, prime_oneHundredFourteenDH_89272272147727]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222459 : Nat.totient 134778424787721756736295222459 = 131537217207209561319217814784 := by
  rw [← show ((([(43, 1), (1259, 1), (62047, 1), (918389, 1), (43689666467129, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222459 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_43, prime_oneHundredFourteenDH_1259, prime_oneHundredFourteenDH_62047, prime_oneHundredFourteenDH_918389, prime_oneHundredFourteenDH_43689666467129]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222460 : Nat.totient 134778424787721756736295222460 = 35940913276725801796345392640 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (2246307079795362612271587041, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222460 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_2, prime_oneHundredFourteenDH_3, prime_oneHundredFourteenDH_5, prime_oneHundredFourteenDH_2246307079795362612271587041]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222461 : Nat.totient 134778424787721756736295222461 = 115524354629656638008071732608 := by
  rw [← show ((([(7, 1), (12193697, 1), (1579017477960970406459, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222461 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_7, prime_oneHundredFourteenDH_12193697, prime_oneHundredFourteenDH_1579017477960970406459]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222462 : Nat.totient 134778424787721756736295222462 = 65745573066640700266681536000 := by
  rw [← show ((([(2, 1), (41, 1), (121607020321, 1), (13515990461248871, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222462 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_2, prime_oneHundredFourteenDH_41, prime_oneHundredFourteenDH_121607020321, prime_oneHundredFourteenDH_13515990461248871]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222463 : Nat.totient 134778424787721756736295222463 = 89852046621304518685888106496 := by
  rw [← show ((([(3, 1), (390989, 1), (20637977, 1), (72827129, 1), (76449433, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222463 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_3, prime_oneHundredFourteenDH_390989, prime_oneHundredFourteenDH_20637977, prime_oneHundredFourteenDH_72827129, prime_oneHundredFourteenDH_76449433]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222464 : Nat.totient 134778424787721756736295222464 = 67279200790737677926109193216 := by
  rw [← show ((([(2, 6), (619, 1), (59693, 1), (4046719, 1), (14083911874787, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222464 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_2, prime_oneHundredFourteenDH_619, prime_oneHundredFourteenDH_59693, prime_oneHundredFourteenDH_4046719, prime_oneHundredFourteenDH_14083911874787]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222465 : Nat.totient 134778424787721756736295222465 = 107616570737382329414298624000 := by
  rw [← show ((([(5, 1), (523, 1), (15229441, 1), (3384267788357002951, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222465 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_5, prime_oneHundredFourteenDH_523, prime_oneHundredFourteenDH_15229441, prime_oneHundredFourteenDH_3384267788357002951]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222466 : Nat.totient 134778424787721756736295222466 = 40767113565374200410049257600 := by
  rw [← show ((([(2, 1), (3, 6), (13, 1), (59, 1), (143141, 1), (841983229614766891, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222466 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_2, prime_oneHundredFourteenDH_3, prime_oneHundredFourteenDH_13, prime_oneHundredFourteenDH_59, prime_oneHundredFourteenDH_143141, prime_oneHundredFourteenDH_841983229614766891]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222467 : Nat.totient 134778424787721756736295222467 = 134778424172940289868316129760 := by
  rw [← show ((([(219229811, 1), (614781466867759862897, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222467 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_219229811, prime_oneHundredFourteenDH_614781466867759862897]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222468 : Nat.totient 134778424787721756736295222468 = 51878411043310205221606350240 := by
  rw [← show ((([(2, 2), (7, 1), (11, 1), (83, 1), (5272196244238841994065687, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222468 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_2, prime_oneHundredFourteenDH_7, prime_oneHundredFourteenDH_11, prime_oneHundredFourteenDH_83, prime_oneHundredFourteenDH_5272196244238841994065687]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222469 : Nat.totient 134778424787721756736295222469 = 89851724692617996255303128448 := by
  rw [← show ((([(3, 1), (160883, 1), (19481132537, 1), (14334243066613, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222469 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_3, prime_oneHundredFourteenDH_160883, prime_oneHundredFourteenDH_19481132537, prime_oneHundredFourteenDH_14334243066613]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222470 : Nat.totient 134778424787721756736295222470 = 53844294897543365570248387200 := by
  rw [← show ((([(2, 1), (5, 1), (823, 1), (34351, 1), (34063123, 1), (13995766681093, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222470 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_2, prime_oneHundredFourteenDH_5, prime_oneHundredFourteenDH_823, prime_oneHundredFourteenDH_34351, prime_oneHundredFourteenDH_34063123, prime_oneHundredFourteenDH_13995766681093]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222471 : Nat.totient 134778424787721756736295222471 = 133696472396163521985118702080 := by
  rw [← show ((([(139, 1), (1193, 1), (826153, 1), (983795084090656741, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222471 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_139, prime_oneHundredFourteenDH_1193, prime_oneHundredFourteenDH_826153, prime_oneHundredFourteenDH_983795084090656741]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222472 : Nat.totient 134778424787721756736295222472 = 42971513028028763996802295872 := by
  rw [← show ((([(2, 3), (3, 1), (23, 1), (32603, 1), (7488998344362023941087, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222472 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_2, prime_oneHundredFourteenDH_3, prime_oneHundredFourteenDH_23, prime_oneHundredFourteenDH_32603, prime_oneHundredFourteenDH_7488998344362023941087]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222473 : Nat.totient 134778424787721756736295222473 = 131614487714713647717673205760 := by
  rw [← show ((([(71, 1), (193, 1), (557, 1), (593, 1), (1123, 1), (26516431262501417, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222473 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_71, prime_oneHundredFourteenDH_193, prime_oneHundredFourteenDH_557, prime_oneHundredFourteenDH_593, prime_oneHundredFourteenDH_1123, prime_oneHundredFourteenDH_26516431262501417]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222474 : Nat.totient 134778424787721756736295222474 = 67092334502849032133998025952 := by
  rw [← show ((([(2, 1), (227, 1), (7361503, 1), (40327196370831666377, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222474 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_2, prime_oneHundredFourteenDH_227, prime_oneHundredFourteenDH_7361503, prime_oneHundredFourteenDH_40327196370831666377]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222475 : Nat.totient 134778424787721756736295222475 = 56352279069720920103966720000 := by
  rw [← show ((([(3, 2), (5, 2), (7, 1), (17, 1), (37, 1), (1279, 1), (2251, 1), (47254495754060453, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222475 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_3, prime_oneHundredFourteenDH_5, prime_oneHundredFourteenDH_7, prime_oneHundredFourteenDH_17, prime_oneHundredFourteenDH_37, prime_oneHundredFourteenDH_1279, prime_oneHundredFourteenDH_2251, prime_oneHundredFourteenDH_47254495754060453]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222476 : Nat.totient 134778424787721756736295222476 = 60959384087675759852610060288 := by
  rw [← show ((([(2, 2), (19, 1), (29, 1), (113, 1), (449, 1), (1205269042013298899237, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222476 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_2, prime_oneHundredFourteenDH_19, prime_oneHundredFourteenDH_29, prime_oneHundredFourteenDH_113, prime_oneHundredFourteenDH_449, prime_oneHundredFourteenDH_1205269042013298899237]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222477 : Nat.totient 134778424787721756736295222477 = 134753089050841486567908114432 := by
  rw [← show ((([(11777, 1), (18043, 1), (20983, 1), (30227997071821729, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222477 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_11777, prime_oneHundredFourteenDH_18043, prime_oneHundredFourteenDH_20983, prime_oneHundredFourteenDH_30227997071821729]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222478 : Nat.totient 134778424787721756736295222478 = 44926141595907252245431740824 := by
  rw [← show ((([(2, 1), (3, 1), (22463070797953626122715870413, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222478 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_2, prime_oneHundredFourteenDH_3, prime_oneHundredFourteenDH_22463070797953626122715870413]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222479 : Nat.totient 134778424787721756736295222479 = 113100776045640635023464522240 := by
  rw [← show ((([(11, 1), (13, 1), (942506467047005291862204353, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222479 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_11, prime_oneHundredFourteenDH_13, prime_oneHundredFourteenDH_942506467047005291862204353]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222480 : Nat.totient 134778424787721756736295222480 = 53848555932677783526940107264 := by
  rw [← show ((([(2, 4), (5, 1), (863, 1), (156419, 1), (12480445510527170173, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222480 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_2, prime_oneHundredFourteenDH_5, prime_oneHundredFourteenDH_863, prime_oneHundredFourteenDH_156419, prime_oneHundredFourteenDH_12480445510527170173]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222481 : Nat.totient 134778424787721756736295222481 = 88836934595760560287849541760 := by
  rw [← show ((([(3, 1), (89, 2), (15391, 1), (368512539298964745557, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222481 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_3, prime_oneHundredFourteenDH_89, prime_oneHundredFourteenDH_15391, prime_oneHundredFourteenDH_368512539298964745557]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222482 : Nat.totient 134778424787721756736295222482 = 57762077965546604720273443968 := by
  rw [← show ((([(2, 1), (7, 1), (554969, 1), (12910955093, 1), (1343585305739, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222482 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_2, prime_oneHundredFourteenDH_7, prime_oneHundredFourteenDH_554969, prime_oneHundredFourteenDH_12910955093, prime_oneHundredFourteenDH_1343585305739]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222483 : Nat.totient 134778424787721756736295222483 = 134717705832555063912231014400 := by
  rw [← show ((([(2239, 1), (435181, 1), (693661, 1), (11896289, 1), (16762453, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222483 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_2239, prime_oneHundredFourteenDH_435181, prime_oneHundredFourteenDH_693661, prime_oneHundredFourteenDH_11896289, prime_oneHundredFourteenDH_16762453]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222484 : Nat.totient 134778424787721756736295222484 = 44189646536662531327401984000 := by
  rw [← show ((([(2, 2), (3, 2), (61, 1), (47275729, 1), (1298224515520902401, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222484 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_2, prime_oneHundredFourteenDH_3, prime_oneHundredFourteenDH_61, prime_oneHundredFourteenDH_47275729, prime_oneHundredFourteenDH_1298224515520902401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222485 : Nat.totient 134778424787721756736295222485 = 107822739830177405389036177984 := by
  rw [← show ((([(5, 1), (26955684957544351347259044497, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222485 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_5, prime_oneHundredFourteenDH_26955684957544351347259044497]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222486 : Nat.totient 134778424787721756736295222486 = 67382815611715683009329931360 := by
  rw [← show ((([(2, 1), (10789, 1), (447197, 1), (13967230684837612571, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222486 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_2, prime_oneHundredFourteenDH_10789, prime_oneHundredFourteenDH_447197, prime_oneHundredFourteenDH_13967230684837612571]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222487 : Nat.totient 134778424787721756736295222487 = 86953822442812204610019816960 := by
  rw [← show ((([(3, 1), (31, 1), (98895963457, 1), (14654090252041987, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222487 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_3, prime_oneHundredFourteenDH_31, prime_oneHundredFourteenDH_98895963457, prime_oneHundredFourteenDH_14654090252041987]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222488 : Nat.totient 134778424787721756736295222488 = 67189237708510189430323103232 := by
  rw [← show ((([(2, 3), (337, 1), (10034159, 1), (4982181100062557317, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222488 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_2, prime_oneHundredFourteenDH_337, prime_oneHundredFourteenDH_10034159, prime_oneHundredFourteenDH_4982181100062557317]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222489 : Nat.totient 134778424787721756736295222489 = 115524116069427035891853942240 := by
  rw [← show ((([(7, 2), (507109, 1), (5712059, 1), (949577232649231, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222489 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_7, prime_oneHundredFourteenDH_507109, prime_oneHundredFourteenDH_5712059, prime_oneHundredFourteenDH_949577232649231]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222490 : Nat.totient 134778424787721756736295222490 = 32371298469875916950248857600 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (11, 1), (109, 1), (12941, 1), (289542354222801077537, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222490 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_2, prime_oneHundredFourteenDH_3, prime_oneHundredFourteenDH_5, prime_oneHundredFourteenDH_11, prime_oneHundredFourteenDH_109, prime_oneHundredFourteenDH_12941, prime_oneHundredFourteenDH_289542354222801077537]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222491 : Nat.totient 134778424787721756736295222491 = 133654155391442833276395847680 := by
  rw [← show ((([(229, 1), (487, 1), (641, 1), (2789, 1), (40277, 1), (16783876450529, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222491 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_229, prime_oneHundredFourteenDH_487, prime_oneHundredFourteenDH_641, prime_oneHundredFourteenDH_2789, prime_oneHundredFourteenDH_40277, prime_oneHundredFourteenDH_16783876450529]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222492 : Nat.totient 134778424787721756736295222492 = 58520392443120124268646236160 := by
  rw [← show ((([(2, 2), (13, 1), (17, 1), (2297, 1), (161561, 1), (1418513, 1), (289625811203, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222492 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_2, prime_oneHundredFourteenDH_13, prime_oneHundredFourteenDH_17, prime_oneHundredFourteenDH_2297, prime_oneHundredFourteenDH_161561, prime_oneHundredFourteenDH_1418513, prime_oneHundredFourteenDH_289625811203]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222493 : Nat.totient 134778424787721756736295222493 = 89852282367157313923742058672 := by
  rw [← show ((([(3, 3), (108957133, 1), (45814288364731121923, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222493 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_3, prime_oneHundredFourteenDH_108957133, prime_oneHundredFourteenDH_45814288364731121923]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222494 : Nat.totient 134778424787721756736295222494 = 65841066467519300934931229184 := by
  rw [← show ((([(2, 1), (53, 1), (239, 1), (8046989, 1), (661124425155551569, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222494 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_2, prime_oneHundredFourteenDH_53, prime_oneHundredFourteenDH_239, prime_oneHundredFourteenDH_8046989, prime_oneHundredFourteenDH_661124425155551569]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222495 : Nat.totient 134778424787721756736295222495 = 95591036919852641949264248832 := by
  rw [← show ((([(5, 1), (19, 1), (23, 1), (47, 1), (2609, 1), (1030817, 1), (487995060087097, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222495 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_5, prime_oneHundredFourteenDH_19, prime_oneHundredFourteenDH_23, prime_oneHundredFourteenDH_47, prime_oneHundredFourteenDH_2609, prime_oneHundredFourteenDH_1030817, prime_oneHundredFourteenDH_487995060087097]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222496 : Nat.totient 134778424787721756736295222496 = 38507729717044799029414084608 := by
  rw [← show ((([(2, 5), (3, 1), (7, 1), (98323, 1), (44444387353, 1), (45896446097, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222496 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_2, prime_oneHundredFourteenDH_3, prime_oneHundredFourteenDH_7, prime_oneHundredFourteenDH_98323, prime_oneHundredFourteenDH_44444387353, prime_oneHundredFourteenDH_45896446097]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222497 : Nat.totient 134778424787721756736295222497 = 134687538498847780728756764160 := by
  rw [← show ((([(1483, 1), (33617411, 1), (2703428958055696769, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222497 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_1483, prime_oneHundredFourteenDH_33617411, prime_oneHundredFourteenDH_2703428958055696769]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222498 : Nat.totient 134778424787721756736295222498 = 67388252419032491676280980000 := by
  rw [← show ((([(2, 1), (70199, 1), (78585370601, 1), (12215682868351, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222498 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_2, prime_oneHundredFourteenDH_70199, prime_oneHundredFourteenDH_78585370601, prime_oneHundredFourteenDH_12215682868351]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222499 : Nat.totient 134778424787721756736295222499 = 89658606947529628803302367552 := by
  rw [← show ((([(3, 1), (617, 1), (1867, 1), (39000451930099816262347, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222499 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_3, prime_oneHundredFourteenDH_617, prime_oneHundredFourteenDH_1867, prime_oneHundredFourteenDH_39000451930099816262347]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222500 : Nat.totient 134778424787721756736295222500 = 53909904653492336844925824000 := by
  rw [← show ((([(2, 2), (5, 4), (36793, 1), (1465261596365849555473, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222500 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_2, prime_oneHundredFourteenDH_5, prime_oneHundredFourteenDH_36793, prime_oneHundredFourteenDH_1465261596365849555473]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222501 : Nat.totient 134778424787721756736295222501 = 120016581508055142012564000000 := by
  rw [← show ((([(11, 1), (67, 1), (347, 1), (373, 1), (11971, 1), (18723751, 1), (6303638423, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222501 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_11, prime_oneHundredFourteenDH_67, prime_oneHundredFourteenDH_347, prime_oneHundredFourteenDH_373, prime_oneHundredFourteenDH_11971, prime_oneHundredFourteenDH_18723751, prime_oneHundredFourteenDH_6303638423]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFourteenDH_134778424787721756736295222502 : Nat.totient 134778424787721756736295222502 = 43881347605304758007165886144 := by
  rw [← show ((([(2, 1), (3, 2), (43, 1), (174132331767082373044309073, 1)] : List FactorBlock).map factorBlockValue).prod) = 134778424787721756736295222502 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFourteenDH_2, prime_oneHundredFourteenDH_3, prime_oneHundredFourteenDH_43, prime_oneHundredFourteenDH_174132331767082373044309073]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64OneHundredFourteenDH : certifiedKill 2 134778424787721756736295222399 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_oneHundredFourteenDH_134778424787721756736295222400, phi_oneHundredFourteenDH_134778424787721756736295222401, phi_oneHundredFourteenDH_134778424787721756736295222402,
    phi_oneHundredFourteenDH_134778424787721756736295222403, phi_oneHundredFourteenDH_134778424787721756736295222404, phi_oneHundredFourteenDH_134778424787721756736295222405,
    phi_oneHundredFourteenDH_134778424787721756736295222406, phi_oneHundredFourteenDH_134778424787721756736295222407, phi_oneHundredFourteenDH_134778424787721756736295222408,
    phi_oneHundredFourteenDH_134778424787721756736295222409, phi_oneHundredFourteenDH_134778424787721756736295222410, phi_oneHundredFourteenDH_134778424787721756736295222411,
    phi_oneHundredFourteenDH_134778424787721756736295222412, phi_oneHundredFourteenDH_134778424787721756736295222413, phi_oneHundredFourteenDH_134778424787721756736295222414,
    phi_oneHundredFourteenDH_134778424787721756736295222415, phi_oneHundredFourteenDH_134778424787721756736295222416, phi_oneHundredFourteenDH_134778424787721756736295222417,
    phi_oneHundredFourteenDH_134778424787721756736295222418, phi_oneHundredFourteenDH_134778424787721756736295222419, phi_oneHundredFourteenDH_134778424787721756736295222420,
    phi_oneHundredFourteenDH_134778424787721756736295222421, phi_oneHundredFourteenDH_134778424787721756736295222422, phi_oneHundredFourteenDH_134778424787721756736295222423,
    phi_oneHundredFourteenDH_134778424787721756736295222424, phi_oneHundredFourteenDH_134778424787721756736295222425, phi_oneHundredFourteenDH_134778424787721756736295222426,
    phi_oneHundredFourteenDH_134778424787721756736295222427, phi_oneHundredFourteenDH_134778424787721756736295222428, phi_oneHundredFourteenDH_134778424787721756736295222429,
    phi_oneHundredFourteenDH_134778424787721756736295222430, phi_oneHundredFourteenDH_134778424787721756736295222431, phi_oneHundredFourteenDH_134778424787721756736295222432,
    phi_oneHundredFourteenDH_134778424787721756736295222433, phi_oneHundredFourteenDH_134778424787721756736295222434, phi_oneHundredFourteenDH_134778424787721756736295222435,
    phi_oneHundredFourteenDH_134778424787721756736295222436, phi_oneHundredFourteenDH_134778424787721756736295222437, phi_oneHundredFourteenDH_134778424787721756736295222438,
    phi_oneHundredFourteenDH_134778424787721756736295222439, phi_oneHundredFourteenDH_134778424787721756736295222440, phi_oneHundredFourteenDH_134778424787721756736295222441,
    phi_oneHundredFourteenDH_134778424787721756736295222442, phi_oneHundredFourteenDH_134778424787721756736295222443, phi_oneHundredFourteenDH_134778424787721756736295222444,
    phi_oneHundredFourteenDH_134778424787721756736295222445, phi_oneHundredFourteenDH_134778424787721756736295222446, phi_oneHundredFourteenDH_134778424787721756736295222447,
    phi_oneHundredFourteenDH_134778424787721756736295222448, phi_oneHundredFourteenDH_134778424787721756736295222449, phi_oneHundredFourteenDH_134778424787721756736295222450,
    phi_oneHundredFourteenDH_134778424787721756736295222451, phi_oneHundredFourteenDH_134778424787721756736295222452, phi_oneHundredFourteenDH_134778424787721756736295222453,
    phi_oneHundredFourteenDH_134778424787721756736295222454, phi_oneHundredFourteenDH_134778424787721756736295222455, phi_oneHundredFourteenDH_134778424787721756736295222456,
    phi_oneHundredFourteenDH_134778424787721756736295222457, phi_oneHundredFourteenDH_134778424787721756736295222458, phi_oneHundredFourteenDH_134778424787721756736295222459,
    phi_oneHundredFourteenDH_134778424787721756736295222460, phi_oneHundredFourteenDH_134778424787721756736295222461, phi_oneHundredFourteenDH_134778424787721756736295222462,
    phi_oneHundredFourteenDH_134778424787721756736295222463, phi_oneHundredFourteenDH_134778424787721756736295222464, phi_oneHundredFourteenDH_134778424787721756736295222465,
    phi_oneHundredFourteenDH_134778424787721756736295222466, phi_oneHundredFourteenDH_134778424787721756736295222467, phi_oneHundredFourteenDH_134778424787721756736295222468,
    phi_oneHundredFourteenDH_134778424787721756736295222469, phi_oneHundredFourteenDH_134778424787721756736295222470, phi_oneHundredFourteenDH_134778424787721756736295222471,
    phi_oneHundredFourteenDH_134778424787721756736295222472, phi_oneHundredFourteenDH_134778424787721756736295222473, phi_oneHundredFourteenDH_134778424787721756736295222474,
    phi_oneHundredFourteenDH_134778424787721756736295222475, phi_oneHundredFourteenDH_134778424787721756736295222476, phi_oneHundredFourteenDH_134778424787721756736295222477,
    phi_oneHundredFourteenDH_134778424787721756736295222478, phi_oneHundredFourteenDH_134778424787721756736295222479, phi_oneHundredFourteenDH_134778424787721756736295222480,
    phi_oneHundredFourteenDH_134778424787721756736295222481, phi_oneHundredFourteenDH_134778424787721756736295222482, phi_oneHundredFourteenDH_134778424787721756736295222483,
    phi_oneHundredFourteenDH_134778424787721756736295222484, phi_oneHundredFourteenDH_134778424787721756736295222485, phi_oneHundredFourteenDH_134778424787721756736295222486,
    phi_oneHundredFourteenDH_134778424787721756736295222487, phi_oneHundredFourteenDH_134778424787721756736295222488, phi_oneHundredFourteenDH_134778424787721756736295222489,
    phi_oneHundredFourteenDH_134778424787721756736295222490, phi_oneHundredFourteenDH_134778424787721756736295222491, phi_oneHundredFourteenDH_134778424787721756736295222492,
    phi_oneHundredFourteenDH_134778424787721756736295222493, phi_oneHundredFourteenDH_134778424787721756736295222494, phi_oneHundredFourteenDH_134778424787721756736295222495,
    phi_oneHundredFourteenDH_134778424787721756736295222496, phi_oneHundredFourteenDH_134778424787721756736295222497, phi_oneHundredFourteenDH_134778424787721756736295222498,
    phi_oneHundredFourteenDH_134778424787721756736295222499, phi_oneHundredFourteenDH_134778424787721756736295222500, phi_oneHundredFourteenDH_134778424787721756736295222501,
    phi_oneHundredFourteenDH_134778424787721756736295222502
    ]

end TotientTailPeriodKiller
end Erdos249257
