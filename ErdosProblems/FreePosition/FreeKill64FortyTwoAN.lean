import Erdos249257.DiagonalPincerCertificatesT64

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def fortyTwoANFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem fortyTwoANFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) :
    fortyTwoANFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [fortyTwoANFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [fortyTwoANFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then fortyTwoANFastPow a n * fortyTwoANFastPow a n * a
        else fortyTwoANFastPow a n * fortyTwoANFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_fortyTwoAN_2 : Nat.Prime 2 := by norm_num
private theorem prime_fortyTwoAN_3 : Nat.Prime 3 := by norm_num
private theorem prime_fortyTwoAN_5 : Nat.Prime 5 := by norm_num
private theorem prime_fortyTwoAN_7 : Nat.Prime 7 := by norm_num
private theorem prime_fortyTwoAN_11 : Nat.Prime 11 := by norm_num
private theorem prime_fortyTwoAN_13 : Nat.Prime 13 := by norm_num
private theorem prime_fortyTwoAN_17 : Nat.Prime 17 := by norm_num
private theorem prime_fortyTwoAN_19 : Nat.Prime 19 := by norm_num
private theorem prime_fortyTwoAN_23 : Nat.Prime 23 := by norm_num
private theorem prime_fortyTwoAN_29 : Nat.Prime 29 := by norm_num
private theorem prime_fortyTwoAN_31 : Nat.Prime 31 := by norm_num
private theorem prime_fortyTwoAN_37 : Nat.Prime 37 := by norm_num
private theorem prime_fortyTwoAN_41 : Nat.Prime 41 := by norm_num
private theorem prime_fortyTwoAN_43 : Nat.Prime 43 := by norm_num
private theorem prime_fortyTwoAN_47 : Nat.Prime 47 := by norm_num
private theorem prime_fortyTwoAN_53 : Nat.Prime 53 := by norm_num
private theorem prime_fortyTwoAN_59 : Nat.Prime 59 := by norm_num
private theorem prime_fortyTwoAN_61 : Nat.Prime 61 := by norm_num
private theorem prime_fortyTwoAN_67 : Nat.Prime 67 := by norm_num
private theorem prime_fortyTwoAN_71 : Nat.Prime 71 := by norm_num
private theorem prime_fortyTwoAN_73 : Nat.Prime 73 := by norm_num
private theorem prime_fortyTwoAN_79 : Nat.Prime 79 := by norm_num
private theorem prime_fortyTwoAN_83 : Nat.Prime 83 := by norm_num
private theorem prime_fortyTwoAN_89 : Nat.Prime 89 := by norm_num
private theorem prime_fortyTwoAN_97 : Nat.Prime 97 := by norm_num
private theorem prime_fortyTwoAN_101 : Nat.Prime 101 := by norm_num
private theorem prime_fortyTwoAN_103 : Nat.Prime 103 := by norm_num
private theorem prime_fortyTwoAN_107 : Nat.Prime 107 := by norm_num
private theorem prime_fortyTwoAN_109 : Nat.Prime 109 := by norm_num
private theorem prime_fortyTwoAN_113 : Nat.Prime 113 := by norm_num
private theorem prime_fortyTwoAN_127 : Nat.Prime 127 := by norm_num
private theorem prime_fortyTwoAN_131 : Nat.Prime 131 := by norm_num
private theorem prime_fortyTwoAN_137 : Nat.Prime 137 := by norm_num
private theorem prime_fortyTwoAN_139 : Nat.Prime 139 := by norm_num
private theorem prime_fortyTwoAN_149 : Nat.Prime 149 := by norm_num
private theorem prime_fortyTwoAN_151 : Nat.Prime 151 := by norm_num
private theorem prime_fortyTwoAN_157 : Nat.Prime 157 := by norm_num
private theorem prime_fortyTwoAN_163 : Nat.Prime 163 := by norm_num
private theorem prime_fortyTwoAN_167 : Nat.Prime 167 := by norm_num
private theorem prime_fortyTwoAN_173 : Nat.Prime 173 := by norm_num
private theorem prime_fortyTwoAN_179 : Nat.Prime 179 := by norm_num
private theorem prime_fortyTwoAN_181 : Nat.Prime 181 := by norm_num
private theorem prime_fortyTwoAN_191 : Nat.Prime 191 := by norm_num
private theorem prime_fortyTwoAN_193 : Nat.Prime 193 := by norm_num
private theorem prime_fortyTwoAN_197 : Nat.Prime 197 := by norm_num
private theorem prime_fortyTwoAN_199 : Nat.Prime 199 := by norm_num
private theorem prime_fortyTwoAN_211 : Nat.Prime 211 := by norm_num
private theorem prime_fortyTwoAN_223 : Nat.Prime 223 := by norm_num
private theorem prime_fortyTwoAN_227 : Nat.Prime 227 := by norm_num
private theorem prime_fortyTwoAN_229 : Nat.Prime 229 := by norm_num
private theorem prime_fortyTwoAN_233 : Nat.Prime 233 := by norm_num
private theorem prime_fortyTwoAN_239 : Nat.Prime 239 := by norm_num
private theorem prime_fortyTwoAN_251 : Nat.Prime 251 := by norm_num
private theorem prime_fortyTwoAN_257 : Nat.Prime 257 := by norm_num
private theorem prime_fortyTwoAN_263 : Nat.Prime 263 := by norm_num
private theorem prime_fortyTwoAN_269 : Nat.Prime 269 := by norm_num
private theorem prime_fortyTwoAN_281 : Nat.Prime 281 := by norm_num
private theorem prime_fortyTwoAN_283 : Nat.Prime 283 := by norm_num
private theorem prime_fortyTwoAN_293 : Nat.Prime 293 := by norm_num
private theorem prime_fortyTwoAN_307 : Nat.Prime 307 := by norm_num
private theorem prime_fortyTwoAN_317 : Nat.Prime 317 := by norm_num
private theorem prime_fortyTwoAN_331 : Nat.Prime 331 := by norm_num
private theorem prime_fortyTwoAN_349 : Nat.Prime 349 := by norm_num
private theorem prime_fortyTwoAN_353 : Nat.Prime 353 := by norm_num
private theorem prime_fortyTwoAN_359 : Nat.Prime 359 := by norm_num
private theorem prime_fortyTwoAN_379 : Nat.Prime 379 := by norm_num
private theorem prime_fortyTwoAN_383 : Nat.Prime 383 := by norm_num
private theorem prime_fortyTwoAN_389 : Nat.Prime 389 := by norm_num
private theorem prime_fortyTwoAN_397 : Nat.Prime 397 := by norm_num
private theorem prime_fortyTwoAN_409 : Nat.Prime 409 := by norm_num
private theorem prime_fortyTwoAN_419 : Nat.Prime 419 := by norm_num
private theorem prime_fortyTwoAN_421 : Nat.Prime 421 := by norm_num
private theorem prime_fortyTwoAN_431 : Nat.Prime 431 := by norm_num
private theorem prime_fortyTwoAN_439 : Nat.Prime 439 := by norm_num
private theorem prime_fortyTwoAN_449 : Nat.Prime 449 := by norm_num
private theorem prime_fortyTwoAN_457 : Nat.Prime 457 := by norm_num
private theorem prime_fortyTwoAN_461 : Nat.Prime 461 := by norm_num
private theorem prime_fortyTwoAN_467 : Nat.Prime 467 := by norm_num
private theorem prime_fortyTwoAN_479 : Nat.Prime 479 := by norm_num
private theorem prime_fortyTwoAN_487 : Nat.Prime 487 := by norm_num
private theorem prime_fortyTwoAN_491 : Nat.Prime 491 := by norm_num
private theorem prime_fortyTwoAN_499 : Nat.Prime 499 := by norm_num
private theorem prime_fortyTwoAN_547 : Nat.Prime 547 := by norm_num
private theorem prime_fortyTwoAN_557 : Nat.Prime 557 := by norm_num
private theorem prime_fortyTwoAN_563 : Nat.Prime 563 := by norm_num
private theorem prime_fortyTwoAN_593 : Nat.Prime 593 := by norm_num
private theorem prime_fortyTwoAN_599 : Nat.Prime 599 := by norm_num
private theorem prime_fortyTwoAN_601 : Nat.Prime 601 := by norm_num
private theorem prime_fortyTwoAN_613 : Nat.Prime 613 := by norm_num
private theorem prime_fortyTwoAN_641 : Nat.Prime 641 := by norm_num
private theorem prime_fortyTwoAN_643 : Nat.Prime 643 := by norm_num
private theorem prime_fortyTwoAN_677 : Nat.Prime 677 := by norm_num
private theorem prime_fortyTwoAN_683 : Nat.Prime 683 := by norm_num
private theorem prime_fortyTwoAN_701 : Nat.Prime 701 := by norm_num
private theorem prime_fortyTwoAN_709 : Nat.Prime 709 := by norm_num
private theorem prime_fortyTwoAN_719 : Nat.Prime 719 := by norm_num
private theorem prime_fortyTwoAN_727 : Nat.Prime 727 := by norm_num
private theorem prime_fortyTwoAN_739 : Nat.Prime 739 := by norm_num
private theorem prime_fortyTwoAN_769 : Nat.Prime 769 := by norm_num
private theorem prime_fortyTwoAN_773 : Nat.Prime 773 := by norm_num
private theorem prime_fortyTwoAN_787 : Nat.Prime 787 := by norm_num
private theorem prime_fortyTwoAN_811 : Nat.Prime 811 := by norm_num
private theorem prime_fortyTwoAN_823 : Nat.Prime 823 := by norm_num
private theorem prime_fortyTwoAN_853 : Nat.Prime 853 := by norm_num
private theorem prime_fortyTwoAN_929 : Nat.Prime 929 := by norm_num
private theorem prime_fortyTwoAN_953 : Nat.Prime 953 := by norm_num
private theorem prime_fortyTwoAN_971 : Nat.Prime 971 := by norm_num
private theorem prime_fortyTwoAN_991 : Nat.Prime 991 := by norm_num
private theorem prime_fortyTwoAN_1009 : Nat.Prime 1009 := by norm_num
private theorem prime_fortyTwoAN_1031 : Nat.Prime 1031 := by norm_num
private theorem prime_fortyTwoAN_1049 : Nat.Prime 1049 := by norm_num
private theorem prime_fortyTwoAN_1069 : Nat.Prime 1069 := by norm_num
private theorem prime_fortyTwoAN_1091 : Nat.Prime 1091 := by norm_num
private theorem prime_fortyTwoAN_1093 : Nat.Prime 1093 := by norm_num
private theorem prime_fortyTwoAN_1097 : Nat.Prime 1097 := by norm_num
private theorem prime_fortyTwoAN_1151 : Nat.Prime 1151 := by norm_num
private theorem prime_fortyTwoAN_1201 : Nat.Prime 1201 := by norm_num
private theorem prime_fortyTwoAN_1217 : Nat.Prime 1217 := by norm_num
private theorem prime_fortyTwoAN_1223 : Nat.Prime 1223 := by norm_num
private theorem prime_fortyTwoAN_1249 : Nat.Prime 1249 := by norm_num
private theorem prime_fortyTwoAN_1259 : Nat.Prime 1259 := by norm_num
private theorem prime_fortyTwoAN_1289 : Nat.Prime 1289 := by norm_num
private theorem prime_fortyTwoAN_1303 : Nat.Prime 1303 := by norm_num
private theorem prime_fortyTwoAN_1321 : Nat.Prime 1321 := by norm_num
private theorem prime_fortyTwoAN_1361 : Nat.Prime 1361 := by norm_num
private theorem prime_fortyTwoAN_1367 : Nat.Prime 1367 := by norm_num
private theorem prime_fortyTwoAN_1381 : Nat.Prime 1381 := by norm_num
private theorem prime_fortyTwoAN_1399 : Nat.Prime 1399 := by norm_num
private theorem prime_fortyTwoAN_1429 : Nat.Prime 1429 := by norm_num
private theorem prime_fortyTwoAN_1433 : Nat.Prime 1433 := by norm_num
private theorem prime_fortyTwoAN_1483 : Nat.Prime 1483 := by norm_num
private theorem prime_fortyTwoAN_1543 : Nat.Prime 1543 := by norm_num
private theorem prime_fortyTwoAN_1607 : Nat.Prime 1607 := by norm_num
private theorem prime_fortyTwoAN_1619 : Nat.Prime 1619 := by norm_num
private theorem prime_fortyTwoAN_1667 : Nat.Prime 1667 := by norm_num
private theorem prime_fortyTwoAN_1669 : Nat.Prime 1669 := by norm_num
private theorem prime_fortyTwoAN_1801 : Nat.Prime 1801 := by norm_num
private theorem prime_fortyTwoAN_1879 : Nat.Prime 1879 := by norm_num
private theorem prime_fortyTwoAN_1997 : Nat.Prime 1997 := by norm_num
private theorem prime_fortyTwoAN_1999 : Nat.Prime 1999 := by norm_num
private theorem prime_fortyTwoAN_2029 : Nat.Prime 2029 := by norm_num
private theorem prime_fortyTwoAN_2039 : Nat.Prime 2039 := by norm_num
private theorem prime_fortyTwoAN_2087 : Nat.Prime 2087 := by norm_num
private theorem prime_fortyTwoAN_2141 : Nat.Prime 2141 := by norm_num
private theorem prime_fortyTwoAN_2143 : Nat.Prime 2143 := by norm_num
private theorem prime_fortyTwoAN_2213 : Nat.Prime 2213 := by norm_num
private theorem prime_fortyTwoAN_2239 : Nat.Prime 2239 := by norm_num
private theorem prime_fortyTwoAN_2243 : Nat.Prime 2243 := by norm_num
private theorem prime_fortyTwoAN_2269 : Nat.Prime 2269 := by norm_num
private theorem prime_fortyTwoAN_2293 : Nat.Prime 2293 := by norm_num
private theorem prime_fortyTwoAN_2531 : Nat.Prime 2531 := by norm_num
private theorem prime_fortyTwoAN_2591 : Nat.Prime 2591 := by norm_num
private theorem prime_fortyTwoAN_2621 : Nat.Prime 2621 := by norm_num
private theorem prime_fortyTwoAN_2633 : Nat.Prime 2633 := by norm_num
private theorem prime_fortyTwoAN_2657 : Nat.Prime 2657 := by norm_num
private theorem prime_fortyTwoAN_2719 : Nat.Prime 2719 := by norm_num
private theorem prime_fortyTwoAN_2731 : Nat.Prime 2731 := by norm_num
private theorem prime_fortyTwoAN_2861 : Nat.Prime 2861 := by norm_num
private theorem prime_fortyTwoAN_2879 : Nat.Prime 2879 := by norm_num
private theorem prime_fortyTwoAN_2957 : Nat.Prime 2957 := by norm_num
private theorem prime_fortyTwoAN_3023 : Nat.Prime 3023 := by norm_num
private theorem prime_fortyTwoAN_3209 : Nat.Prime 3209 := by norm_num
private theorem prime_fortyTwoAN_3229 : Nat.Prime 3229 := by norm_num
private theorem prime_fortyTwoAN_3253 : Nat.Prime 3253 := by norm_num
private theorem prime_fortyTwoAN_3271 : Nat.Prime 3271 := by norm_num
private theorem prime_fortyTwoAN_3301 : Nat.Prime 3301 := by norm_num
private theorem prime_fortyTwoAN_3463 : Nat.Prime 3463 := by norm_num
private theorem prime_fortyTwoAN_3581 : Nat.Prime 3581 := by norm_num
private theorem prime_fortyTwoAN_3643 : Nat.Prime 3643 := by norm_num
private theorem prime_fortyTwoAN_3739 : Nat.Prime 3739 := by norm_num
private theorem prime_fortyTwoAN_3821 : Nat.Prime 3821 := by norm_num
private theorem prime_fortyTwoAN_4159 : Nat.Prime 4159 := by norm_num
private theorem prime_fortyTwoAN_4229 : Nat.Prime 4229 := by norm_num
private theorem prime_fortyTwoAN_4259 : Nat.Prime 4259 := by norm_num
private theorem prime_fortyTwoAN_4261 : Nat.Prime 4261 := by norm_num
private theorem prime_fortyTwoAN_4289 : Nat.Prime 4289 := by norm_num
private theorem prime_fortyTwoAN_4363 : Nat.Prime 4363 := by norm_num
private theorem prime_fortyTwoAN_4397 : Nat.Prime 4397 := by norm_num
private theorem prime_fortyTwoAN_4513 : Nat.Prime 4513 := by norm_num
private theorem prime_fortyTwoAN_4519 : Nat.Prime 4519 := by norm_num
private theorem prime_fortyTwoAN_4561 : Nat.Prime 4561 := by norm_num
private theorem prime_fortyTwoAN_4703 : Nat.Prime 4703 := by norm_num
private theorem prime_fortyTwoAN_5009 : Nat.Prime 5009 := by norm_num
private theorem prime_fortyTwoAN_5231 : Nat.Prime 5231 := by norm_num
private theorem prime_fortyTwoAN_5449 : Nat.Prime 5449 := by norm_num
private theorem prime_fortyTwoAN_5573 : Nat.Prime 5573 := by norm_num
private theorem prime_fortyTwoAN_5741 : Nat.Prime 5741 := by norm_num
private theorem prime_fortyTwoAN_5779 : Nat.Prime 5779 := by norm_num
private theorem prime_fortyTwoAN_5843 : Nat.Prime 5843 := by norm_num
private theorem prime_fortyTwoAN_5861 : Nat.Prime 5861 := by norm_num
private theorem prime_fortyTwoAN_5879 : Nat.Prime 5879 := by norm_num
private theorem prime_fortyTwoAN_5903 : Nat.Prime 5903 := by norm_num
private theorem prime_fortyTwoAN_6043 : Nat.Prime 6043 := by norm_num
private theorem prime_fortyTwoAN_6229 : Nat.Prime 6229 := by norm_num
private theorem prime_fortyTwoAN_6287 : Nat.Prime 6287 := by norm_num
private theorem prime_fortyTwoAN_6343 : Nat.Prime 6343 := by norm_num
private theorem prime_fortyTwoAN_6389 : Nat.Prime 6389 := by norm_num
private theorem prime_fortyTwoAN_6563 : Nat.Prime 6563 := by norm_num
private theorem prime_fortyTwoAN_6691 : Nat.Prime 6691 := by norm_num
private theorem prime_fortyTwoAN_6763 : Nat.Prime 6763 := by norm_num
private theorem prime_fortyTwoAN_7013 : Nat.Prime 7013 := by norm_num
private theorem prime_fortyTwoAN_7129 : Nat.Prime 7129 := by norm_num
private theorem prime_fortyTwoAN_7309 : Nat.Prime 7309 := by norm_num
private theorem prime_fortyTwoAN_7487 : Nat.Prime 7487 := by norm_num
private theorem prime_fortyTwoAN_7681 : Nat.Prime 7681 := by norm_num
private theorem prime_fortyTwoAN_7691 : Nat.Prime 7691 := by norm_num
private theorem prime_fortyTwoAN_7817 : Nat.Prime 7817 := by norm_num
private theorem prime_fortyTwoAN_7879 : Nat.Prime 7879 := by norm_num
private theorem prime_fortyTwoAN_8089 : Nat.Prime 8089 := by norm_num
private theorem prime_fortyTwoAN_8219 : Nat.Prime 8219 := by norm_num
private theorem prime_fortyTwoAN_8233 : Nat.Prime 8233 := by norm_num
private theorem prime_fortyTwoAN_8443 : Nat.Prime 8443 := by norm_num
private theorem prime_fortyTwoAN_8597 : Nat.Prime 8597 := by norm_num
private theorem prime_fortyTwoAN_8747 : Nat.Prime 8747 := by norm_num
private theorem prime_fortyTwoAN_8783 : Nat.Prime 8783 := by norm_num
private theorem prime_fortyTwoAN_9431 : Nat.Prime 9431 := by norm_num
private theorem prime_fortyTwoAN_9719 : Nat.Prime 9719 := by norm_num
private theorem prime_fortyTwoAN_9833 : Nat.Prime 9833 := by norm_num
private theorem prime_fortyTwoAN_10141 : Nat.Prime 10141 := by norm_num
private theorem prime_fortyTwoAN_10391 : Nat.Prime 10391 := by norm_num
private theorem prime_fortyTwoAN_11119 : Nat.Prime 11119 := by norm_num
private theorem prime_fortyTwoAN_11467 : Nat.Prime 11467 := by norm_num
private theorem prime_fortyTwoAN_12589 : Nat.Prime 12589 := by norm_num
private theorem prime_fortyTwoAN_12853 : Nat.Prime 12853 := by norm_num
private theorem prime_fortyTwoAN_13093 : Nat.Prime 13093 := by norm_num
private theorem prime_fortyTwoAN_13331 : Nat.Prime 13331 := by norm_num
private theorem prime_fortyTwoAN_13789 : Nat.Prime 13789 := by norm_num
private theorem prime_fortyTwoAN_13807 : Nat.Prime 13807 := by norm_num
private theorem prime_fortyTwoAN_15131 : Nat.Prime 15131 := by norm_num
private theorem prime_fortyTwoAN_15661 : Nat.Prime 15661 := by norm_num
private theorem prime_fortyTwoAN_16097 : Nat.Prime 16097 := by norm_num
private theorem prime_fortyTwoAN_16217 : Nat.Prime 16217 := by norm_num
private theorem prime_fortyTwoAN_16411 : Nat.Prime 16411 := by norm_num
private theorem prime_fortyTwoAN_16453 : Nat.Prime 16453 := by norm_num
private theorem prime_fortyTwoAN_17921 : Nat.Prime 17921 := by norm_num
private theorem prime_fortyTwoAN_18353 : Nat.Prime 18353 := by norm_num
private theorem prime_fortyTwoAN_19163 : Nat.Prime 19163 := by norm_num
private theorem prime_fortyTwoAN_19379 : Nat.Prime 19379 := by norm_num
private theorem prime_fortyTwoAN_19559 : Nat.Prime 19559 := by norm_num
private theorem prime_fortyTwoAN_20549 : Nat.Prime 20549 := by norm_num
private theorem prime_fortyTwoAN_22013 : Nat.Prime 22013 := by norm_num
private theorem prime_fortyTwoAN_22279 : Nat.Prime 22279 := by norm_num
private theorem prime_fortyTwoAN_22543 : Nat.Prime 22543 := by norm_num
private theorem prime_fortyTwoAN_23743 : Nat.Prime 23743 := by norm_num
private theorem prime_fortyTwoAN_24551 : Nat.Prime 24551 := by norm_num
private theorem prime_fortyTwoAN_25457 : Nat.Prime 25457 := by norm_num
private theorem prime_fortyTwoAN_25717 : Nat.Prime 25717 := by norm_num
private theorem prime_fortyTwoAN_26489 : Nat.Prime 26489 := by norm_num
private theorem prime_fortyTwoAN_26641 : Nat.Prime 26641 := by norm_num
private theorem prime_fortyTwoAN_28517 : Nat.Prime 28517 := by norm_num
private theorem prime_fortyTwoAN_28537 : Nat.Prime 28537 := by norm_num
private theorem prime_fortyTwoAN_32503 : Nat.Prime 32503 := by norm_num
private theorem prime_fortyTwoAN_33811 : Nat.Prime 33811 := by norm_num
private theorem prime_fortyTwoAN_35279 : Nat.Prime 35279 := by norm_num
private theorem prime_fortyTwoAN_35747 : Nat.Prime 35747 := by norm_num
private theorem prime_fortyTwoAN_37309 : Nat.Prime 37309 := by norm_num
private theorem prime_fortyTwoAN_37663 : Nat.Prime 37663 := by norm_num
private theorem prime_fortyTwoAN_39703 : Nat.Prime 39703 := by norm_num
private theorem prime_fortyTwoAN_42463 : Nat.Prime 42463 := by norm_num
private theorem prime_fortyTwoAN_43591 : Nat.Prime 43591 := by norm_num
private theorem prime_fortyTwoAN_45589 : Nat.Prime 45589 := by norm_num
private theorem prime_fortyTwoAN_47717 : Nat.Prime 47717 := by norm_num
private theorem prime_fortyTwoAN_52697 : Nat.Prime 52697 := by norm_num
private theorem prime_fortyTwoAN_54167 : Nat.Prime 54167 := by norm_num
private theorem prime_fortyTwoAN_55511 : Nat.Prime 55511 := by norm_num
private theorem prime_fortyTwoAN_61631 : Nat.Prime 61631 := by norm_num
private theorem prime_fortyTwoAN_61717 : Nat.Prime 61717 := by norm_num
private theorem prime_fortyTwoAN_65089 : Nat.Prime 65089 := by norm_num
private theorem prime_fortyTwoAN_72797 : Nat.Prime 72797 := by norm_num
private theorem prime_fortyTwoAN_72973 : Nat.Prime 72973 := by norm_num
private theorem prime_fortyTwoAN_73771 : Nat.Prime 73771 := by norm_num
private theorem prime_fortyTwoAN_80149 : Nat.Prime 80149 := by norm_num
private theorem prime_fortyTwoAN_81047 : Nat.Prime 81047 := by norm_num
private theorem prime_fortyTwoAN_81463 : Nat.Prime 81463 := by norm_num
private theorem prime_fortyTwoAN_89069 : Nat.Prime 89069 := by norm_num
private theorem prime_fortyTwoAN_90617 : Nat.Prime 90617 := by norm_num
private theorem prime_fortyTwoAN_93811 : Nat.Prime 93811 := by norm_num
private theorem prime_fortyTwoAN_97327 : Nat.Prime 97327 := by norm_num
private theorem prime_fortyTwoAN_107609 : Nat.Prime 107609 := by norm_num
private theorem prime_fortyTwoAN_111869 : Nat.Prime 111869 := by norm_num
private theorem prime_fortyTwoAN_112019 : Nat.Prime 112019 := by norm_num
private theorem prime_fortyTwoAN_112573 : Nat.Prime 112573 := by norm_num
private theorem prime_fortyTwoAN_114593 : Nat.Prime 114593 := by norm_num
private theorem prime_fortyTwoAN_115903 : Nat.Prime 115903 := by norm_num
private theorem prime_fortyTwoAN_117497 : Nat.Prime 117497 := by norm_num
private theorem prime_fortyTwoAN_117701 : Nat.Prime 117701 := by norm_num
private theorem prime_fortyTwoAN_125789 : Nat.Prime 125789 := by norm_num
private theorem prime_fortyTwoAN_127241 : Nat.Prime 127241 := by norm_num
private theorem prime_fortyTwoAN_127423 : Nat.Prime 127423 := by norm_num
private theorem prime_fortyTwoAN_127487 : Nat.Prime 127487 := by norm_num
private theorem prime_fortyTwoAN_139537 : Nat.Prime 139537 := by norm_num
private theorem prime_fortyTwoAN_139753 : Nat.Prime 139753 := by norm_num
private theorem prime_fortyTwoAN_148537 : Nat.Prime 148537 := by norm_num
private theorem prime_fortyTwoAN_151883 : Nat.Prime 151883 := by norm_num
private theorem prime_fortyTwoAN_151939 : Nat.Prime 151939 := by norm_num
private theorem prime_fortyTwoAN_156979 : Nat.Prime 156979 := by norm_num
private theorem prime_fortyTwoAN_161017 : Nat.Prime 161017 := by norm_num
private theorem prime_fortyTwoAN_163063 : Nat.Prime 163063 := by norm_num
private theorem prime_fortyTwoAN_168781 : Nat.Prime 168781 := by norm_num
private theorem prime_fortyTwoAN_176317 : Nat.Prime 176317 := by norm_num
private theorem prime_fortyTwoAN_187559 : Nat.Prime 187559 := by norm_num
private theorem prime_fortyTwoAN_189853 : Nat.Prime 189853 := by norm_num
private theorem prime_fortyTwoAN_190769 : Nat.Prime 190769 := by norm_num
private theorem prime_fortyTwoAN_192979 : Nat.Prime 192979 := by norm_num
private theorem prime_fortyTwoAN_195271 : Nat.Prime 195271 := by norm_num
private theorem prime_fortyTwoAN_201823 : Nat.Prime 201823 := by norm_num
private theorem prime_fortyTwoAN_208223 : Nat.Prime 208223 := by norm_num
private theorem prime_fortyTwoAN_210193 : Nat.Prime 210193 := by norm_num
private theorem prime_fortyTwoAN_215497 : Nat.Prime 215497 := by norm_num
private theorem prime_fortyTwoAN_217223 : Nat.Prime 217223 := by norm_num
private theorem prime_fortyTwoAN_218857 : Nat.Prime 218857 := by norm_num
private theorem prime_fortyTwoAN_230291 : Nat.Prime 230291 := by norm_num
private theorem prime_fortyTwoAN_232753 : Nat.Prime 232753 := by norm_num
private theorem prime_fortyTwoAN_242227 : Nat.Prime 242227 := by norm_num
private theorem prime_fortyTwoAN_251609 : Nat.Prime 251609 := by norm_num
private theorem prime_fortyTwoAN_262853 : Nat.Prime 262853 := by norm_num
private theorem prime_fortyTwoAN_275491 : Nat.Prime 275491 := by norm_num
private theorem prime_fortyTwoAN_293147 : Nat.Prime 293147 := by norm_num
private theorem prime_fortyTwoAN_311677 : Nat.Prime 311677 := by norm_num
private theorem prime_fortyTwoAN_318281 : Nat.Prime 318281 := by norm_num
private theorem prime_fortyTwoAN_325079 : Nat.Prime 325079 := by norm_num
private theorem prime_fortyTwoAN_331489 : Nat.Prime 331489 := by norm_num
private theorem prime_fortyTwoAN_344543 : Nat.Prime 344543 := by norm_num
private theorem prime_fortyTwoAN_363611 : Nat.Prime 363611 := by norm_num
private theorem prime_fortyTwoAN_367219 : Nat.Prime 367219 := by norm_num
private theorem prime_fortyTwoAN_382541 : Nat.Prime 382541 := by norm_num
private theorem prime_fortyTwoAN_391451 : Nat.Prime 391451 := by norm_num
private theorem prime_fortyTwoAN_393247 : Nat.Prime 393247 := by norm_num
private theorem prime_fortyTwoAN_413869 : Nat.Prime 413869 := by norm_num
private theorem prime_fortyTwoAN_425681 : Nat.Prime 425681 := by norm_num
private theorem prime_fortyTwoAN_436081 : Nat.Prime 436081 := by norm_num
private theorem prime_fortyTwoAN_439171 : Nat.Prime 439171 := by norm_num
private theorem prime_fortyTwoAN_457739 : Nat.Prime 457739 := by norm_num
private theorem prime_fortyTwoAN_505061 : Nat.Prime 505061 := by norm_num
private theorem prime_fortyTwoAN_507757 : Nat.Prime 507757 := by norm_num
private theorem prime_fortyTwoAN_512903 : Nat.Prime 512903 := by norm_num
private theorem prime_fortyTwoAN_517267 : Nat.Prime 517267 := by norm_num
private theorem prime_fortyTwoAN_555253 : Nat.Prime 555253 := by norm_num
private theorem prime_fortyTwoAN_692663 : Nat.Prime 692663 := by norm_num
private theorem prime_fortyTwoAN_758159 : Nat.Prime 758159 := by norm_num
private theorem prime_fortyTwoAN_784367 : Nat.Prime 784367 := by norm_num
private theorem prime_fortyTwoAN_888409 : Nat.Prime 888409 := by norm_num
private theorem prime_fortyTwoAN_924359 : Nat.Prime 924359 := by norm_num
private theorem prime_fortyTwoAN_951637 : Nat.Prime 951637 := by norm_num
private theorem prime_fortyTwoAN_959831 : Nat.Prime 959831 := by norm_num
private theorem prime_fortyTwoAN_1121831 : Nat.Prime 1121831 := by norm_num
private theorem prime_fortyTwoAN_1129501 : Nat.Prime 1129501 := by norm_num
private theorem prime_fortyTwoAN_1173959 : Nat.Prime 1173959 := by norm_num
private theorem prime_fortyTwoAN_1351547 : Nat.Prime 1351547 := by norm_num
private theorem prime_fortyTwoAN_1509031 : Nat.Prime 1509031 := by norm_num
private theorem prime_fortyTwoAN_1634609 : Nat.Prime 1634609 := by norm_num
private theorem prime_fortyTwoAN_1693169 : Nat.Prime 1693169 := by norm_num
private theorem prime_fortyTwoAN_1780577 : Nat.Prime 1780577 := by norm_num
private theorem prime_fortyTwoAN_1911977 : Nat.Prime 1911977 := by norm_num
private theorem prime_fortyTwoAN_1929523 : Nat.Prime 1929523 := by norm_num
private theorem prime_fortyTwoAN_1957301 : Nat.Prime 1957301 := by norm_num
private theorem prime_fortyTwoAN_2072201 : Nat.Prime 2072201 := by norm_num
private theorem prime_fortyTwoAN_2245339 : Nat.Prime 2245339 := by norm_num
private theorem prime_fortyTwoAN_2290081 : Nat.Prime 2290081 := by norm_num
private theorem prime_fortyTwoAN_2443997 : Nat.Prime 2443997 := by norm_num
private theorem prime_fortyTwoAN_2567179 : Nat.Prime 2567179 := by norm_num
private theorem prime_fortyTwoAN_2584511 : Nat.Prime 2584511 := by norm_num
private theorem prime_fortyTwoAN_2846287 : Nat.Prime 2846287 := by norm_num
private theorem prime_fortyTwoAN_2915719 : Nat.Prime 2915719 := by norm_num
private theorem prime_fortyTwoAN_2968373 : Nat.Prime 2968373 := by norm_num
private theorem prime_fortyTwoAN_2993957 : Nat.Prime 2993957 := by norm_num
private theorem prime_fortyTwoAN_2995609 : Nat.Prime 2995609 := by norm_num
private theorem prime_fortyTwoAN_3096739 : Nat.Prime 3096739 := by norm_num
private theorem prime_fortyTwoAN_3257707 : Nat.Prime 3257707 := by norm_num
private theorem prime_fortyTwoAN_3532679 : Nat.Prime 3532679 := by norm_num
private theorem prime_fortyTwoAN_3779417 : Nat.Prime 3779417 := by norm_num
private theorem prime_fortyTwoAN_3866927 : Nat.Prime 3866927 := by norm_num
private theorem prime_fortyTwoAN_4090649 : Nat.Prime 4090649 := by norm_num
private theorem prime_fortyTwoAN_4095737 : Nat.Prime 4095737 := by norm_num
private theorem prime_fortyTwoAN_4121269 : Nat.Prime 4121269 := by norm_num
private theorem prime_fortyTwoAN_4129087 : Nat.Prime 4129087 := by norm_num
private theorem prime_fortyTwoAN_4144969 : Nat.Prime 4144969 := by norm_num
private theorem prime_fortyTwoAN_4731367 : Nat.Prime 4731367 := by norm_num
private theorem prime_fortyTwoAN_5572883 : Nat.Prime 5572883 := by norm_num
private theorem prime_fortyTwoAN_5944361 : Nat.Prime 5944361 := by norm_num
private theorem prime_fortyTwoAN_5945839 : Nat.Prime 5945839 := by norm_num
private theorem prime_fortyTwoAN_6135331 : Nat.Prime 6135331 := by norm_num
private theorem prime_fortyTwoAN_6470753 : Nat.Prime 6470753 := by norm_num
private theorem prime_fortyTwoAN_6474341 : Nat.Prime 6474341 := by norm_num
private theorem prime_fortyTwoAN_6475879 : Nat.Prime 6475879 := by norm_num
private theorem prime_fortyTwoAN_6766183 : Nat.Prime 6766183 := by norm_num
private theorem prime_fortyTwoAN_7190123 : Nat.Prime 7190123 := by norm_num
private theorem prime_fortyTwoAN_7601051 : Nat.Prime 7601051 := by norm_num
private theorem prime_fortyTwoAN_7780667 : Nat.Prime 7780667 := by norm_num
private theorem prime_fortyTwoAN_7978459 : Nat.Prime 7978459 := by norm_num
private theorem prime_fortyTwoAN_8081267 : Nat.Prime 8081267 := by norm_num
private theorem prime_fortyTwoAN_8274073 : Nat.Prime 8274073 := by norm_num
private theorem prime_fortyTwoAN_9355447 : Nat.Prime 9355447 := by norm_num
private theorem prime_fortyTwoAN_9792301 : Nat.Prime 9792301 := by norm_num
private theorem prime_fortyTwoAN_10049639 : Nat.Prime 10049639 := by norm_num
private theorem prime_fortyTwoAN_10167809 : Nat.Prime 10167809 := by norm_num
private theorem prime_fortyTwoAN_10339193 : Nat.Prime 10339193 := by norm_num
private theorem prime_fortyTwoAN_10972711 : Nat.Prime 10972711 := by norm_num
private theorem prime_fortyTwoAN_12588833 : Nat.Prime 12588833 := by norm_num
private theorem prime_fortyTwoAN_14014339 : Nat.Prime 14014339 := by norm_num
private theorem prime_fortyTwoAN_14962183 : Nat.Prime 14962183 := by norm_num
private theorem prime_fortyTwoAN_14999741 : Nat.Prime 14999741 := by norm_num
private theorem prime_fortyTwoAN_15027377 : Nat.Prime 15027377 := by norm_num
private theorem prime_fortyTwoAN_15756119 : Nat.Prime 15756119 := by norm_num
private theorem prime_fortyTwoAN_16499213 : Nat.Prime 16499213 := by norm_num
private theorem prime_fortyTwoAN_16850357 : Nat.Prime 16850357 := by norm_num
private theorem prime_fortyTwoAN_17642671 : Nat.Prime 17642671 := by norm_num
private theorem prime_fortyTwoAN_17788357 : Nat.Prime 17788357 := by norm_num
private theorem prime_fortyTwoAN_18431951 : Nat.Prime 18431951 := by norm_num
private theorem prime_fortyTwoAN_19542287 : Nat.Prime 19542287 := by norm_num
private theorem prime_fortyTwoAN_20298013 : Nat.Prime 20298013 := by norm_num
private theorem prime_fortyTwoAN_20980153 : Nat.Prime 20980153 := by norm_num
private theorem prime_fortyTwoAN_22951043 : Nat.Prime 22951043 := by norm_num
private theorem prime_fortyTwoAN_27075547 : Nat.Prime 27075547 := by norm_num
private theorem prime_fortyTwoAN_27571249 : Nat.Prime 27571249 := by norm_num
private theorem prime_fortyTwoAN_27757949 : Nat.Prime 27757949 := by norm_num
private theorem prime_fortyTwoAN_28940609 : Nat.Prime 28940609 := by norm_num
private theorem prime_fortyTwoAN_29517919 : Nat.Prime 29517919 := by norm_num
private theorem prime_fortyTwoAN_29716873 : Nat.Prime 29716873 := by norm_num

private theorem prime_fortyTwoAN_31471001 : Nat.Prime 31471001 := by
  apply lucas_primality 31471001 (3 : ZMod 31471001)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 3), (11, 1), (2861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 3), (11, 1), (2861, 1)] : List FactorBlock).map factorBlockValue).prod) = 31471001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_5
      · exact prime_fortyTwoAN_11
      · exact prime_fortyTwoAN_2861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 31471001) ^ 15735500 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 31471001) ^ 6294200 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 31471001) ^ 2861000 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 31471001) ^ 11000 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_31913837 : Nat.Prime 31913837 := by
  apply lucas_primality 31913837 (2 : ZMod 31913837)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7978459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7978459, 1)] : List FactorBlock).map factorBlockValue).prod) = 31913837 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_7978459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 31913837) ^ 15956918 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 31913837) ^ 4 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_33352703 : Nat.Prime 33352703 := by
  apply lucas_primality 33352703 (5 : ZMod 33352703)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2029, 1), (8219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2029, 1), (8219, 1)] : List FactorBlock).map factorBlockValue).prod) = 33352703 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_2029
      · exact prime_fortyTwoAN_8219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 33352703) ^ 16676351 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 33352703) ^ 16438 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 33352703) ^ 4058 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_35444011 : Nat.Prime 35444011 := by
  apply lucas_primality 35444011 (3 : ZMod 35444011)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (168781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (168781, 1)] : List FactorBlock).map factorBlockValue).prod) = 35444011 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_5
      · exact prime_fortyTwoAN_7
      · exact prime_fortyTwoAN_168781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 35444011) ^ 17722005 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 35444011) ^ 11814670 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 35444011) ^ 7088802 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 35444011) ^ 5063430 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 35444011) ^ 210 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_36473579 : Nat.Prime 36473579 := by
  apply lucas_primality 36473579 (2 : ZMod 36473579)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (959831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (959831, 1)] : List FactorBlock).map factorBlockValue).prod) = 36473579 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_19
      · exact prime_fortyTwoAN_959831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 36473579) ^ 18236789 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 36473579) ^ 1919662 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 36473579) ^ 38 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_38363417 : Nat.Prime 38363417 := by
  apply lucas_primality 38363417 (3 : ZMod 38363417)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (13, 1), (52697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (13, 1), (52697, 1)] : List FactorBlock).map factorBlockValue).prod) = 38363417 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_7
      · exact prime_fortyTwoAN_13
      · exact prime_fortyTwoAN_52697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 38363417) ^ 19181708 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 38363417) ^ 5480488 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 38363417) ^ 2951032 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 38363417) ^ 728 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_40346827 : Nat.Prime 40346827 := by
  apply lucas_primality 40346827 (2 : ZMod 40346827)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (517267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (517267, 1)] : List FactorBlock).map factorBlockValue).prod) = 40346827 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_13
      · exact prime_fortyTwoAN_517267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 40346827) ^ 20173413 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 40346827) ^ 13448942 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 40346827) ^ 3103602 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 40346827) ^ 78 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_42857783 : Nat.Prime 42857783 := by
  apply lucas_primality 42857783 (5 : ZMod 42857783)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (17, 1), (114593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (17, 1), (114593, 1)] : List FactorBlock).map factorBlockValue).prod) = 42857783 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_11
      · exact prime_fortyTwoAN_17
      · exact prime_fortyTwoAN_114593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 42857783) ^ 21428891 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 42857783) ^ 3896162 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 42857783) ^ 2521046 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 42857783) ^ 374 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_44369233 : Nat.Prime 44369233 := by
  apply lucas_primality 44369233 (5 : ZMod 44369233)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (924359, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (924359, 1)] : List FactorBlock).map factorBlockValue).prod) = 44369233 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_924359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 44369233) ^ 22184616 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 44369233) ^ 14789744 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 44369233) ^ 48 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_45885799 : Nat.Prime 45885799 := by
  apply lucas_primality 45885799 (7 : ZMod 45885799)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 1), (19, 1), (6389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 1), (19, 1), (6389, 1)] : List FactorBlock).map factorBlockValue).prod) = 45885799 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_7
      · exact prime_fortyTwoAN_19
      · exact prime_fortyTwoAN_6389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 45885799) ^ 22942899 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (7 : ZMod 45885799) ^ 15295266 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (7 : ZMod 45885799) ^ 6555114 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (7 : ZMod 45885799) ^ 2415042 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (7 : ZMod 45885799) ^ 7182 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_47639987 : Nat.Prime 47639987 := by
  apply lucas_primality 47639987 (2 : ZMod 47639987)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (127, 1), (187559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (127, 1), (187559, 1)] : List FactorBlock).map factorBlockValue).prod) = 47639987 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_127
      · exact prime_fortyTwoAN_187559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 47639987) ^ 23819993 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 47639987) ^ 375118 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 47639987) ^ 254 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_54068233 : Nat.Prime 54068233 := by
  apply lucas_primality 54068233 (10 : ZMod 54068233)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (79, 1), (28517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (79, 1), (28517, 1)] : List FactorBlock).map factorBlockValue).prod) = 54068233 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_79
      · exact prime_fortyTwoAN_28517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 54068233) ^ 27034116 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (10 : ZMod 54068233) ^ 18022744 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (10 : ZMod 54068233) ^ 684408 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (10 : ZMod 54068233) ^ 1896 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_58756853 : Nat.Prime 58756853 := by
  apply lucas_primality 58756853 (2 : ZMod 58756853)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (11, 1), (190769, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (11, 1), (190769, 1)] : List FactorBlock).map factorBlockValue).prod) = 58756853 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_7
      · exact prime_fortyTwoAN_11
      · exact prime_fortyTwoAN_190769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 58756853) ^ 29378426 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 58756853) ^ 8393836 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 58756853) ^ 5341532 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 58756853) ^ 308 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_67197287 : Nat.Prime 67197287 := by
  apply lucas_primality 67197287 (5 : ZMod 67197287)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (2584511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (2584511, 1)] : List FactorBlock).map factorBlockValue).prod) = 67197287 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_13
      · exact prime_fortyTwoAN_2584511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 67197287) ^ 33598643 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 67197287) ^ 5169022 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 67197287) ^ 26 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_84294913 : Nat.Prime 84294913 := by
  apply lucas_primality 84294913 (14 : ZMod 84294913)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 1), (13, 1), (8443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 1), (13, 1), (8443, 1)] : List FactorBlock).map factorBlockValue).prod) = 84294913 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_13
      · exact prime_fortyTwoAN_8443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 84294913) ^ 42147456 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (14 : ZMod 84294913) ^ 28098304 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (14 : ZMod 84294913) ^ 6484224 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (14 : ZMod 84294913) ^ 9984 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_89401187 : Nat.Prime 89401187 := by
  apply lucas_primality 89401187 (2 : ZMod 89401187)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (139, 1), (6563, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (139, 1), (6563, 1)] : List FactorBlock).map factorBlockValue).prod) = 89401187 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_7
      · exact prime_fortyTwoAN_139
      · exact prime_fortyTwoAN_6563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 89401187) ^ 44700593 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 89401187) ^ 12771598 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 89401187) ^ 643174 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 89401187) ^ 13622 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_100015189 : Nat.Prime 100015189 := by
  apply lucas_primality 100015189 (10 : ZMod 100015189)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (13, 1), (67, 1), (1367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (13, 1), (67, 1), (1367, 1)] : List FactorBlock).map factorBlockValue).prod) = 100015189 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_7
      · exact prime_fortyTwoAN_13
      · exact prime_fortyTwoAN_67
      · exact prime_fortyTwoAN_1367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 100015189) ^ 50007594 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (10 : ZMod 100015189) ^ 33338396 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (10 : ZMod 100015189) ^ 14287884 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (10 : ZMod 100015189) ^ 7693476 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (10 : ZMod 100015189) ^ 1492764 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (10 : ZMod 100015189) ^ 73164 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_100315387 : Nat.Prime 100315387 := by
  apply lucas_primality 100315387 (2 : ZMod 100315387)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (227, 1), (24551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (227, 1), (24551, 1)] : List FactorBlock).map factorBlockValue).prod) = 100315387 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_227
      · exact prime_fortyTwoAN_24551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 100315387) ^ 50157693 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 100315387) ^ 33438462 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 100315387) ^ 441918 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 100315387) ^ 4086 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_119628851 : Nat.Prime 119628851 := by
  apply lucas_primality 119628851 (6 : ZMod 119628851)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (11, 1), (199, 1), (1093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (11, 1), (199, 1), (1093, 1)] : List FactorBlock).map factorBlockValue).prod) = 119628851 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_5
      · exact prime_fortyTwoAN_11
      · exact prime_fortyTwoAN_199
      · exact prime_fortyTwoAN_1093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 119628851) ^ 59814425 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (6 : ZMod 119628851) ^ 23925770 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (6 : ZMod 119628851) ^ 10875350 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (6 : ZMod 119628851) ^ 601150 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (6 : ZMod 119628851) ^ 109450 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_120219017 : Nat.Prime 120219017 := by
  apply lucas_primality 120219017 (3 : ZMod 120219017)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (15027377, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (15027377, 1)] : List FactorBlock).map factorBlockValue).prod) = 120219017 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_15027377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 120219017) ^ 60109508 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 120219017) ^ 8 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_123638071 : Nat.Prime 123638071 := by
  apply lucas_primality 123638071 (7 : ZMod 123638071)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (4121269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (4121269, 1)] : List FactorBlock).map factorBlockValue).prod) = 123638071 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_5
      · exact prime_fortyTwoAN_4121269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 123638071) ^ 61819035 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (7 : ZMod 123638071) ^ 41212690 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (7 : ZMod 123638071) ^ 24727614 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (7 : ZMod 123638071) ^ 30 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_126190483 : Nat.Prime 126190483 := by
  apply lucas_primality 126190483 (2 : ZMod 126190483)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (1911977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (1911977, 1)] : List FactorBlock).map factorBlockValue).prod) = 126190483 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_11
      · exact prime_fortyTwoAN_1911977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 126190483) ^ 63095241 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 126190483) ^ 42063494 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 126190483) ^ 11471862 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 126190483) ^ 66 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_142700137 : Nat.Prime 142700137 := by
  apply lucas_primality 142700137 (7 : ZMod 142700137)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5945839, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5945839, 1)] : List FactorBlock).map factorBlockValue).prod) = 142700137 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_5945839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 142700137) ^ 71350068 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (7 : ZMod 142700137) ^ 47566712 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (7 : ZMod 142700137) ^ 24 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_143078893 : Nat.Prime 143078893 := by
  apply lucas_primality 143078893 (5 : ZMod 143078893)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (19, 1), (89, 1), (641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (19, 1), (89, 1), (641, 1)] : List FactorBlock).map factorBlockValue).prod) = 143078893 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_11
      · exact prime_fortyTwoAN_19
      · exact prime_fortyTwoAN_89
      · exact prime_fortyTwoAN_641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 143078893) ^ 71539446 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 143078893) ^ 47692964 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 143078893) ^ 13007172 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 143078893) ^ 7530468 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 143078893) ^ 1607628 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 143078893) ^ 223212 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_156859133 : Nat.Prime 156859133 := by
  apply lucas_primality 156859133 (2 : ZMod 156859133)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (31, 1), (37, 1), (179, 1), (191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (31, 1), (37, 1), (179, 1), (191, 1)] : List FactorBlock).map factorBlockValue).prod) = 156859133 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_31
      · exact prime_fortyTwoAN_37
      · exact prime_fortyTwoAN_179
      · exact prime_fortyTwoAN_191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 156859133) ^ 78429566 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 156859133) ^ 5059972 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 156859133) ^ 4239436 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 156859133) ^ 876308 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 156859133) ^ 821252 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_160338799 : Nat.Prime 160338799 := by
  apply lucas_primality 160338799 (3 : ZMod 160338799)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (17, 1), (389, 1), (449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (17, 1), (389, 1), (449, 1)] : List FactorBlock).map factorBlockValue).prod) = 160338799 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_17
      · exact prime_fortyTwoAN_389
      · exact prime_fortyTwoAN_449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 160338799) ^ 80169399 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 160338799) ^ 53446266 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 160338799) ^ 9431694 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 160338799) ^ 412182 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 160338799) ^ 357102 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_161521313 : Nat.Prime 161521313 := by
  apply lucas_primality 161521313 (3 : ZMod 161521313)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (1321, 1), (3821, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (1321, 1), (3821, 1)] : List FactorBlock).map factorBlockValue).prod) = 161521313 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_1321
      · exact prime_fortyTwoAN_3821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 161521313) ^ 80760656 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 161521313) ^ 122272 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 161521313) ^ 42272 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_169985287 : Nat.Prime 169985287 := by
  apply lucas_primality 169985287 (3 : ZMod 169985287)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (19, 1), (307, 1), (1619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (19, 1), (307, 1), (1619, 1)] : List FactorBlock).map factorBlockValue).prod) = 169985287 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_19
      · exact prime_fortyTwoAN_307
      · exact prime_fortyTwoAN_1619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 169985287) ^ 84992643 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 169985287) ^ 56661762 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 169985287) ^ 8946594 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 169985287) ^ 553698 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 169985287) ^ 104994 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_175593973 : Nat.Prime 175593973 := by
  apply lucas_primality 175593973 (5 : ZMod 175593973)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (131, 1), (5879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (131, 1), (5879, 1)] : List FactorBlock).map factorBlockValue).prod) = 175593973 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_19
      · exact prime_fortyTwoAN_131
      · exact prime_fortyTwoAN_5879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 175593973) ^ 87796986 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 175593973) ^ 58531324 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 175593973) ^ 9241788 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 175593973) ^ 1340412 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 175593973) ^ 29868 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_187828033 : Nat.Prime 187828033 := by
  apply lucas_primality 187828033 (11 : ZMod 187828033)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (7, 1), (139753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (7, 1), (139753, 1)] : List FactorBlock).map factorBlockValue).prod) = 187828033 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_7
      · exact prime_fortyTwoAN_139753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 187828033) ^ 93914016 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (11 : ZMod 187828033) ^ 62609344 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (11 : ZMod 187828033) ^ 26832576 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (11 : ZMod 187828033) ^ 1344 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_189443929 : Nat.Prime 189443929 := by
  apply lucas_primality 189443929 (7 : ZMod 189443929)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (107, 1), (73771, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (107, 1), (73771, 1)] : List FactorBlock).map factorBlockValue).prod) = 189443929 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_107
      · exact prime_fortyTwoAN_73771
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 189443929) ^ 94721964 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (7 : ZMod 189443929) ^ 63147976 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (7 : ZMod 189443929) ^ 1770504 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (7 : ZMod 189443929) ^ 2568 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_209801531 : Nat.Prime 209801531 := by
  apply lucas_primality 209801531 (6 : ZMod 209801531)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (20980153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (20980153, 1)] : List FactorBlock).map factorBlockValue).prod) = 209801531 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_5
      · exact prime_fortyTwoAN_20980153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 209801531) ^ 104900765 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (6 : ZMod 209801531) ^ 41960306 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (6 : ZMod 209801531) ^ 10 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_213426679 : Nat.Prime 213426679 := by
  apply lucas_primality 213426679 (3 : ZMod 213426679)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (61, 1), (257, 1), (2269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (61, 1), (257, 1), (2269, 1)] : List FactorBlock).map factorBlockValue).prod) = 213426679 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_61
      · exact prime_fortyTwoAN_257
      · exact prime_fortyTwoAN_2269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 213426679) ^ 106713339 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 213426679) ^ 71142226 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 213426679) ^ 3498798 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 213426679) ^ 830454 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 213426679) ^ 94062 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_216317813 : Nat.Prime 216317813 := by
  apply lucas_primality 216317813 (2 : ZMod 216317813)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (2846287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (2846287, 1)] : List FactorBlock).map factorBlockValue).prod) = 216317813 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_19
      · exact prime_fortyTwoAN_2846287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 216317813) ^ 108158906 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 216317813) ^ 11385148 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 216317813) ^ 76 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_237308333 : Nat.Prime 237308333 := by
  apply lucas_primality 237308333 (2 : ZMod 237308333)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (191, 1), (383, 1), (811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (191, 1), (383, 1), (811, 1)] : List FactorBlock).map factorBlockValue).prod) = 237308333 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_191
      · exact prime_fortyTwoAN_383
      · exact prime_fortyTwoAN_811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 237308333) ^ 118654166 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 237308333) ^ 1242452 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 237308333) ^ 619604 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 237308333) ^ 292612 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_266215399 : Nat.Prime 266215399 := by
  apply lucas_primality 266215399 (3 : ZMod 266215399)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (44369233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (44369233, 1)] : List FactorBlock).map factorBlockValue).prod) = 266215399 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_44369233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 266215399) ^ 133107699 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 266215399) ^ 88738466 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 266215399) ^ 6 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_275558879 : Nat.Prime 275558879 := by
  apply lucas_primality 275558879 (7 : ZMod 275558879)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (43, 1), (457739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (43, 1), (457739, 1)] : List FactorBlock).map factorBlockValue).prod) = 275558879 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_7
      · exact prime_fortyTwoAN_43
      · exact prime_fortyTwoAN_457739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 275558879) ^ 137779439 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (7 : ZMod 275558879) ^ 39365554 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (7 : ZMod 275558879) ^ 6408346 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (7 : ZMod 275558879) ^ 602 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_286464551 : Nat.Prime 286464551 := by
  apply lucas_primality 286464551 (7 : ZMod 286464551)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (1303, 1), (4397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (1303, 1), (4397, 1)] : List FactorBlock).map factorBlockValue).prod) = 286464551 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_5
      · exact prime_fortyTwoAN_1303
      · exact prime_fortyTwoAN_4397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 286464551) ^ 143232275 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (7 : ZMod 286464551) ^ 57292910 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (7 : ZMod 286464551) ^ 219850 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (7 : ZMod 286464551) ^ 65150 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_288670153 : Nat.Prime 288670153 := by
  apply lucas_primality 288670153 (5 : ZMod 288670153)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (37, 1), (325079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (37, 1), (325079, 1)] : List FactorBlock).map factorBlockValue).prod) = 288670153 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_37
      · exact prime_fortyTwoAN_325079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 288670153) ^ 144335076 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 288670153) ^ 96223384 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 288670153) ^ 7801896 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 288670153) ^ 888 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_372958561 : Nat.Prime 372958561 := by
  apply lucas_primality 372958561 (11 : ZMod 372958561)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 3), (5, 1), (13, 1), (29, 1), (229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 3), (5, 1), (13, 1), (29, 1), (229, 1)] : List FactorBlock).map factorBlockValue).prod) = 372958561 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_5
      · exact prime_fortyTwoAN_13
      · exact prime_fortyTwoAN_29
      · exact prime_fortyTwoAN_229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 372958561) ^ 186479280 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (11 : ZMod 372958561) ^ 124319520 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (11 : ZMod 372958561) ^ 74591712 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (11 : ZMod 372958561) ^ 28689120 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (11 : ZMod 372958561) ^ 12860640 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (11 : ZMod 372958561) ^ 1628640 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_550990241 : Nat.Prime 550990241 := by
  apply lucas_primality 550990241 (3 : ZMod 550990241)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (79, 1), (43591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (79, 1), (43591, 1)] : List FactorBlock).map factorBlockValue).prod) = 550990241 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_5
      · exact prime_fortyTwoAN_79
      · exact prime_fortyTwoAN_43591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 550990241) ^ 275495120 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 550990241) ^ 110198048 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 550990241) ^ 6974560 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 550990241) ^ 12640 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_680104267 : Nat.Prime 680104267 := by
  apply lucas_primality 680104267 (13 : ZMod 680104267)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (487, 1), (232753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (487, 1), (232753, 1)] : List FactorBlock).map factorBlockValue).prod) = 680104267 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_487
      · exact prime_fortyTwoAN_232753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 680104267) ^ 340052133 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (13 : ZMod 680104267) ^ 226701422 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (13 : ZMod 680104267) ^ 1396518 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (13 : ZMod 680104267) ^ 2922 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_712658239 : Nat.Prime 712658239 := by
  apply lucas_primality 712658239 (19 : ZMod 712658239)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 1), (4095737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 1), (4095737, 1)] : List FactorBlock).map factorBlockValue).prod) = 712658239 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_29
      · exact prime_fortyTwoAN_4095737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 712658239) ^ 356329119 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (19 : ZMod 712658239) ^ 237552746 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (19 : ZMod 712658239) ^ 24574422 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (19 : ZMod 712658239) ^ 174 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_734686247 : Nat.Prime 734686247 := by
  apply lucas_primality 734686247 (5 : ZMod 734686247)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (17, 1), (491, 1), (6287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (17, 1), (491, 1), (6287, 1)] : List FactorBlock).map factorBlockValue).prod) = 734686247 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_7
      · exact prime_fortyTwoAN_17
      · exact prime_fortyTwoAN_491
      · exact prime_fortyTwoAN_6287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 734686247) ^ 367343123 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 734686247) ^ 104955178 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 734686247) ^ 43216838 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 734686247) ^ 1496306 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 734686247) ^ 116858 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_741828427 : Nat.Prime 741828427 := by
  apply lucas_primality 741828427 (2 : ZMod 741828427)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (123638071, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (123638071, 1)] : List FactorBlock).map factorBlockValue).prod) = 741828427 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_123638071
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 741828427) ^ 370914213 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 741828427) ^ 247276142 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 741828427) ^ 6 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_883650809 : Nat.Prime 883650809 := by
  apply lucas_primality 883650809 (3 : ZMod 883650809)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (439, 1), (251609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (439, 1), (251609, 1)] : List FactorBlock).map factorBlockValue).prod) = 883650809 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_439
      · exact prime_fortyTwoAN_251609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 883650809) ^ 441825404 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 883650809) ^ 2012872 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 883650809) ^ 3512 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_910838081 : Nat.Prime 910838081 := by
  apply lucas_primality 910838081 (3 : ZMod 910838081)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (5, 1), (173, 1), (16453, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (5, 1), (173, 1), (16453, 1)] : List FactorBlock).map factorBlockValue).prod) = 910838081 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_5
      · exact prime_fortyTwoAN_173
      · exact prime_fortyTwoAN_16453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 910838081) ^ 455419040 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 910838081) ^ 182167616 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 910838081) ^ 5264960 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 910838081) ^ 55360 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_956242277 : Nat.Prime 956242277 := by
  apply lucas_primality 956242277 (2 : ZMod 956242277)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (173, 1), (269, 1), (467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (173, 1), (269, 1), (467, 1)] : List FactorBlock).map factorBlockValue).prod) = 956242277 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_11
      · exact prime_fortyTwoAN_173
      · exact prime_fortyTwoAN_269
      · exact prime_fortyTwoAN_467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 956242277) ^ 478121138 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 956242277) ^ 86931116 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 956242277) ^ 5527412 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 956242277) ^ 3554804 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 956242277) ^ 2047628 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_1088310731 : Nat.Prime 1088310731 := by
  apply lucas_primality 1088310731 (7 : ZMod 1088310731)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (2239, 1), (3739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (2239, 1), (3739, 1)] : List FactorBlock).map factorBlockValue).prod) = 1088310731 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_5
      · exact prime_fortyTwoAN_13
      · exact prime_fortyTwoAN_2239
      · exact prime_fortyTwoAN_3739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1088310731) ^ 544155365 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (7 : ZMod 1088310731) ^ 217662146 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (7 : ZMod 1088310731) ^ 83716210 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (7 : ZMod 1088310731) ^ 486070 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (7 : ZMod 1088310731) ^ 291070 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_1222615931 : Nat.Prime 1222615931 := by
  apply lucas_primality 1222615931 (2 : ZMod 1222615931)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (29, 1), (113, 1), (37309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (29, 1), (113, 1), (37309, 1)] : List FactorBlock).map factorBlockValue).prod) = 1222615931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_5
      · exact prime_fortyTwoAN_29
      · exact prime_fortyTwoAN_113
      · exact prime_fortyTwoAN_37309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1222615931) ^ 611307965 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 244523186 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 42159170 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 10819610 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 32770 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_1366656409 : Nat.Prime 1366656409 := by
  apply lucas_primality 1366656409 (7 : ZMod 1366656409)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (13, 1), (179, 1), (2719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (13, 1), (179, 1), (2719, 1)] : List FactorBlock).map factorBlockValue).prod) = 1366656409 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_13
      · exact prime_fortyTwoAN_179
      · exact prime_fortyTwoAN_2719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1366656409) ^ 683328204 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (7 : ZMod 1366656409) ^ 455552136 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (7 : ZMod 1366656409) ^ 105127416 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (7 : ZMod 1366656409) ^ 7634952 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (7 : ZMod 1366656409) ^ 502632 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_1422302993 : Nat.Prime 1422302993 := by
  apply lucas_primality 1422302993 (3 : ZMod 1422302993)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (11, 1), (8081267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (11, 1), (8081267, 1)] : List FactorBlock).map factorBlockValue).prod) = 1422302993 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_11
      · exact prime_fortyTwoAN_8081267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1422302993) ^ 711151496 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 1422302993) ^ 129300272 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 1422302993) ^ 176 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_1590164911 : Nat.Prime 1590164911 := by
  apply lucas_primality 1590164911 (3 : ZMod 1590164911)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (19, 1), (37, 1), (41, 1), (613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (19, 1), (37, 1), (41, 1), (613, 1)] : List FactorBlock).map factorBlockValue).prod) = 1590164911 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_5
      · exact prime_fortyTwoAN_19
      · exact prime_fortyTwoAN_37
      · exact prime_fortyTwoAN_41
      · exact prime_fortyTwoAN_613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1590164911) ^ 795082455 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 1590164911) ^ 530054970 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 1590164911) ^ 318032982 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 1590164911) ^ 83692890 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 1590164911) ^ 42977430 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 1590164911) ^ 38784510 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 1590164911) ^ 2594070 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_1849892749 : Nat.Prime 1849892749 := by
  apply lucas_primality 1849892749 (2 : ZMod 1849892749)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (14014339, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (14014339, 1)] : List FactorBlock).map factorBlockValue).prod) = 1849892749 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_11
      · exact prime_fortyTwoAN_14014339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1849892749) ^ 924946374 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 1849892749) ^ 616630916 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 1849892749) ^ 168172068 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 1849892749) ^ 132 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_2261361899 : Nat.Prime 2261361899 := by
  apply lucas_primality 2261361899 (2 : ZMod 2261361899)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (36473579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (36473579, 1)] : List FactorBlock).map factorBlockValue).prod) = 2261361899 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_31
      · exact prime_fortyTwoAN_36473579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2261361899) ^ 1130680949 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 2261361899) ^ 72947158 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 2261361899) ^ 62 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_3139143389 : Nat.Prime 3139143389 := by
  apply lucas_primality 3139143389 (2 : ZMod 3139143389)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (359, 1), (677, 1), (3229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (359, 1), (677, 1), (3229, 1)] : List FactorBlock).map factorBlockValue).prod) = 3139143389 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_359
      · exact prime_fortyTwoAN_677
      · exact prime_fortyTwoAN_3229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3139143389) ^ 1569571694 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 3139143389) ^ 8744132 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 3139143389) ^ 4636844 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 3139143389) ^ 972172 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_3540386347 : Nat.Prime 3540386347 := by
  apply lucas_primality 3540386347 (11 : ZMod 3540386347)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (84294913, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (84294913, 1)] : List FactorBlock).map factorBlockValue).prod) = 3540386347 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_7
      · exact prime_fortyTwoAN_84294913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 3540386347) ^ 1770193173 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (11 : ZMod 3540386347) ^ 1180128782 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (11 : ZMod 3540386347) ^ 505769478 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (11 : ZMod 3540386347) ^ 42 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_5264385367 : Nat.Prime 5264385367 := by
  apply lucas_primality 5264385367 (3 : ZMod 5264385367)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (5861, 1), (7879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (5861, 1), (7879, 1)] : List FactorBlock).map factorBlockValue).prod) = 5264385367 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_19
      · exact prime_fortyTwoAN_5861
      · exact prime_fortyTwoAN_7879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 5264385367) ^ 2632192683 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 5264385367) ^ 1754795122 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 5264385367) ^ 277072914 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 5264385367) ^ 898206 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 5264385367) ^ 668154 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_5796774251 : Nat.Prime 5796774251 := by
  apply lucas_primality 5796774251 (2 : ZMod 5796774251)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 3), (197, 1), (117701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 3), (197, 1), (117701, 1)] : List FactorBlock).map factorBlockValue).prod) = 5796774251 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_5
      · exact prime_fortyTwoAN_197
      · exact prime_fortyTwoAN_117701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5796774251) ^ 2898387125 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 5796774251) ^ 1159354850 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 5796774251) ^ 29425250 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 5796774251) ^ 49250 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_5916548189 : Nat.Prime 5916548189 := by
  apply lucas_primality 5916548189 (2 : ZMod 5916548189)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (47, 1), (31471001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (47, 1), (31471001, 1)] : List FactorBlock).map factorBlockValue).prod) = 5916548189 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_47
      · exact prime_fortyTwoAN_31471001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 5916548189) ^ 2958274094 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 5916548189) ^ 125884004 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 5916548189) ^ 188 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_6391408799 : Nat.Prime 6391408799 := by
  apply lucas_primality 6391408799 (23 : ZMod 6391408799)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (89, 1), (223, 1), (161017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (89, 1), (223, 1), (161017, 1)] : List FactorBlock).map factorBlockValue).prod) = 6391408799 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_89
      · exact prime_fortyTwoAN_223
      · exact prime_fortyTwoAN_161017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (23 : ZMod 6391408799) ^ 3195704399 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (23 : ZMod 6391408799) ^ 71813582 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (23 : ZMod 6391408799) ^ 28661026 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (23 : ZMod 6391408799) ^ 39694 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_6805676209 : Nat.Prime 6805676209 := by
  apply lucas_primality 6805676209 (7 : ZMod 6805676209)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (89, 1), (353, 1), (4513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (89, 1), (353, 1), (4513, 1)] : List FactorBlock).map factorBlockValue).prod) = 6805676209 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_89
      · exact prime_fortyTwoAN_353
      · exact prime_fortyTwoAN_4513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 6805676209) ^ 3402838104 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (7 : ZMod 6805676209) ^ 2268558736 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (7 : ZMod 6805676209) ^ 76468272 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (7 : ZMod 6805676209) ^ 19279536 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (7 : ZMod 6805676209) ^ 1508016 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_7097035321 : Nat.Prime 7097035321 := by
  apply lucas_primality 7097035321 (7 : ZMod 7097035321)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 4), (5, 1), (197, 1), (11119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 4), (5, 1), (197, 1), (11119, 1)] : List FactorBlock).map factorBlockValue).prod) = 7097035321 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_5
      · exact prime_fortyTwoAN_197
      · exact prime_fortyTwoAN_11119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 7097035321) ^ 3548517660 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (7 : ZMod 7097035321) ^ 2365678440 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (7 : ZMod 7097035321) ^ 1419407064 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (7 : ZMod 7097035321) ^ 36025560 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (7 : ZMod 7097035321) ^ 638280 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_7652554093 : Nat.Prime 7652554093 := by
  apply lucas_primality 7652554093 (5 : ZMod 7652554093)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (71, 1), (2993957, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (71, 1), (2993957, 1)] : List FactorBlock).map factorBlockValue).prod) = 7652554093 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_71
      · exact prime_fortyTwoAN_2993957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 7652554093) ^ 3826277046 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 7652554093) ^ 2550851364 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 7652554093) ^ 107782452 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 7652554093) ^ 2556 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_7706514863 : Nat.Prime 7706514863 := by
  apply lucas_primality 7706514863 (5 : ZMod 7706514863)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1997, 1), (1929523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1997, 1), (1929523, 1)] : List FactorBlock).map factorBlockValue).prod) = 7706514863 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_1997
      · exact prime_fortyTwoAN_1929523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 7706514863) ^ 3853257431 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 7706514863) ^ 3859046 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 7706514863) ^ 3994 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_8696692033 : Nat.Prime 8696692033 := by
  apply lucas_primality 8696692033 (17 : ZMod 8696692033)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (7, 1), (6470753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (7, 1), (6470753, 1)] : List FactorBlock).map factorBlockValue).prod) = 8696692033 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_7
      · exact prime_fortyTwoAN_6470753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 8696692033) ^ 4348346016 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (17 : ZMod 8696692033) ^ 2898897344 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (17 : ZMod 8696692033) ^ 1242384576 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (17 : ZMod 8696692033) ^ 1344 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_8729662687 : Nat.Prime 8729662687 := by
  apply lucas_primality 8729662687 (3 : ZMod 8729662687)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (499, 1), (2915719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (499, 1), (2915719, 1)] : List FactorBlock).map factorBlockValue).prod) = 8729662687 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_499
      · exact prime_fortyTwoAN_2915719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 8729662687) ^ 4364831343 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 8729662687) ^ 2909887562 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 8729662687) ^ 17494314 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 8729662687) ^ 2994 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_8977309801 : Nat.Prime 8977309801 := by
  apply lucas_primality 8977309801 (19 : ZMod 8977309801)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 2), (14962183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 2), (14962183, 1)] : List FactorBlock).map factorBlockValue).prod) = 8977309801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_5
      · exact prime_fortyTwoAN_14962183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 8977309801) ^ 4488654900 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (19 : ZMod 8977309801) ^ 2992436600 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (19 : ZMod 8977309801) ^ 1795461960 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (19 : ZMod 8977309801) ^ 600 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_9277522589 : Nat.Prime 9277522589 := by
  apply lucas_primality 9277522589 (2 : ZMod 9277522589)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 1), (53, 1), (1509031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 1), (53, 1), (1509031, 1)] : List FactorBlock).map factorBlockValue).prod) = 9277522589 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_29
      · exact prime_fortyTwoAN_53
      · exact prime_fortyTwoAN_1509031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 9277522589) ^ 4638761294 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 9277522589) ^ 319914572 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 9277522589) ^ 175047596 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 9277522589) ^ 6148 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_14577836023 : Nat.Prime 14577836023 := by
  apply lucas_primality 14577836023 (5 : ZMod 14577836023)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (17, 1), (47639987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (17, 1), (47639987, 1)] : List FactorBlock).map factorBlockValue).prod) = 14577836023 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_17
      · exact prime_fortyTwoAN_47639987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 14577836023) ^ 7288918011 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 14577836023) ^ 4859278674 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 14577836023) ^ 857519766 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 14577836023) ^ 306 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_14853048211 : Nat.Prime 14853048211 := by
  apply lucas_primality 14853048211 (2 : ZMod 14853048211)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 1), (11, 1), (13, 1), (173, 1), (953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 1), (11, 1), (13, 1), (173, 1), (953, 1)] : List FactorBlock).map factorBlockValue).prod) = 14853048211 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_5
      · exact prime_fortyTwoAN_7
      · exact prime_fortyTwoAN_11
      · exact prime_fortyTwoAN_13
      · exact prime_fortyTwoAN_173
      · exact prime_fortyTwoAN_953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 14853048211) ^ 7426524105 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 14853048211) ^ 4951016070 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 14853048211) ^ 2970609642 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 14853048211) ^ 2121864030 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 14853048211) ^ 1350277110 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 14853048211) ^ 1142542170 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 14853048211) ^ 85855770 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 14853048211) ^ 15585570 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_16828374767 : Nat.Prime 16828374767 := by
  apply lucas_primality 16828374767 (5 : ZMod 16828374767)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (17, 1), (269, 1), (262853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (17, 1), (269, 1), (262853, 1)] : List FactorBlock).map factorBlockValue).prod) = 16828374767 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_7
      · exact prime_fortyTwoAN_17
      · exact prime_fortyTwoAN_269
      · exact prime_fortyTwoAN_262853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 16828374767) ^ 8414187383 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 16828374767) ^ 2404053538 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 16828374767) ^ 989904398 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 16828374767) ^ 62559014 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 16828374767) ^ 64022 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_17037864143 : Nat.Prime 17037864143 := by
  apply lucas_primality 17037864143 (5 : ZMod 17037864143)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (41, 1), (709, 1), (22543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (41, 1), (709, 1), (22543, 1)] : List FactorBlock).map factorBlockValue).prod) = 17037864143 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_13
      · exact prime_fortyTwoAN_41
      · exact prime_fortyTwoAN_709
      · exact prime_fortyTwoAN_22543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 17037864143) ^ 8518932071 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 17037864143) ^ 1310604934 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 17037864143) ^ 415557662 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 17037864143) ^ 24030838 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 17037864143) ^ 755794 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_23241977389 : Nat.Prime 23241977389 := by
  apply lucas_primality 23241977389 (2 : ZMod 23241977389)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (23, 1), (101, 1), (39703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (23, 1), (101, 1), (39703, 1)] : List FactorBlock).map factorBlockValue).prod) = 23241977389 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_7
      · exact prime_fortyTwoAN_23
      · exact prime_fortyTwoAN_101
      · exact prime_fortyTwoAN_39703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 23241977389) ^ 11620988694 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 23241977389) ^ 7747325796 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 23241977389) ^ 3320282484 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 23241977389) ^ 1010520756 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 23241977389) ^ 230118588 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 23241977389) ^ 585396 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_24913302187 : Nat.Prime 24913302187 := by
  apply lucas_primality 24913302187 (2 : ZMod 24913302187)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (487, 1), (2621, 1), (3253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (487, 1), (2621, 1), (3253, 1)] : List FactorBlock).map factorBlockValue).prod) = 24913302187 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_487
      · exact prime_fortyTwoAN_2621
      · exact prime_fortyTwoAN_3253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 24913302187) ^ 12456651093 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 24913302187) ^ 8304434062 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 24913302187) ^ 51156678 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 24913302187) ^ 9505266 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 24913302187) ^ 7658562 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_30429025931 : Nat.Prime 30429025931 := by
  apply lucas_primality 30429025931 (2 : ZMod 30429025931)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (71, 1), (42857783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (71, 1), (42857783, 1)] : List FactorBlock).map factorBlockValue).prod) = 30429025931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_5
      · exact prime_fortyTwoAN_71
      · exact prime_fortyTwoAN_42857783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 30429025931) ^ 15214512965 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 30429025931) ^ 6085805186 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 30429025931) ^ 428577830 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 30429025931) ^ 710 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_31586312203 : Nat.Prime 31586312203 := by
  apply lucas_primality 31586312203 (2 : ZMod 31586312203)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5264385367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5264385367, 1)] : List FactorBlock).map factorBlockValue).prod) = 31586312203 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_5264385367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 31586312203) ^ 15793156101 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 31586312203) ^ 10528770734 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 31586312203) ^ 6 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_32244294937 : Nat.Prime 32244294937 := by
  apply lucas_primality 32244294937 (10 : ZMod 32244294937)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (131, 1), (149, 1), (9833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (131, 1), (149, 1), (9833, 1)] : List FactorBlock).map factorBlockValue).prod) = 32244294937 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_7
      · exact prime_fortyTwoAN_131
      · exact prime_fortyTwoAN_149
      · exact prime_fortyTwoAN_9833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 32244294937) ^ 16122147468 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (10 : ZMod 32244294937) ^ 10748098312 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (10 : ZMod 32244294937) ^ 4606327848 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (10 : ZMod 32244294937) ^ 246139656 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (10 : ZMod 32244294937) ^ 216404664 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (10 : ZMod 32244294937) ^ 3279192 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_32976288733 : Nat.Prime 32976288733 := by
  apply lucas_primality 32976288733 (5 : ZMod 32976288733)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (23, 1), (59, 1), (113, 1), (17921, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (23, 1), (59, 1), (113, 1), (17921, 1)] : List FactorBlock).map factorBlockValue).prod) = 32976288733 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_23
      · exact prime_fortyTwoAN_59
      · exact prime_fortyTwoAN_113
      · exact prime_fortyTwoAN_17921
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 32976288733) ^ 16488144366 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 32976288733) ^ 10992096244 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 32976288733) ^ 1433751684 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 32976288733) ^ 558920148 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 32976288733) ^ 291825564 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 32976288733) ^ 1840092 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_35105030159 : Nat.Prime 35105030159 := by
  apply lucas_primality 35105030159 (11 : ZMod 35105030159)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (17, 1), (67, 1), (107, 1), (13093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (17, 1), (67, 1), (107, 1), (13093, 1)] : List FactorBlock).map factorBlockValue).prod) = 35105030159 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_11
      · exact prime_fortyTwoAN_17
      · exact prime_fortyTwoAN_67
      · exact prime_fortyTwoAN_107
      · exact prime_fortyTwoAN_13093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 35105030159) ^ 17552515079 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (11 : ZMod 35105030159) ^ 3191366378 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (11 : ZMod 35105030159) ^ 2065001774 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (11 : ZMod 35105030159) ^ 523955674 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (11 : ZMod 35105030159) ^ 328084394 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (11 : ZMod 35105030159) ^ 2681206 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_36793525309 : Nat.Prime 36793525309 := by
  apply lucas_primality 36793525309 (11 : ZMod 36793525309)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (29, 1), (47, 1), (197, 1), (601, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (29, 1), (47, 1), (197, 1), (601, 1)] : List FactorBlock).map factorBlockValue).prod) = 36793525309 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_19
      · exact prime_fortyTwoAN_29
      · exact prime_fortyTwoAN_47
      · exact prime_fortyTwoAN_197
      · exact prime_fortyTwoAN_601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 36793525309) ^ 18396762654 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (11 : ZMod 36793525309) ^ 12264508436 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (11 : ZMod 36793525309) ^ 1936501332 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (11 : ZMod 36793525309) ^ 1268742252 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (11 : ZMod 36793525309) ^ 782840964 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (11 : ZMod 36793525309) ^ 186769164 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (11 : ZMod 36793525309) ^ 61220508 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_38651421607 : Nat.Prime 38651421607 := by
  apply lucas_primality 38651421607 (3 : ZMod 38651421607)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (173, 1), (1249, 1), (4259, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (173, 1), (1249, 1), (4259, 1)] : List FactorBlock).map factorBlockValue).prod) = 38651421607 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_7
      · exact prime_fortyTwoAN_173
      · exact prime_fortyTwoAN_1249
      · exact prime_fortyTwoAN_4259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 38651421607) ^ 19325710803 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 38651421607) ^ 12883807202 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 38651421607) ^ 5521631658 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 38651421607) ^ 223418622 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 38651421607) ^ 30945894 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 38651421607) ^ 9075234 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_44960719007 : Nat.Prime 44960719007 := by
  apply lucas_primality 44960719007 (5 : ZMod 44960719007)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (151, 1), (479, 1), (6343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (151, 1), (479, 1), (6343, 1)] : List FactorBlock).map factorBlockValue).prod) = 44960719007 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_7
      · exact prime_fortyTwoAN_151
      · exact prime_fortyTwoAN_479
      · exact prime_fortyTwoAN_6343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 44960719007) ^ 22480359503 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 44960719007) ^ 6422959858 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 44960719007) ^ 297753106 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 44960719007) ^ 93863714 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 44960719007) ^ 7088242 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_51165623833 : Nat.Prime 51165623833 := by
  apply lucas_primality 51165623833 (5 : ZMod 51165623833)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5573, 1), (382541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5573, 1), (382541, 1)] : List FactorBlock).map factorBlockValue).prod) = 51165623833 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_5573
      · exact prime_fortyTwoAN_382541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 51165623833) ^ 25582811916 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 51165623833) ^ 17055207944 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 51165623833) ^ 9180984 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 51165623833) ^ 133752 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_55197867029 : Nat.Prime 55197867029 := by
  apply lucas_primality 55197867029 (2 : ZMod 55197867029)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (37, 1), (372958561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (37, 1), (372958561, 1)] : List FactorBlock).map factorBlockValue).prod) = 55197867029 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_37
      · exact prime_fortyTwoAN_372958561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 55197867029) ^ 27598933514 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 55197867029) ^ 1491834244 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 55197867029) ^ 148 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_69747157289 : Nat.Prime 69747157289 := by
  apply lucas_primality 69747157289 (3 : ZMod 69747157289)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (71, 1), (131, 1), (929, 1), (1009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (71, 1), (131, 1), (929, 1), (1009, 1)] : List FactorBlock).map factorBlockValue).prod) = 69747157289 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_71
      · exact prime_fortyTwoAN_131
      · exact prime_fortyTwoAN_929
      · exact prime_fortyTwoAN_1009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 69747157289) ^ 34873578644 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 69747157289) ^ 982354328 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 69747157289) ^ 532421048 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 69747157289) ^ 75077672 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 69747157289) ^ 69125032 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_73987284121 : Nat.Prime 73987284121 := by
  apply lucas_primality 73987284121 (29 : ZMod 73987284121)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (23, 1), (73, 1), (367219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (23, 1), (73, 1), (367219, 1)] : List FactorBlock).map factorBlockValue).prod) = 73987284121 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_5
      · exact prime_fortyTwoAN_23
      · exact prime_fortyTwoAN_73
      · exact prime_fortyTwoAN_367219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (29 : ZMod 73987284121) ^ 36993642060 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (29 : ZMod 73987284121) ^ 24662428040 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (29 : ZMod 73987284121) ^ 14797456824 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (29 : ZMod 73987284121) ^ 3216838440 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (29 : ZMod 73987284121) ^ 1013524440 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (29 : ZMod 73987284121) ^ 201480 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_81554969011 : Nat.Prime 81554969011 := by
  apply lucas_primality 81554969011 (3 : ZMod 81554969011)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (19, 1), (143078893, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (19, 1), (143078893, 1)] : List FactorBlock).map factorBlockValue).prod) = 81554969011 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_5
      · exact prime_fortyTwoAN_19
      · exact prime_fortyTwoAN_143078893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 81554969011) ^ 40777484505 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 81554969011) ^ 27184989670 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 81554969011) ^ 16310993802 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 81554969011) ^ 4292366790 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 81554969011) ^ 570 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_84811121713 : Nat.Prime 84811121713 := by
  apply lucas_primality 84811121713 (5 : ZMod 84811121713)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (19, 1), (563, 1), (18353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (19, 1), (563, 1), (18353, 1)] : List FactorBlock).map factorBlockValue).prod) = 84811121713 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_19
      · exact prime_fortyTwoAN_563
      · exact prime_fortyTwoAN_18353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 84811121713) ^ 42405560856 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 84811121713) ^ 28270373904 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 84811121713) ^ 4463743248 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 84811121713) ^ 150641424 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 84811121713) ^ 4621104 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_84927410431 : Nat.Prime 84927410431 := by
  apply lucas_primality 84927410431 (6 : ZMod 84927410431)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (61, 1), (67, 1), (692663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (61, 1), (67, 1), (692663, 1)] : List FactorBlock).map factorBlockValue).prod) = 84927410431 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_5
      · exact prime_fortyTwoAN_61
      · exact prime_fortyTwoAN_67
      · exact prime_fortyTwoAN_692663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 84927410431) ^ 42463705215 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (6 : ZMod 84927410431) ^ 28309136810 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (6 : ZMod 84927410431) ^ 16985482086 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (6 : ZMod 84927410431) ^ 1392252630 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (6 : ZMod 84927410431) ^ 1267573290 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (6 : ZMod 84927410431) ^ 122610 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_86317688251 : Nat.Prime 86317688251 := by
  apply lucas_primality 86317688251 (10 : ZMod 86317688251)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 3), (38363417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 3), (38363417, 1)] : List FactorBlock).map factorBlockValue).prod) = 86317688251 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_5
      · exact prime_fortyTwoAN_38363417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 86317688251) ^ 43158844125 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (10 : ZMod 86317688251) ^ 28772562750 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (10 : ZMod 86317688251) ^ 17263537650 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (10 : ZMod 86317688251) ^ 2250 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_87467016139 : Nat.Prime 87467016139 := by
  apply lucas_primality 87467016139 (2 : ZMod 87467016139)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (14577836023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (14577836023, 1)] : List FactorBlock).map factorBlockValue).prod) = 87467016139 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_14577836023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 87467016139) ^ 43733508069 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 87467016139) ^ 29155672046 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 87467016139) ^ 6 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_88525349741 : Nat.Prime 88525349741 := by
  apply lucas_primality 88525349741 (2 : ZMod 88525349741)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (37, 1), (119628851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (37, 1), (119628851, 1)] : List FactorBlock).map factorBlockValue).prod) = 88525349741 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_5
      · exact prime_fortyTwoAN_37
      · exact prime_fortyTwoAN_119628851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 88525349741) ^ 44262674870 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 88525349741) ^ 17705069948 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 88525349741) ^ 2392577020 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 88525349741) ^ 740 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_102310987907 : Nat.Prime 102310987907 := by
  apply lucas_primality 102310987907 (2 : ZMod 102310987907)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 2), (7013, 1), (13789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 2), (7013, 1), (13789, 1)] : List FactorBlock).map factorBlockValue).prod) = 102310987907 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_23
      · exact prime_fortyTwoAN_7013
      · exact prime_fortyTwoAN_13789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 102310987907) ^ 51155493953 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 102310987907) ^ 4448303822 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 102310987907) ^ 14588762 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 102310987907) ^ 7419754 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_104878619159 : Nat.Prime 104878619159 := by
  apply lucas_primality 104878619159 (13 : ZMod 104878619159)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (16097, 1), (3257707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (16097, 1), (3257707, 1)] : List FactorBlock).map factorBlockValue).prod) = 104878619159 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_16097
      · exact prime_fortyTwoAN_3257707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 104878619159) ^ 52439309579 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (13 : ZMod 104878619159) ^ 6515414 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (13 : ZMod 104878619159) ^ 32194 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_106528215379 : Nat.Prime 106528215379 := by
  apply lucas_primality 106528215379 (2 : ZMod 106528215379)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (47, 1), (1097, 1), (26489, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (47, 1), (1097, 1), (26489, 1)] : List FactorBlock).map factorBlockValue).prod) = 106528215379 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_13
      · exact prime_fortyTwoAN_47
      · exact prime_fortyTwoAN_1097
      · exact prime_fortyTwoAN_26489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 106528215379) ^ 53264107689 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 106528215379) ^ 35509405126 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 106528215379) ^ 8194478106 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 106528215379) ^ 2266557774 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 106528215379) ^ 97108674 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 106528215379) ^ 4021602 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_110361057607 : Nat.Prime 110361057607 := by
  apply lucas_primality 110361057607 (11 : ZMod 110361057607)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (17, 1), (120219017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (17, 1), (120219017, 1)] : List FactorBlock).map factorBlockValue).prod) = 110361057607 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_17
      · exact prime_fortyTwoAN_120219017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 110361057607) ^ 55180528803 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (11 : ZMod 110361057607) ^ 36787019202 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (11 : ZMod 110361057607) ^ 6491826918 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (11 : ZMod 110361057607) ^ 918 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_120863194567 : Nat.Prime 120863194567 := by
  apply lucas_primality 120863194567 (3 : ZMod 120863194567)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (439, 1), (45885799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (439, 1), (45885799, 1)] : List FactorBlock).map factorBlockValue).prod) = 120863194567 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_439
      · exact prime_fortyTwoAN_45885799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 120863194567) ^ 60431597283 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 120863194567) ^ 40287731522 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 120863194567) ^ 275314794 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 120863194567) ^ 2634 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_152394958517 : Nat.Prime 152394958517 := by
  apply lucas_primality 152394958517 (2 : ZMod 152394958517)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (593, 1), (709, 1), (90617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (593, 1), (709, 1), (90617, 1)] : List FactorBlock).map factorBlockValue).prod) = 152394958517 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_593
      · exact prime_fortyTwoAN_709
      · exact prime_fortyTwoAN_90617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 152394958517) ^ 76197479258 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 152394958517) ^ 256989812 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 152394958517) ^ 214943524 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 152394958517) ^ 1681748 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_194932333439 : Nat.Prime 194932333439 := by
  apply lucas_primality 194932333439 (7 : ZMod 194932333439)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (192979, 1), (505061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (192979, 1), (505061, 1)] : List FactorBlock).map factorBlockValue).prod) = 194932333439 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_192979
      · exact prime_fortyTwoAN_505061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 194932333439) ^ 97466166719 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (7 : ZMod 194932333439) ^ 1010122 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (7 : ZMod 194932333439) ^ 385958 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_254426385761 : Nat.Prime 254426385761 := by
  apply lucas_primality 254426385761 (3 : ZMod 254426385761)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (1590164911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (1590164911, 1)] : List FactorBlock).map factorBlockValue).prod) = 254426385761 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_5
      · exact prime_fortyTwoAN_1590164911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 254426385761) ^ 127213192880 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 254426385761) ^ 50885277152 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 254426385761) ^ 160 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_277508030299 : Nat.Prime 277508030299 := by
  apply lucas_primality 277508030299 (3 : ZMod 277508030299)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (149, 1), (1429, 1), (217223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (149, 1), (1429, 1), (217223, 1)] : List FactorBlock).map factorBlockValue).prod) = 277508030299 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_149
      · exact prime_fortyTwoAN_1429
      · exact prime_fortyTwoAN_217223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 277508030299) ^ 138754015149 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 277508030299) ^ 92502676766 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 277508030299) ^ 1862470002 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 277508030299) ^ 194197362 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 277508030299) ^ 1277526 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_326767060643 : Nat.Prime 326767060643 := by
  apply lucas_primality 326767060643 (2 : ZMod 326767060643)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (14853048211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (14853048211, 1)] : List FactorBlock).map factorBlockValue).prod) = 326767060643 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_11
      · exact prime_fortyTwoAN_14853048211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 326767060643) ^ 163383530321 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 326767060643) ^ 29706096422 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 326767060643) ^ 22 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_400780711729 : Nat.Prime 400780711729 := by
  apply lucas_primality 400780711729 (7 : ZMod 400780711729)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (17, 1), (23, 1), (73, 1), (32503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (17, 1), (23, 1), (73, 1), (32503, 1)] : List FactorBlock).map factorBlockValue).prod) = 400780711729 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_17
      · exact prime_fortyTwoAN_23
      · exact prime_fortyTwoAN_73
      · exact prime_fortyTwoAN_32503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 400780711729) ^ 200390355864 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (7 : ZMod 400780711729) ^ 133593570576 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (7 : ZMod 400780711729) ^ 23575335984 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (7 : ZMod 400780711729) ^ 17425248336 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (7 : ZMod 400780711729) ^ 5490146736 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (7 : ZMod 400780711729) ^ 12330576 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_420303742769 : Nat.Prime 420303742769 := by
  apply lucas_primality 420303742769 (3 : ZMod 420303742769)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (13, 1), (288670153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (13, 1), (288670153, 1)] : List FactorBlock).map factorBlockValue).prod) = 420303742769 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_7
      · exact prime_fortyTwoAN_13
      · exact prime_fortyTwoAN_288670153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 420303742769) ^ 210151871384 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 420303742769) ^ 60043391824 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 420303742769) ^ 32331057136 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 420303742769) ^ 1456 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_462094662389 : Nat.Prime 462094662389 := by
  apply lucas_primality 462094662389 (2 : ZMod 462094662389)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (397, 1), (2531, 1), (6763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (397, 1), (2531, 1), (6763, 1)] : List FactorBlock).map factorBlockValue).prod) = 462094662389 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_17
      · exact prime_fortyTwoAN_397
      · exact prime_fortyTwoAN_2531
      · exact prime_fortyTwoAN_6763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 462094662389) ^ 231047331194 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 27182038964 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 1163966404 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 182573948 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 68326876 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_498528184081 : Nat.Prime 498528184081 := by
  apply lucas_primality 498528184081 (19 : ZMod 498528184081)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (47, 1), (5903, 1), (7487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (47, 1), (5903, 1), (7487, 1)] : List FactorBlock).map factorBlockValue).prod) = 498528184081 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_5
      · exact prime_fortyTwoAN_47
      · exact prime_fortyTwoAN_5903
      · exact prime_fortyTwoAN_7487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 498528184081) ^ 249264092040 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (19 : ZMod 498528184081) ^ 166176061360 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (19 : ZMod 498528184081) ^ 99705636816 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (19 : ZMod 498528184081) ^ 10606982640 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (19 : ZMod 498528184081) ^ 84453360 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (19 : ZMod 498528184081) ^ 66585840 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_535986344717 : Nat.Prime 535986344717 := by
  apply lucas_primality 535986344717 (2 : ZMod 535986344717)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (41, 1), (1091, 1), (2995609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (41, 1), (1091, 1), (2995609, 1)] : List FactorBlock).map factorBlockValue).prod) = 535986344717 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_41
      · exact prime_fortyTwoAN_1091
      · exact prime_fortyTwoAN_2995609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 535986344717) ^ 267993172358 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 535986344717) ^ 13072837676 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 535986344717) ^ 491279876 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 535986344717) ^ 178924 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_852391097893 : Nat.Prime 852391097893 := by
  apply lucas_primality 852391097893 (2 : ZMod 852391097893)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (853, 1), (27757949, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (853, 1), (27757949, 1)] : List FactorBlock).map factorBlockValue).prod) = 852391097893 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_853
      · exact prime_fortyTwoAN_27757949
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 852391097893) ^ 426195548946 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 852391097893) ^ 284130365964 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 852391097893) ^ 999286164 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 852391097893) ^ 30708 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_964862349257 : Nat.Prime 964862349257 := by
  apply lucas_primality 964862349257 (5 : ZMod 964862349257)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (9277522589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (9277522589, 1)] : List FactorBlock).map factorBlockValue).prod) = 964862349257 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_13
      · exact prime_fortyTwoAN_9277522589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 964862349257) ^ 482431174628 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 964862349257) ^ 74220180712 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 964862349257) ^ 104 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_977519457737 : Nat.Prime 977519457737 := by
  apply lucas_primality 977519457737 (3 : ZMod 977519457737)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (1259, 1), (3643, 1), (26641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (1259, 1), (3643, 1), (26641, 1)] : List FactorBlock).map factorBlockValue).prod) = 977519457737 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_1259
      · exact prime_fortyTwoAN_3643
      · exact prime_fortyTwoAN_26641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 977519457737) ^ 488759728868 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 977519457737) ^ 776425304 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 977519457737) ^ 268328152 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 977519457737) ^ 36692296 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_1026349089653 : Nat.Prime 1026349089653 := by
  apply lucas_primality 1026349089653 (2 : ZMod 1026349089653)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1223, 1), (209801531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1223, 1), (209801531, 1)] : List FactorBlock).map factorBlockValue).prod) = 1026349089653 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_1223
      · exact prime_fortyTwoAN_209801531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1026349089653) ^ 513174544826 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 1026349089653) ^ 839206124 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 1026349089653) ^ 4892 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_1184113519489 : Nat.Prime 1184113519489 := by
  apply lucas_primality 1184113519489 (7 : ZMod 1184113519489)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 2), (29, 1), (35444011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 2), (29, 1), (35444011, 1)] : List FactorBlock).map factorBlockValue).prod) = 1184113519489 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_29
      · exact prime_fortyTwoAN_35444011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 1184113519489) ^ 592056759744 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (7 : ZMod 1184113519489) ^ 394704506496 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (7 : ZMod 1184113519489) ^ 40831500672 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (7 : ZMod 1184113519489) ^ 33408 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_1348821570211 : Nat.Prime 1348821570211 := by
  apply lucas_primality 1348821570211 (2 : ZMod 1348821570211)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (44960719007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (44960719007, 1)] : List FactorBlock).map factorBlockValue).prod) = 1348821570211 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_5
      · exact prime_fortyTwoAN_44960719007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1348821570211) ^ 674410785105 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 1348821570211) ^ 449607190070 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 1348821570211) ^ 269764314042 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 1348821570211) ^ 30 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_1515172544143 : Nat.Prime 1515172544143 := by
  apply lucas_primality 1515172544143 (5 : ZMod 1515172544143)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (43, 1), (189443929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (43, 1), (189443929, 1)] : List FactorBlock).map factorBlockValue).prod) = 1515172544143 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_31
      · exact prime_fortyTwoAN_43
      · exact prime_fortyTwoAN_189443929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1515172544143) ^ 757586272071 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 1515172544143) ^ 505057514714 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 1515172544143) ^ 48876533682 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 1515172544143) ^ 35236570794 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 1515172544143) ^ 7998 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_1521962095903 : Nat.Prime 1521962095903 := by
  apply lucas_primality 1521962095903 (3 : ZMod 1521962095903)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (35279, 1), (7190123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (35279, 1), (7190123, 1)] : List FactorBlock).map factorBlockValue).prod) = 1521962095903 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_35279
      · exact prime_fortyTwoAN_7190123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1521962095903) ^ 760981047951 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 507320698634 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 43140738 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 211674 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_1770184470797 : Nat.Prime 1770184470797 := by
  apply lucas_primality 1770184470797 (2 : ZMod 1770184470797)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (2293, 1), (27571249, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (2293, 1), (27571249, 1)] : List FactorBlock).map factorBlockValue).prod) = 1770184470797 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_7
      · exact prime_fortyTwoAN_2293
      · exact prime_fortyTwoAN_27571249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1770184470797) ^ 885092235398 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 1770184470797) ^ 252883495828 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 1770184470797) ^ 771994972 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 1770184470797) ^ 64204 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_1898100541591 : Nat.Prime 1898100541591 := by
  apply lucas_primality 1898100541591 (3 : ZMod 1898100541591)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (457, 1), (1433, 1), (8783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (457, 1), (1433, 1), (8783, 1)] : List FactorBlock).map factorBlockValue).prod) = 1898100541591 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_5
      · exact prime_fortyTwoAN_11
      · exact prime_fortyTwoAN_457
      · exact prime_fortyTwoAN_1433
      · exact prime_fortyTwoAN_8783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1898100541591) ^ 949050270795 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 1898100541591) ^ 632700180530 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 1898100541591) ^ 379620108318 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 1898100541591) ^ 172554594690 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 1898100541591) ^ 4153392870 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 1898100541591) ^ 1324564230 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 1898100541591) ^ 216110730 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_2716813051523 : Nat.Prime 2716813051523 := by
  apply lucas_primality 2716813051523 (2 : ZMod 2716813051523)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (449, 1), (23743, 1), (127423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (449, 1), (23743, 1), (127423, 1)] : List FactorBlock).map factorBlockValue).prod) = 2716813051523 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_449
      · exact prime_fortyTwoAN_23743
      · exact prime_fortyTwoAN_127423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2716813051523) ^ 1358406525761 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 2716813051523) ^ 6050808578 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 2716813051523) ^ 114425854 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 2716813051523) ^ 21321214 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_5083141924411 : Nat.Prime 5083141924411 := by
  apply lucas_primality 5083141924411 (2 : ZMod 5083141924411)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (103, 1), (131, 1), (547, 1), (2087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (103, 1), (131, 1), (547, 1), (2087, 1)] : List FactorBlock).map factorBlockValue).prod) = 5083141924411 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_5
      · exact prime_fortyTwoAN_11
      · exact prime_fortyTwoAN_103
      · exact prime_fortyTwoAN_131
      · exact prime_fortyTwoAN_547
      · exact prime_fortyTwoAN_2087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5083141924411) ^ 2541570962205 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 5083141924411) ^ 1694380641470 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 5083141924411) ^ 1016628384882 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 5083141924411) ^ 462103811310 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 5083141924411) ^ 49350892470 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 5083141924411) ^ 38802610110 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 5083141924411) ^ 9292764030 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 5083141924411) ^ 2435621430 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_7007144209529 : Nat.Prime 7007144209529 := by
  apply lucas_primality 7007144209529 (3 : ZMod 7007144209529)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (112573, 1), (7780667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (112573, 1), (7780667, 1)] : List FactorBlock).map factorBlockValue).prod) = 7007144209529 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_112573
      · exact prime_fortyTwoAN_7780667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 7007144209529) ^ 3503572104764 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 7007144209529) ^ 62245336 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 7007144209529) ^ 900584 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_13203689273969 : Nat.Prime 13203689273969 := by
  apply lucas_primality 13203689273969 (3 : ZMod 13203689273969)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (37, 1), (971, 1), (1031, 1), (22279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (37, 1), (971, 1), (1031, 1), (22279, 1)] : List FactorBlock).map factorBlockValue).prod) = 13203689273969 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_37
      · exact prime_fortyTwoAN_971
      · exact prime_fortyTwoAN_1031
      · exact prime_fortyTwoAN_22279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 13203689273969) ^ 6601844636984 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 13203689273969) ^ 356856466864 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 13203689273969) ^ 13598032208 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 13203689273969) ^ 12806682128 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 13203689273969) ^ 592651792 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_13392269608129 : Nat.Prime 13392269608129 := by
  apply lucas_primality 13392269608129 (14 : ZMod 13392269608129)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (17, 1), (5231, 1), (784367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (17, 1), (5231, 1), (784367, 1)] : List FactorBlock).map factorBlockValue).prod) = 13392269608129 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_17
      · exact prime_fortyTwoAN_5231
      · exact prime_fortyTwoAN_784367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 13392269608129) ^ 6696134804064 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (14 : ZMod 13392269608129) ^ 4464089869376 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (14 : ZMod 13392269608129) ^ 787780565184 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (14 : ZMod 13392269608129) ^ 2560173888 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (14 : ZMod 13392269608129) ^ 17073984 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_16960095999137 : Nat.Prime 16960095999137 := by
  apply lucas_primality 16960095999137 (3 : ZMod 16960095999137)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (112019, 1), (4731367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (112019, 1), (4731367, 1)] : List FactorBlock).map factorBlockValue).prod) = 16960095999137 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_112019
      · exact prime_fortyTwoAN_4731367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 16960095999137) ^ 8480047999568 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 16960095999137) ^ 151403744 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 16960095999137) ^ 3584608 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_18401798692153 : Nat.Prime 18401798692153 := by
  apply lucas_primality 18401798692153 (10 : ZMod 18401798692153)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (29, 1), (163, 1), (54068233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (29, 1), (163, 1), (54068233, 1)] : List FactorBlock).map factorBlockValue).prod) = 18401798692153 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_29
      · exact prime_fortyTwoAN_163
      · exact prime_fortyTwoAN_54068233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 18401798692153) ^ 9200899346076 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (10 : ZMod 18401798692153) ^ 6133932897384 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (10 : ZMod 18401798692153) ^ 634544782488 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (10 : ZMod 18401798692153) ^ 112894470504 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (10 : ZMod 18401798692153) ^ 340344 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_21910764024983 : Nat.Prime 21910764024983 := by
  apply lucas_primality 21910764024983 (5 : ZMod 21910764024983)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (19, 1), (37, 1), (97, 1), (22951043, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (19, 1), (37, 1), (97, 1), (22951043, 1)] : List FactorBlock).map factorBlockValue).prod) = 21910764024983 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_7
      · exact prime_fortyTwoAN_19
      · exact prime_fortyTwoAN_37
      · exact prime_fortyTwoAN_97
      · exact prime_fortyTwoAN_22951043
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 21910764024983) ^ 10955382012491 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 21910764024983) ^ 3130109146426 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 21910764024983) ^ 1153198106578 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 21910764024983) ^ 592182811486 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 21910764024983) ^ 225884165206 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 21910764024983) ^ 954674 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_27346626158783 : Nat.Prime 27346626158783 := by
  apply lucas_primality 27346626158783 (5 : ZMod 27346626158783)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (23, 1), (84927410431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (23, 1), (84927410431, 1)] : List FactorBlock).map factorBlockValue).prod) = 27346626158783 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_7
      · exact prime_fortyTwoAN_23
      · exact prime_fortyTwoAN_84927410431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 27346626158783) ^ 13673313079391 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 27346626158783) ^ 3906660879826 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 27346626158783) ^ 1188983746034 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 27346626158783) ^ 322 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_29073707324071 : Nat.Prime 29073707324071 := by
  apply lucas_primality 29073707324071 (3 : ZMod 29073707324071)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (67, 1), (1399, 1), (10339193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (67, 1), (1399, 1), (10339193, 1)] : List FactorBlock).map factorBlockValue).prod) = 29073707324071 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_5
      · exact prime_fortyTwoAN_67
      · exact prime_fortyTwoAN_1399
      · exact prime_fortyTwoAN_10339193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 29073707324071) ^ 14536853662035 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 29073707324071) ^ 9691235774690 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 29073707324071) ^ 5814741464814 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 29073707324071) ^ 433935930210 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 29073707324071) ^ 20781777930 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 29073707324071) ^ 2811990 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_34264205873333 : Nat.Prime 34264205873333 := by
  apply lucas_primality 34264205873333 (2 : ZMod 34264205873333)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (719, 1), (6691, 1), (1780577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (719, 1), (6691, 1), (1780577, 1)] : List FactorBlock).map factorBlockValue).prod) = 34264205873333 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_719
      · exact prime_fortyTwoAN_6691
      · exact prime_fortyTwoAN_1780577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 34264205873333) ^ 17132102936666 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 34264205873333) ^ 47655362828 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 34264205873333) ^ 5120939452 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 34264205873333) ^ 19243316 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_38554545693913 : Nat.Prime 38554545693913 := by
  apply lucas_primality 38554545693913 (10 : ZMod 38554545693913)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (59, 1), (293, 1), (317, 1), (293147, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (59, 1), (293, 1), (317, 1), (293147, 1)] : List FactorBlock).map factorBlockValue).prod) = 38554545693913 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_59
      · exact prime_fortyTwoAN_293
      · exact prime_fortyTwoAN_317
      · exact prime_fortyTwoAN_293147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 38554545693913) ^ 19277272846956 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (10 : ZMod 38554545693913) ^ 12851515231304 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (10 : ZMod 38554545693913) ^ 653466876168 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (10 : ZMod 38554545693913) ^ 131585480184 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (10 : ZMod 38554545693913) ^ 121623172536 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (10 : ZMod 38554545693913) ^ 131519496 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_39530687550041 : Nat.Prime 39530687550041 := by
  apply lucas_primality 39530687550041 (3 : ZMod 39530687550041)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (101, 1), (5779, 1), (1693169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (101, 1), (5779, 1), (1693169, 1)] : List FactorBlock).map factorBlockValue).prod) = 39530687550041 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_5
      · exact prime_fortyTwoAN_101
      · exact prime_fortyTwoAN_5779
      · exact prime_fortyTwoAN_1693169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 39530687550041) ^ 19765343775020 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 39530687550041) ^ 7906137510008 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 39530687550041) ^ 391392946040 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 39530687550041) ^ 6840402760 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 39530687550041) ^ 23347160 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_41007301887107 : Nat.Prime 41007301887107 := by
  apply lucas_primality 41007301887107 (2 : ZMod 41007301887107)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (601, 1), (1069, 1), (31913837, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (601, 1), (1069, 1), (31913837, 1)] : List FactorBlock).map factorBlockValue).prod) = 41007301887107 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_601
      · exact prime_fortyTwoAN_1069
      · exact prime_fortyTwoAN_31913837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 41007301887107) ^ 20503650943553 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 41007301887107) ^ 68231783506 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 41007301887107) ^ 38360432074 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 41007301887107) ^ 1284938 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_46558229274047 : Nat.Prime 46558229274047 := by
  apply lucas_primality 46558229274047 (7 : ZMod 46558229274047)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (23, 1), (151939, 1), (951637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (23, 1), (151939, 1), (951637, 1)] : List FactorBlock).map factorBlockValue).prod) = 46558229274047 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_7
      · exact prime_fortyTwoAN_23
      · exact prime_fortyTwoAN_151939
      · exact prime_fortyTwoAN_951637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 46558229274047) ^ 23279114637023 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (7 : ZMod 46558229274047) ^ 6651175610578 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (7 : ZMod 46558229274047) ^ 2024270838002 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (7 : ZMod 46558229274047) ^ 306427114 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (7 : ZMod 46558229274047) ^ 48924358 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_47447873988967 : Nat.Prime 47447873988967 := by
  apply lucas_primality 47447873988967 (3 : ZMod 47447873988967)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (11, 1), (211, 1), (126190483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (11, 1), (211, 1), (126190483, 1)] : List FactorBlock).map factorBlockValue).prod) = 47447873988967 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_11
      · exact prime_fortyTwoAN_211
      · exact prime_fortyTwoAN_126190483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 47447873988967) ^ 23723936994483 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 47447873988967) ^ 15815957996322 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 47447873988967) ^ 4313443089906 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 47447873988967) ^ 224871440706 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 47447873988967) ^ 376002 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_53799161710751 : Nat.Prime 53799161710751 := by
  apply lucas_primality 53799161710751 (7 : ZMod 53799161710751)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 3), (242227, 1), (888409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 3), (242227, 1), (888409, 1)] : List FactorBlock).map factorBlockValue).prod) = 53799161710751 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_5
      · exact prime_fortyTwoAN_242227
      · exact prime_fortyTwoAN_888409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 53799161710751) ^ 26899580855375 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (7 : ZMod 53799161710751) ^ 10759832342150 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (7 : ZMod 53799161710751) ^ 222102250 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (7 : ZMod 53799161710751) ^ 60556750 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_61107638809001 : Nat.Prime 61107638809001 := by
  apply lucas_primality 61107638809001 (6 : ZMod 61107638809001)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 3), (7, 1), (8729662687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 3), (7, 1), (8729662687, 1)] : List FactorBlock).map factorBlockValue).prod) = 61107638809001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_5
      · exact prime_fortyTwoAN_7
      · exact prime_fortyTwoAN_8729662687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 61107638809001) ^ 30553819404500 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (6 : ZMod 61107638809001) ^ 12221527761800 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (6 : ZMod 61107638809001) ^ 8729662687000 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (6 : ZMod 61107638809001) ^ 7000 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_65950130168807 : Nat.Prime 65950130168807 := by
  apply lucas_primality 65950130168807 (5 : ZMod 65950130168807)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (29, 1), (87467016139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (29, 1), (87467016139, 1)] : List FactorBlock).map factorBlockValue).prod) = 65950130168807 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_13
      · exact prime_fortyTwoAN_29
      · exact prime_fortyTwoAN_87467016139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 65950130168807) ^ 32975065084403 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 65950130168807) ^ 5073086936062 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 65950130168807) ^ 2274142419614 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 65950130168807) ^ 754 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_75763511577581 : Nat.Prime 75763511577581 := by
  apply lucas_primality 75763511577581 (3 : ZMod 75763511577581)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (4159, 1), (910838081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (4159, 1), (910838081, 1)] : List FactorBlock).map factorBlockValue).prod) = 75763511577581 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_5
      · exact prime_fortyTwoAN_4159
      · exact prime_fortyTwoAN_910838081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 75763511577581) ^ 37881755788790 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 75763511577581) ^ 15152702315516 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 75763511577581) ^ 18216761620 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 75763511577581) ^ 83180 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_81330270790577 : Nat.Prime 81330270790577 := by
  apply lucas_primality 81330270790577 (3 : ZMod 81330270790577)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5083141924411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5083141924411, 1)] : List FactorBlock).map factorBlockValue).prod) = 81330270790577 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_5083141924411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 81330270790577) ^ 40665135395288 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 81330270790577) ^ 16 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_103223297103137 : Nat.Prime 103223297103137 := by
  apply lucas_primality 103223297103137 (10 : ZMod 103223297103137)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (7, 3), (139, 1), (431, 1), (156979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (7, 3), (139, 1), (431, 1), (156979, 1)] : List FactorBlock).map factorBlockValue).prod) = 103223297103137 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_7
      · exact prime_fortyTwoAN_139
      · exact prime_fortyTwoAN_431
      · exact prime_fortyTwoAN_156979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 103223297103137) ^ 51611648551568 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (10 : ZMod 103223297103137) ^ 14746185300448 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (10 : ZMod 103223297103137) ^ 742613648224 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (10 : ZMod 103223297103137) ^ 239497209056 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (10 : ZMod 103223297103137) ^ 657561184 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_122215277618003 : Nat.Prime 122215277618003 := by
  apply lucas_primality 122215277618003 (2 : ZMod 122215277618003)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (61107638809001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (61107638809001, 1)] : List FactorBlock).map factorBlockValue).prod) = 122215277618003 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_61107638809001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 122215277618003) ^ 61107638809001 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 122215277618003) ^ 2 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_135096519595393 : Nat.Prime 135096519595393 := by
  apply lucas_primality 135096519595393 (10 : ZMod 135096519595393)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 2), (275491, 1), (425681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 2), (275491, 1), (425681, 1)] : List FactorBlock).map factorBlockValue).prod) = 135096519595393 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_275491
      · exact prime_fortyTwoAN_425681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 135096519595393) ^ 67548259797696 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (10 : ZMod 135096519595393) ^ 45032173198464 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (10 : ZMod 135096519595393) ^ 490384512 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (10 : ZMod 135096519595393) ^ 317365632 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_216706854253751 : Nat.Prime 216706854253751 := by
  apply lucas_primality 216706854253751 (7 : ZMod 216706854253751)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 4), (7, 1), (151883, 1), (163063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 4), (7, 1), (151883, 1), (163063, 1)] : List FactorBlock).map factorBlockValue).prod) = 216706854253751 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_5
      · exact prime_fortyTwoAN_7
      · exact prime_fortyTwoAN_151883
      · exact prime_fortyTwoAN_163063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 216706854253751) ^ 108353427126875 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (7 : ZMod 216706854253751) ^ 43341370850750 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (7 : ZMod 216706854253751) ^ 30958122036250 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (7 : ZMod 216706854253751) ^ 1426801250 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (7 : ZMod 216706854253751) ^ 1328976250 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_415034571917257 : Nat.Prime 415034571917257 := by
  apply lucas_primality 415034571917257 (5 : ZMod 415034571917257)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (29, 1), (59, 1), (13331, 1), (758159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (29, 1), (59, 1), (13331, 1), (758159, 1)] : List FactorBlock).map factorBlockValue).prod) = 415034571917257 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_29
      · exact prime_fortyTwoAN_59
      · exact prime_fortyTwoAN_13331
      · exact prime_fortyTwoAN_758159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 415034571917257) ^ 207517285958628 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 415034571917257) ^ 138344857305752 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 415034571917257) ^ 14311536962664 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 415034571917257) ^ 7034484269784 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 415034571917257) ^ 31133041176 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 415034571917257) ^ 547424184 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_598744972004371 : Nat.Prime 598744972004371 := by
  apply lucas_primality 598744972004371 (2 : ZMod 598744972004371)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (107, 1), (233, 1), (409, 1), (1957301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (107, 1), (233, 1), (409, 1), (1957301, 1)] : List FactorBlock).map factorBlockValue).prod) = 598744972004371 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_5
      · exact prime_fortyTwoAN_107
      · exact prime_fortyTwoAN_233
      · exact prime_fortyTwoAN_409
      · exact prime_fortyTwoAN_1957301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 598744972004371) ^ 299372486002185 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 598744972004371) ^ 199581657334790 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 598744972004371) ^ 119748994400874 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 598744972004371) ^ 5595747401910 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 598744972004371) ^ 2569720909890 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 598744972004371) ^ 1463924136930 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 598744972004371) ^ 305903370 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_618339305293807 : Nat.Prime 618339305293807 := by
  apply lucas_primality 618339305293807 (3 : ZMod 618339305293807)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (43, 1), (773, 1), (100015189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (43, 1), (773, 1), (100015189, 1)] : List FactorBlock).map factorBlockValue).prod) = 618339305293807 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_31
      · exact prime_fortyTwoAN_43
      · exact prime_fortyTwoAN_773
      · exact prime_fortyTwoAN_100015189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 618339305293807) ^ 309169652646903 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 618339305293807) ^ 206113101764602 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 618339305293807) ^ 19946429203026 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 618339305293807) ^ 14379983844042 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 618339305293807) ^ 799921481622 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 618339305293807) ^ 6182454 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_659702079143411 : Nat.Prime 659702079143411 := by
  apply lucas_primality 659702079143411 (2 : ZMod 659702079143411)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (230291, 1), (286464551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (230291, 1), (286464551, 1)] : List FactorBlock).map factorBlockValue).prod) = 659702079143411 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_5
      · exact prime_fortyTwoAN_230291
      · exact prime_fortyTwoAN_286464551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 659702079143411) ^ 329851039571705 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 659702079143411) ^ 131940415828682 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 659702079143411) ^ 2864645510 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 659702079143411) ^ 2302910 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_817016986973969 : Nat.Prime 817016986973969 := by
  apply lucas_primality 817016986973969 (3 : ZMod 817016986973969)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (11, 1), (223, 1), (283, 1), (5843, 1), (12589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (11, 1), (223, 1), (283, 1), (5843, 1), (12589, 1)] : List FactorBlock).map factorBlockValue).prod) = 817016986973969 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_11
      · exact prime_fortyTwoAN_223
      · exact prime_fortyTwoAN_283
      · exact prime_fortyTwoAN_5843
      · exact prime_fortyTwoAN_12589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 817016986973969) ^ 408508493486984 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 817016986973969) ^ 74274271543088 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 817016986973969) ^ 3663753304816 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 817016986973969) ^ 2886985819696 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 817016986973969) ^ 139828339376 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 817016986973969) ^ 64899276112 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_937016334000793 : Nat.Prime 937016334000793 := by
  apply lucas_primality 937016334000793 (5 : ZMod 937016334000793)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (1121831, 1), (3866927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (1121831, 1), (3866927, 1)] : List FactorBlock).map factorBlockValue).prod) = 937016334000793 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_1121831
      · exact prime_fortyTwoAN_3866927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 937016334000793) ^ 468508167000396 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 937016334000793) ^ 312338778000264 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 937016334000793) ^ 835256232 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 937016334000793) ^ 242315496 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_1217879459003443 : Nat.Prime 1217879459003443 := by
  apply lucas_primality 1217879459003443 (2 : ZMod 1217879459003443)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (7817, 1), (1366656409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (7817, 1), (1366656409, 1)] : List FactorBlock).map factorBlockValue).prod) = 1217879459003443 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_19
      · exact prime_fortyTwoAN_7817
      · exact prime_fortyTwoAN_1366656409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1217879459003443) ^ 608939729501721 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 1217879459003443) ^ 405959819667814 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 1217879459003443) ^ 64098918894918 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 1217879459003443) ^ 155798830626 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 1217879459003443) ^ 891138 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_1445126159443919 : Nat.Prime 1445126159443919 := by
  apply lucas_primality 1445126159443919 (7 : ZMod 1445126159443919)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (103223297103137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (103223297103137, 1)] : List FactorBlock).map factorBlockValue).prod) = 1445126159443919 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_7
      · exact prime_fortyTwoAN_103223297103137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 1445126159443919) ^ 722563079721959 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (7 : ZMod 1445126159443919) ^ 206446594206274 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (7 : ZMod 1445126159443919) ^ 14 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_1449186049018109 : Nat.Prime 1449186049018109 := by
  apply lucas_primality 1449186049018109 (2 : ZMod 1449186049018109)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (43, 1), (2591, 1), (2879, 1), (1129501, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (43, 1), (2591, 1), (2879, 1), (1129501, 1)] : List FactorBlock).map factorBlockValue).prod) = 1449186049018109 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_43
      · exact prime_fortyTwoAN_2591
      · exact prime_fortyTwoAN_2879
      · exact prime_fortyTwoAN_1129501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1449186049018109) ^ 724593024509054 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 1449186049018109) ^ 33702001139956 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 1449186049018109) ^ 559315341188 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 1449186049018109) ^ 503364379652 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 1449186049018109) ^ 1283032108 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_1583581521533941 : Nat.Prime 1583581521533941 := by
  apply lucas_primality 1583581521533941 (2 : ZMod 1583581521533941)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (5, 1), (977519457737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (5, 1), (977519457737, 1)] : List FactorBlock).map factorBlockValue).prod) = 1583581521533941 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_5
      · exact prime_fortyTwoAN_977519457737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1583581521533941) ^ 791790760766970 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 1583581521533941) ^ 527860507177980 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 1583581521533941) ^ 316716304306788 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 1583581521533941) ^ 1620 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_1590800534845771 : Nat.Prime 1590800534845771 := by
  apply lucas_primality 1590800534845771 (13 : ZMod 1590800534845771)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (599, 1), (88525349741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (599, 1), (88525349741, 1)] : List FactorBlock).map factorBlockValue).prod) = 1590800534845771 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_5
      · exact prime_fortyTwoAN_599
      · exact prime_fortyTwoAN_88525349741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 1590800534845771) ^ 795400267422885 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (13 : ZMod 1590800534845771) ^ 530266844948590 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (13 : ZMod 1590800534845771) ^ 318160106969154 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (13 : ZMod 1590800534845771) ^ 2655760492230 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (13 : ZMod 1590800534845771) ^ 17970 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_1667237541899513 : Nat.Prime 1667237541899513 := by
  apply lucas_primality 1667237541899513 (3 : ZMod 1667237541899513)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (41, 1), (462094662389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (41, 1), (462094662389, 1)] : List FactorBlock).map factorBlockValue).prod) = 1667237541899513 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_11
      · exact prime_fortyTwoAN_41
      · exact prime_fortyTwoAN_462094662389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1667237541899513) ^ 833618770949756 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 151567049263592 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 40664330290232 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 3608 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_2319415937889107 : Nat.Prime 2319415937889107 := by
  apply lucas_primality 2319415937889107 (2 : ZMod 2319415937889107)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (131, 1), (1801, 1), (100315387, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (131, 1), (1801, 1), (100315387, 1)] : List FactorBlock).map factorBlockValue).prod) = 2319415937889107 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_7
      · exact prime_fortyTwoAN_131
      · exact prime_fortyTwoAN_1801
      · exact prime_fortyTwoAN_100315387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2319415937889107) ^ 1159707968944553 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 2319415937889107) ^ 331345133984158 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 2319415937889107) ^ 17705465174726 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 2319415937889107) ^ 1287848938306 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 2319415937889107) ^ 23121238 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_2398625938490051 : Nat.Prime 2398625938490051 := by
  apply lucas_primality 2398625938490051 (2 : ZMod 2398625938490051)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (233, 2), (883650809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (233, 2), (883650809, 1)] : List FactorBlock).map factorBlockValue).prod) = 2398625938490051 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_5
      · exact prime_fortyTwoAN_233
      · exact prime_fortyTwoAN_883650809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2398625938490051) ^ 1199312969245025 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 2398625938490051) ^ 479725187698010 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 2398625938490051) ^ 10294531924850 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 2398625938490051) ^ 2714450 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_2405286251792507 : Nat.Prime 2405286251792507 := by
  apply lucas_primality 2405286251792507 (2 : ZMod 2405286251792507)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11467, 1), (104878619159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11467, 1), (104878619159, 1)] : List FactorBlock).map factorBlockValue).prod) = 2405286251792507 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_11467
      · exact prime_fortyTwoAN_104878619159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2405286251792507) ^ 1202643125896253 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 2405286251792507) ^ 209757238318 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 2405286251792507) ^ 22934 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_2870680595975869 : Nat.Prime 2870680595975869 := by
  apply lucas_primality 2870680595975869 (2 : ZMod 2870680595975869)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (18401798692153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (18401798692153, 1)] : List FactorBlock).map factorBlockValue).prod) = 2870680595975869 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_13
      · exact prime_fortyTwoAN_18401798692153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2870680595975869) ^ 1435340297987934 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 2870680595975869) ^ 956893531991956 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 2870680595975869) ^ 220821584305836 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 2870680595975869) ^ 156 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_3260946584647001 : Nat.Prime 3260946584647001 := by
  apply lucas_primality 3260946584647001 (6 : ZMod 3260946584647001)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 3), (19, 1), (23, 1), (127, 1), (58756853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 3), (19, 1), (23, 1), (127, 1), (58756853, 1)] : List FactorBlock).map factorBlockValue).prod) = 3260946584647001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_5
      · exact prime_fortyTwoAN_19
      · exact prime_fortyTwoAN_23
      · exact prime_fortyTwoAN_127
      · exact prime_fortyTwoAN_58756853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 3260946584647001) ^ 1630473292323500 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (6 : ZMod 3260946584647001) ^ 652189316929400 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (6 : ZMod 3260946584647001) ^ 171628767613000 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (6 : ZMod 3260946584647001) ^ 141780286289000 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (6 : ZMod 3260946584647001) ^ 25676744761000 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (6 : ZMod 3260946584647001) ^ 55499000 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_3273367641455083 : Nat.Prime 3273367641455083 := by
  apply lucas_primality 3273367641455083 (2 : ZMod 3273367641455083)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (3209, 1), (125789, 1), (1351547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (3209, 1), (125789, 1), (1351547, 1)] : List FactorBlock).map factorBlockValue).prod) = 3273367641455083 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_3209
      · exact prime_fortyTwoAN_125789
      · exact prime_fortyTwoAN_1351547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3273367641455083) ^ 1636683820727541 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 3273367641455083) ^ 1091122547151694 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 3273367641455083) ^ 1020058473498 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 3273367641455083) ^ 26022685938 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 3273367641455083) ^ 2421941406 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_7900383115523419 : Nat.Prime 7900383115523419 := by
  apply lucas_primality 7900383115523419 (2 : ZMod 7900383115523419)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (47, 1), (83, 1), (8747, 1), (2968373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (47, 1), (83, 1), (8747, 1), (2968373, 1)] : List FactorBlock).map factorBlockValue).prod) = 7900383115523419 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_13
      · exact prime_fortyTwoAN_47
      · exact prime_fortyTwoAN_83
      · exact prime_fortyTwoAN_8747
      · exact prime_fortyTwoAN_2968373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7900383115523419) ^ 3950191557761709 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 7900383115523419) ^ 2633461038507806 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 7900383115523419) ^ 607721778117186 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 7900383115523419) ^ 168093257777094 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 7900383115523419) ^ 95185338741246 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 7900383115523419) ^ 903210599694 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 7900383115523419) ^ 2661519666 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_7928223608012369 : Nat.Prime 7928223608012369 := by
  apply lucas_primality 7928223608012369 (3 : ZMod 7928223608012369)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (37, 1), (13392269608129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (37, 1), (13392269608129, 1)] : List FactorBlock).map factorBlockValue).prod) = 7928223608012369 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_37
      · exact prime_fortyTwoAN_13392269608129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 7928223608012369) ^ 3964111804006184 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 7928223608012369) ^ 214276313730064 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 7928223608012369) ^ 592 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_11655978276633277 : Nat.Prime 11655978276633277 := by
  apply lucas_primality 11655978276633277 (2 : ZMod 11655978276633277)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (47, 1), (81047, 1), (14999741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (47, 1), (81047, 1), (14999741, 1)] : List FactorBlock).map factorBlockValue).prod) = 11655978276633277 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_17
      · exact prime_fortyTwoAN_47
      · exact prime_fortyTwoAN_81047
      · exact prime_fortyTwoAN_14999741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 11655978276633277) ^ 5827989138316638 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 11655978276633277) ^ 3885326092211092 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 11655978276633277) ^ 685645780978428 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 11655978276633277) ^ 247999537800708 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 11655978276633277) ^ 143817516708 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 11655978276633277) ^ 777078636 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_14381527743168931 : Nat.Prime 14381527743168931 := by
  apply lucas_primality 14381527743168931 (7 : ZMod 14381527743168931)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (557, 1), (9719, 1), (29517919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (557, 1), (9719, 1), (29517919, 1)] : List FactorBlock).map factorBlockValue).prod) = 14381527743168931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_5
      · exact prime_fortyTwoAN_557
      · exact prime_fortyTwoAN_9719
      · exact prime_fortyTwoAN_29517919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 14381527743168931) ^ 7190763871584465 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (7 : ZMod 14381527743168931) ^ 4793842581056310 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (7 : ZMod 14381527743168931) ^ 2876305548633786 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (7 : ZMod 14381527743168931) ^ 25819618928490 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (7 : ZMod 14381527743168931) ^ 1479733279470 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (7 : ZMod 14381527743168931) ^ 487213470 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_16877197084131511 : Nat.Prime 16877197084131511 := by
  apply lucas_primality 16877197084131511 (6 : ZMod 16877197084131511)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (53, 1), (89, 1), (17037864143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (53, 1), (89, 1), (17037864143, 1)] : List FactorBlock).map factorBlockValue).prod) = 16877197084131511 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_5
      · exact prime_fortyTwoAN_7
      · exact prime_fortyTwoAN_53
      · exact prime_fortyTwoAN_89
      · exact prime_fortyTwoAN_17037864143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 16877197084131511) ^ 8438598542065755 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (6 : ZMod 16877197084131511) ^ 5625732361377170 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (6 : ZMod 16877197084131511) ^ 3375439416826302 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (6 : ZMod 16877197084131511) ^ 2411028154875930 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (6 : ZMod 16877197084131511) ^ 318437680832670 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (6 : ZMod 16877197084131511) ^ 189631427911590 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (6 : ZMod 16877197084131511) ^ 990570 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_17274080639688469 : Nat.Prime 17274080639688469 := by
  apply lucas_primality 17274080639688469 (2 : ZMod 17274080639688469)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (75763511577581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (75763511577581, 1)] : List FactorBlock).map factorBlockValue).prod) = 17274080639688469 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_19
      · exact prime_fortyTwoAN_75763511577581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 17274080639688469) ^ 8637040319844234 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 17274080639688469) ^ 5758026879896156 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 17274080639688469) ^ 909162138930972 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 17274080639688469) ^ 228 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_20660407174714891 : Nat.Prime 20660407174714891 := by
  apply lucas_primality 20660407174714891 (2 : ZMod 20660407174714891)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (61, 1), (1026349089653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (61, 1), (1026349089653, 1)] : List FactorBlock).map factorBlockValue).prod) = 20660407174714891 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_5
      · exact prime_fortyTwoAN_11
      · exact prime_fortyTwoAN_61
      · exact prime_fortyTwoAN_1026349089653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 20660407174714891) ^ 10330203587357445 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 20660407174714891) ^ 6886802391571630 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 20660407174714891) ^ 4132081434942978 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 20660407174714891) ^ 1878218834064990 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 20660407174714891) ^ 338695199585490 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 20660407174714891) ^ 20130 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_22145781469408963 : Nat.Prime 22145781469408963 := by
  apply lucas_primality 22145781469408963 (2 : ZMod 22145781469408963)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (89, 1), (163, 1), (254426385761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (89, 1), (163, 1), (254426385761, 1)] : List FactorBlock).map factorBlockValue).prod) = 22145781469408963 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_89
      · exact prime_fortyTwoAN_163
      · exact prime_fortyTwoAN_254426385761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 22145781469408963) ^ 11072890734704481 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 22145781469408963) ^ 7381927156469654 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 22145781469408963) ^ 248829005274258 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 22145781469408963) ^ 135863689996374 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 22145781469408963) ^ 87042 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_23292642764359417 : Nat.Prime 23292642764359417 := by
  apply lucas_primality 23292642764359417 (5 : ZMod 23292642764359417)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (109, 1), (65089, 1), (19542287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (109, 1), (65089, 1), (19542287, 1)] : List FactorBlock).map factorBlockValue).prod) = 23292642764359417 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_7
      · exact prime_fortyTwoAN_109
      · exact prime_fortyTwoAN_65089
      · exact prime_fortyTwoAN_19542287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 23292642764359417) ^ 11646321382179708 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 23292642764359417) ^ 7764214254786472 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 23292642764359417) ^ 3327520394908488 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 23292642764359417) ^ 213693970315224 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 23292642764359417) ^ 357858359544 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 23292642764359417) ^ 1191909768 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_26026907316507379 : Nat.Prime 26026907316507379 := by
  apply lucas_primality 26026907316507379 (2 : ZMod 26026907316507379)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (81463, 1), (5916548189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (81463, 1), (5916548189, 1)] : List FactorBlock).map factorBlockValue).prod) = 26026907316507379 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_81463
      · exact prime_fortyTwoAN_5916548189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 26026907316507379) ^ 13013453658253689 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 26026907316507379) ^ 8675635772169126 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 26026907316507379) ^ 319493602206 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 26026907316507379) ^ 4399002 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_26229186291798697 : Nat.Prime 26229186291798697 := by
  apply lucas_primality 26229186291798697 (10 : ZMod 26229186291798697)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (6766183, 1), (161521313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (6766183, 1), (161521313, 1)] : List FactorBlock).map factorBlockValue).prod) = 26229186291798697 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_6766183
      · exact prime_fortyTwoAN_161521313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 26229186291798697) ^ 13114593145899348 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (10 : ZMod 26229186291798697) ^ 8743062097266232 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (10 : ZMod 26229186291798697) ^ 3876511512 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (10 : ZMod 26229186291798697) ^ 162388392 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_32264833291152793 : Nat.Prime 32264833291152793 := by
  apply lucas_primality 32264833291152793 (5 : ZMod 32264833291152793)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (122215277618003, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (122215277618003, 1)] : List FactorBlock).map factorBlockValue).prod) = 32264833291152793 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_11
      · exact prime_fortyTwoAN_122215277618003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 32264833291152793) ^ 16132416645576396 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 32264833291152793) ^ 10754944430384264 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 32264833291152793) ^ 2933166662832072 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 32264833291152793) ^ 264 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_33774604584521293 : Nat.Prime 33774604584521293 := by
  apply lucas_primality 33774604584521293 (2 : ZMod 33774604584521293)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (233, 1), (1669, 1), (4561, 1), (176317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (233, 1), (1669, 1), (4561, 1), (176317, 1)] : List FactorBlock).map factorBlockValue).prod) = 33774604584521293 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_233
      · exact prime_fortyTwoAN_1669
      · exact prime_fortyTwoAN_4561
      · exact prime_fortyTwoAN_176317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 33774604584521293) ^ 16887302292260646 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 33774604584521293) ^ 11258201528173764 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 33774604584521293) ^ 144955384482924 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 33774604584521293) ^ 20236431746268 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 33774604584521293) ^ 7405087608972 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 33774604584521293) ^ 191556143676 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_68620548412508303 : Nat.Prime 68620548412508303 := by
  apply lucas_primality 68620548412508303 (5 : ZMod 68620548412508303)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (17, 2), (16960095999137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (17, 2), (16960095999137, 1)] : List FactorBlock).map factorBlockValue).prod) = 68620548412508303 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_7
      · exact prime_fortyTwoAN_17
      · exact prime_fortyTwoAN_16960095999137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 68620548412508303) ^ 34310274206254151 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 68620548412508303) ^ 9802935487501186 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 68620548412508303) ^ 4036502847794606 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 68620548412508303) ^ 4046 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_112248404256013009 : Nat.Prime 112248404256013009 := by
  apply lucas_primality 112248404256013009 (7 : ZMod 112248404256013009)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (4363, 1), (535986344717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (4363, 1), (535986344717, 1)] : List FactorBlock).map factorBlockValue).prod) = 112248404256013009 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_4363
      · exact prime_fortyTwoAN_535986344717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 112248404256013009) ^ 56124202128006504 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (7 : ZMod 112248404256013009) ^ 37416134752004336 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (7 : ZMod 112248404256013009) ^ 25727344546416 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (7 : ZMod 112248404256013009) ^ 209424 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_116559782766332771 : Nat.Prime 116559782766332771 := by
  apply lucas_primality 116559782766332771 (2 : ZMod 116559782766332771)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11655978276633277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11655978276633277, 1)] : List FactorBlock).map factorBlockValue).prod) = 116559782766332771 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_5
      · exact prime_fortyTwoAN_11655978276633277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 116559782766332771) ^ 58279891383166385 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 116559782766332771) ^ 23311956553266554 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 116559782766332771) ^ 10 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_119585448875776439 : Nat.Prime 119585448875776439 := by
  apply lucas_primality 119585448875776439 (19 : ZMod 119585448875776439)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (563, 1), (391451, 1), (9355447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (563, 1), (391451, 1), (9355447, 1)] : List FactorBlock).map factorBlockValue).prod) = 119585448875776439 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_29
      · exact prime_fortyTwoAN_563
      · exact prime_fortyTwoAN_391451
      · exact prime_fortyTwoAN_9355447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 119585448875776439) ^ 59792724437888219 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (19 : ZMod 119585448875776439) ^ 4123636168130222 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (19 : ZMod 119585448875776439) ^ 212407546848626 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (19 : ZMod 119585448875776439) ^ 305492766338 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (19 : ZMod 119585448875776439) ^ 12782440954 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_158361893331124207 : Nat.Prime 158361893331124207 := by
  apply lucas_primality 158361893331124207 (5 : ZMod 158361893331124207)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (97, 1), (10049639, 1), (27075547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (97, 1), (10049639, 1), (27075547, 1)] : List FactorBlock).map factorBlockValue).prod) = 158361893331124207 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_97
      · exact prime_fortyTwoAN_10049639
      · exact prime_fortyTwoAN_27075547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 158361893331124207) ^ 79180946665562103 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 158361893331124207) ^ 52787297777041402 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 158361893331124207) ^ 1632596838465198 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 158361893331124207) ^ 15757968354 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 158361893331124207) ^ 5848889898 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_170959857503138651 : Nat.Prime 170959857503138651 := by
  apply lucas_primality 170959857503138651 (10 : ZMod 170959857503138651)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (67, 1), (318281, 1), (160338799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (67, 1), (318281, 1), (160338799, 1)] : List FactorBlock).map factorBlockValue).prod) = 170959857503138651 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_5
      · exact prime_fortyTwoAN_67
      · exact prime_fortyTwoAN_318281
      · exact prime_fortyTwoAN_160338799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 170959857503138651) ^ 85479928751569325 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (10 : ZMod 170959857503138651) ^ 34191971500627730 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (10 : ZMod 170959857503138651) ^ 2551639664225950 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (10 : ZMod 170959857503138651) ^ 537134976650 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (10 : ZMod 170959857503138651) ^ 1066241350 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_180018837229260329 : Nat.Prime 180018837229260329 := by
  apply lucas_primality 180018837229260329 (3 : ZMod 180018837229260329)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (79, 1), (21910764024983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (79, 1), (21910764024983, 1)] : List FactorBlock).map factorBlockValue).prod) = 180018837229260329 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_13
      · exact prime_fortyTwoAN_79
      · exact prime_fortyTwoAN_21910764024983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 180018837229260329) ^ 90009418614630164 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 180018837229260329) ^ 13847602863789256 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 180018837229260329) ^ 2278719458598232 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 180018837229260329) ^ 8216 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_312118717700524549 : Nat.Prime 312118717700524549 := by
  apply lucas_primality 312118717700524549 (6 : ZMod 312118717700524549)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (12588833, 1), (187828033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (12588833, 1), (187828033, 1)] : List FactorBlock).map factorBlockValue).prod) = 312118717700524549 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_11
      · exact prime_fortyTwoAN_12588833
      · exact prime_fortyTwoAN_187828033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 312118717700524549) ^ 156059358850262274 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (6 : ZMod 312118717700524549) ^ 104039572566841516 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (6 : ZMod 312118717700524549) ^ 28374428881865868 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (6 : ZMod 312118717700524549) ^ 24793300356 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (6 : ZMod 312118717700524549) ^ 1661725956 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_383958901408250471 : Nat.Prime 383958901408250471 := by
  apply lucas_primality 383958901408250471 (7 : ZMod 383958901408250471)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (31, 1), (18431951, 1), (67197287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (31, 1), (18431951, 1), (67197287, 1)] : List FactorBlock).map factorBlockValue).prod) = 383958901408250471 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_5
      · exact prime_fortyTwoAN_31
      · exact prime_fortyTwoAN_18431951
      · exact prime_fortyTwoAN_67197287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 383958901408250471) ^ 191979450704125235 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (7 : ZMod 383958901408250471) ^ 76791780281650094 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (7 : ZMod 383958901408250471) ^ 12385771013169370 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (7 : ZMod 383958901408250471) ^ 20831158970 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (7 : ZMod 383958901408250471) ^ 5713904810 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_445632882740015849 : Nat.Prime 445632882740015849 := by
  apply lucas_primality 445632882740015849 (3 : ZMod 445632882740015849)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (23, 1), (6043, 1), (400780711729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (23, 1), (6043, 1), (400780711729, 1)] : List FactorBlock).map factorBlockValue).prod) = 445632882740015849 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_23
      · exact prime_fortyTwoAN_6043
      · exact prime_fortyTwoAN_400780711729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 445632882740015849) ^ 222816441370007924 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 445632882740015849) ^ 19375342727826776 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 445632882740015849) ^ 73743650958136 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 445632882740015849) ^ 1111912 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_483498887150858771 : Nat.Prime 483498887150858771 := by
  apply lucas_primality 483498887150858771 (2 : ZMod 483498887150858771)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (29, 1), (1667237541899513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (29, 1), (1667237541899513, 1)] : List FactorBlock).map factorBlockValue).prod) = 483498887150858771 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_5
      · exact prime_fortyTwoAN_29
      · exact prime_fortyTwoAN_1667237541899513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 483498887150858771) ^ 241749443575429385 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 96699777430171754 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 16672375418995130 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 290 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_531381464747383571 : Nat.Prime 531381464747383571 := by
  apply lucas_primality 531381464747383571 (2 : ZMod 531381464747383571)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (19559, 1), (2716813051523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (19559, 1), (2716813051523, 1)] : List FactorBlock).map factorBlockValue).prod) = 531381464747383571 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_5
      · exact prime_fortyTwoAN_19559
      · exact prime_fortyTwoAN_2716813051523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 531381464747383571) ^ 265690732373691785 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 531381464747383571) ^ 106276292949476714 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 531381464747383571) ^ 27168130515230 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 531381464747383571) ^ 195590 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_563585608037072707 : Nat.Prime 563585608037072707 := by
  apply lucas_primality 563585608037072707 (3 : ZMod 563585608037072707)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (61717, 1), (1521962095903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (61717, 1), (1521962095903, 1)] : List FactorBlock).map factorBlockValue).prod) = 563585608037072707 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_61717
      · exact prime_fortyTwoAN_1521962095903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 563585608037072707) ^ 281792804018536353 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 187861869345690902 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 9131772575418 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 370302 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_860438700574923961 : Nat.Prime 860438700574923961 := by
  apply lucas_primality 860438700574923961 (11 : ZMod 860438700574923961)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (5, 1), (7, 1), (43, 1), (89069, 1), (29716873, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (5, 1), (7, 1), (43, 1), (89069, 1), (29716873, 1)] : List FactorBlock).map factorBlockValue).prod) = 860438700574923961 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_5
      · exact prime_fortyTwoAN_7
      · exact prime_fortyTwoAN_43
      · exact prime_fortyTwoAN_89069
      · exact prime_fortyTwoAN_29716873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 860438700574923961) ^ 430219350287461980 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (11 : ZMod 860438700574923961) ^ 286812900191641320 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (11 : ZMod 860438700574923961) ^ 172087740114984792 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (11 : ZMod 860438700574923961) ^ 122919814367846280 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (11 : ZMod 860438700574923961) ^ 20010202338951720 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (11 : ZMod 860438700574923961) ^ 9660361074840 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (11 : ZMod 860438700574923961) ^ 28954550520 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_1025759145018831907 : Nat.Prime 1025759145018831907 := by
  apply lucas_primality 1025759145018831907 (2 : ZMod 1025759145018831907)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (170959857503138651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (170959857503138651, 1)] : List FactorBlock).map factorBlockValue).prod) = 1025759145018831907 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_170959857503138651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1025759145018831907) ^ 512879572509415953 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 1025759145018831907) ^ 341919715006277302 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 1025759145018831907) ^ 6 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_1570470015063981253 : Nat.Prime 1570470015063981253 := by
  apply lucas_primality 1570470015063981253 (5 : ZMod 1570470015063981253)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 2), (89, 1), (1151, 1), (3301, 1), (2290081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 2), (89, 1), (1151, 1), (3301, 1), (2290081, 1)] : List FactorBlock).map factorBlockValue).prod) = 1570470015063981253 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_13
      · exact prime_fortyTwoAN_89
      · exact prime_fortyTwoAN_1151
      · exact prime_fortyTwoAN_3301
      · exact prime_fortyTwoAN_2290081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1570470015063981253) ^ 785235007531990626 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 1570470015063981253) ^ 523490005021327084 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 1570470015063981253) ^ 120805385774152404 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 1570470015063981253) ^ 17645730506336868 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 1570470015063981253) ^ 1364439630811452 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 1570470015063981253) ^ 475755836129652 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 1570470015063981253) ^ 685770509892 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_1862345396350691977 : Nat.Prime 1862345396350691977 := by
  apply lucas_primality 1862345396350691977 (10 : ZMod 1862345396350691977)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (17, 1), (157, 1), (29073707324071, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (17, 1), (157, 1), (29073707324071, 1)] : List FactorBlock).map factorBlockValue).prod) = 1862345396350691977 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_17
      · exact prime_fortyTwoAN_157
      · exact prime_fortyTwoAN_29073707324071
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 1862345396350691977) ^ 931172698175345988 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (10 : ZMod 1862345396350691977) ^ 620781798783563992 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (10 : ZMod 1862345396350691977) ^ 109549729197099528 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (10 : ZMod 1862345396350691977) ^ 11862072588220968 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (10 : ZMod 1862345396350691977) ^ 64056 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_3357640771913012023 : Nat.Prime 3357640771913012023 := by
  apply lucas_primality 3357640771913012023 (5 : ZMod 3357640771913012023)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (19, 1), (439, 1), (20549, 1), (1088310731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (19, 1), (439, 1), (20549, 1), (1088310731, 1)] : List FactorBlock).map factorBlockValue).prod) = 3357640771913012023 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_19
      · exact prime_fortyTwoAN_439
      · exact prime_fortyTwoAN_20549
      · exact prime_fortyTwoAN_1088310731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 3357640771913012023) ^ 1678820385956506011 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 3357640771913012023) ^ 1119213590637670674 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 3357640771913012023) ^ 176717935363842738 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 3357640771913012023) ^ 7648384446271098 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 3357640771913012023) ^ 163396796530878 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 3357640771913012023) ^ 3085185762 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_4646135993926002193 : Nat.Prime 4646135993926002193 := by
  apply lucas_primality 4646135993926002193 (10 : ZMod 4646135993926002193)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (32264833291152793, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (32264833291152793, 1)] : List FactorBlock).map factorBlockValue).prod) = 4646135993926002193 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_32264833291152793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 4646135993926002193) ^ 2323067996963001096 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (10 : ZMod 4646135993926002193) ^ 1548711997975334064 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (10 : ZMod 4646135993926002193) ^ 144 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_6373336764968102861 : Nat.Prime 6373336764968102861 := by
  apply lucas_primality 6373336764968102861 (2 : ZMod 6373336764968102861)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (25717, 1), (1770184470797, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (25717, 1), (1770184470797, 1)] : List FactorBlock).map factorBlockValue).prod) = 6373336764968102861 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_5
      · exact prime_fortyTwoAN_7
      · exact prime_fortyTwoAN_25717
      · exact prime_fortyTwoAN_1770184470797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6373336764968102861) ^ 3186668382484051430 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 6373336764968102861) ^ 1274667352993620572 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 6373336764968102861) ^ 910476680709728980 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 6373336764968102861) ^ 247825825911580 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 6373336764968102861) ^ 3600380 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_8081426670915240593 : Nat.Prime 8081426670915240593 := by
  apply lucas_primality 8081426670915240593 (3 : ZMod 8081426670915240593)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (439, 1), (853, 1), (1348821570211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (439, 1), (853, 1), (1348821570211, 1)] : List FactorBlock).map factorBlockValue).prod) = 8081426670915240593 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_439
      · exact prime_fortyTwoAN_853
      · exact prime_fortyTwoAN_1348821570211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 8081426670915240593) ^ 4040713335457620296 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 8081426670915240593) ^ 18408716790239728 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 8081426670915240593) ^ 9474122709162064 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 8081426670915240593) ^ 5991472 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_11891227458126031349 : Nat.Prime 11891227458126031349 := by
  apply lucas_primality 11891227458126031349 (2 : ZMod 11891227458126031349)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (137, 1), (25457, 1), (852391097893, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (137, 1), (25457, 1), (852391097893, 1)] : List FactorBlock).map factorBlockValue).prod) = 11891227458126031349 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_137
      · exact prime_fortyTwoAN_25457
      · exact prime_fortyTwoAN_852391097893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 11891227458126031349) ^ 5945613729063015674 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 11891227458126031349) ^ 86797280716248404 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 11891227458126031349) ^ 467110321645364 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 11891227458126031349) ^ 13950436 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_14143091156502206219 : Nat.Prime 14143091156502206219 := by
  apply lucas_primality 14143091156502206219 (2 : ZMod 14143091156502206219)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (419, 1), (16877197084131511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (419, 1), (16877197084131511, 1)] : List FactorBlock).map factorBlockValue).prod) = 14143091156502206219 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_419
      · exact prime_fortyTwoAN_16877197084131511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 14143091156502206219) ^ 7071545578251103109 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 14143091156502206219) ^ 33754394168263022 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 14143091156502206219) ^ 838 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_26275232482769198029 : Nat.Prime 26275232482769198029 := by
  apply lucas_primality 26275232482769198029 (2 : ZMod 26275232482769198029)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (156859133, 1), (734686247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (156859133, 1), (734686247, 1)] : List FactorBlock).map factorBlockValue).prod) = 26275232482769198029 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_19
      · exact prime_fortyTwoAN_156859133
      · exact prime_fortyTwoAN_734686247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 26275232482769198029) ^ 13137616241384599014 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 26275232482769198029) ^ 8758410827589732676 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 26275232482769198029) ^ 1382906972777326212 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 26275232482769198029) ^ 167508464316 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 26275232482769198029) ^ 35763882324 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_45151642448085877889 : Nat.Prime 45151642448085877889 := by
  apply lucas_primality 45151642448085877889 (3 : ZMod 45151642448085877889)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (29, 1), (31, 1), (67, 1), (79, 1), (109, 1), (680104267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (29, 1), (31, 1), (67, 1), (79, 1), (109, 1), (680104267, 1)] : List FactorBlock).map factorBlockValue).prod) = 45151642448085877889 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_29
      · exact prime_fortyTwoAN_31
      · exact prime_fortyTwoAN_67
      · exact prime_fortyTwoAN_79
      · exact prime_fortyTwoAN_109
      · exact prime_fortyTwoAN_680104267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 45151642448085877889) ^ 22575821224042938944 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 45151642448085877889) ^ 1556953187865030272 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 45151642448085877889) ^ 1456504595099544448 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 45151642448085877889) ^ 673905111165460864 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 45151642448085877889) ^ 571539777823871872 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 45151642448085877889) ^ 414235251817301632 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 45151642448085877889) ^ 66389294464 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_48128351335921711693 : Nat.Prime 48128351335921711693 := by
  apply lucas_primality 48128351335921711693 (2 : ZMod 48128351335921711693)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (445632882740015849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (445632882740015849, 1)] : List FactorBlock).map factorBlockValue).prod) = 48128351335921711693 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_445632882740015849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 48128351335921711693) ^ 24064175667960855846 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 48128351335921711693) ^ 16042783778640570564 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 48128351335921711693) ^ 108 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_93639150386551147643 : Nat.Prime 93639150386551147643 := by
  apply lucas_primality 93639150386551147643 (2 : ZMod 93639150386551147643)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (139, 1), (413869, 1), (73987284121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (139, 1), (413869, 1), (73987284121, 1)] : List FactorBlock).map factorBlockValue).prod) = 93639150386551147643 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_11
      · exact prime_fortyTwoAN_139
      · exact prime_fortyTwoAN_413869
      · exact prime_fortyTwoAN_73987284121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 93639150386551147643) ^ 46819575193275573821 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 93639150386551147643) ^ 8512650035141013422 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 93639150386551147643) ^ 673662952421231278 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 93639150386551147643) ^ 226253114842018 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 93639150386551147643) ^ 1265611402 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_173260613935464457133 : Nat.Prime 173260613935464457133 := by
  apply lucas_primality 173260613935464457133 (2 : ZMod 173260613935464457133)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (37, 1), (359, 1), (3260946584647001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (37, 1), (359, 1), (3260946584647001, 1)] : List FactorBlock).map factorBlockValue).prod) = 173260613935464457133 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_37
      · exact prime_fortyTwoAN_359
      · exact prime_fortyTwoAN_3260946584647001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 173260613935464457133) ^ 86630306967732228566 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 173260613935464457133) ^ 4682719295553093436 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 173260613935464457133) ^ 482620094527756148 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 173260613935464457133) ^ 53132 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_173669944451063813153 : Nat.Prime 173669944451063813153 := by
  apply lucas_primality 173669944451063813153 (3 : ZMod 173669944451063813153)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (233, 1), (23292642764359417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (233, 1), (23292642764359417, 1)] : List FactorBlock).map factorBlockValue).prod) = 173669944451063813153 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_233
      · exact prime_fortyTwoAN_23292642764359417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 173669944451063813153) ^ 86834972225531906576 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 173669944451063813153) ^ 745364568459501344 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 173669944451063813153) ^ 7456 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_198003276191030887067 : Nat.Prime 198003276191030887067 := by
  apply lucas_primality 198003276191030887067 (2 : ZMod 198003276191030887067)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (14143091156502206219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (14143091156502206219, 1)] : List FactorBlock).map factorBlockValue).prod) = 198003276191030887067 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_7
      · exact prime_fortyTwoAN_14143091156502206219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 198003276191030887067) ^ 99001638095515443533 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 198003276191030887067) ^ 28286182313004412438 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 198003276191030887067) ^ 14 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_391571347175524180649 : Nat.Prime 391571347175524180649 := by
  apply lucas_primality 391571347175524180649 (3 : ZMod 391571347175524180649)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (107, 1), (4144969, 1), (110361057607, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (107, 1), (4144969, 1), (110361057607, 1)] : List FactorBlock).map factorBlockValue).prod) = 391571347175524180649 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_107
      · exact prime_fortyTwoAN_4144969
      · exact prime_fortyTwoAN_110361057607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 391571347175524180649) ^ 195785673587762090324 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 391571347175524180649) ^ 3659545300705833464 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 391571347175524180649) ^ 94469065311592 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 391571347175524180649) ^ 3548093464 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_429449525106920937499 : Nat.Prime 429449525106920937499 := by
  apply lucas_primality 429449525106920937499 (2 : ZMod 429449525106920937499)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (199, 1), (5449, 1), (8089, 1), (741828427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (199, 1), (5449, 1), (8089, 1), (741828427, 1)] : List FactorBlock).map factorBlockValue).prod) = 429449525106920937499 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_11
      · exact prime_fortyTwoAN_199
      · exact prime_fortyTwoAN_5449
      · exact prime_fortyTwoAN_8089
      · exact prime_fortyTwoAN_741828427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 429449525106920937499) ^ 214724762553460468749 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 429449525106920937499) ^ 143149841702306979166 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 429449525106920937499) ^ 39040865918810994318 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 429449525106920937499) ^ 2158037814607642902 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 429449525106920937499) ^ 78812539017603402 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 429449525106920937499) ^ 53090558178627882 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 429449525106920937499) ^ 578906805774 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_923168105727978526657 : Nat.Prime 923168105727978526657 := by
  apply lucas_primality 923168105727978526657 (7 : ZMod 923168105727978526657)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (1999, 1), (2405286251792507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (1999, 1), (2405286251792507, 1)] : List FactorBlock).map factorBlockValue).prod) = 923168105727978526657 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_1999
      · exact prime_fortyTwoAN_2405286251792507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 923168105727978526657) ^ 461584052863989263328 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (7 : ZMod 923168105727978526657) ^ 307722701909326175552 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (7 : ZMod 923168105727978526657) ^ 461814960344161344 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (7 : ZMod 923168105727978526657) ^ 383808 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_927515741733830445223 : Nat.Prime 927515741733830445223 := by
  apply lucas_primality 927515741733830445223 (3 : ZMod 927515741733830445223)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (11891227458126031349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (11891227458126031349, 1)] : List FactorBlock).map factorBlockValue).prod) = 927515741733830445223 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_13
      · exact prime_fortyTwoAN_11891227458126031349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 927515741733830445223) ^ 463757870866915222611 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 927515741733830445223) ^ 309171913911276815074 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 927515741733830445223) ^ 71347364748756188094 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 927515741733830445223) ^ 78 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_1413322177816799584771 : Nat.Prime 1413322177816799584771 := by
  apply lucas_primality 1413322177816799584771 (2 : ZMod 1413322177816799584771)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (16411, 1), (2870680595975869, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (16411, 1), (2870680595975869, 1)] : List FactorBlock).map factorBlockValue).prod) = 1413322177816799584771 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_5
      · exact prime_fortyTwoAN_16411
      · exact prime_fortyTwoAN_2870680595975869
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1413322177816799584771) ^ 706661088908399792385 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 1413322177816799584771) ^ 471107392605599861590 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 1413322177816799584771) ^ 282664435563359916954 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 1413322177816799584771) ^ 86120417879276070 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 1413322177816799584771) ^ 492330 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_1593092214812622769463 : Nat.Prime 1593092214812622769463 := by
  apply lucas_primality 1593092214812622769463 (5 : ZMod 1593092214812622769463)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (173, 1), (281, 1), (9431, 1), (80149, 1), (3096739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (173, 1), (281, 1), (9431, 1), (80149, 1), (3096739, 1)] : List FactorBlock).map factorBlockValue).prod) = 1593092214812622769463 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_7
      · exact prime_fortyTwoAN_173
      · exact prime_fortyTwoAN_281
      · exact prime_fortyTwoAN_9431
      · exact prime_fortyTwoAN_80149
      · exact prime_fortyTwoAN_3096739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1593092214812622769463) ^ 796546107406311384731 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 1593092214812622769463) ^ 227584602116088967066 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 1593092214812622769463) ^ 9208625519148108494 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 1593092214812622769463) ^ 5669367312500436902 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 1593092214812622769463) ^ 168920815906332602 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 1593092214812622769463) ^ 19876632457206238 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 1593092214812622769463) ^ 514441874117458 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_1970979474127129694209 : Nat.Prime 1970979474127129694209 := by
  apply lucas_primality 1970979474127129694209 (17 : ZMod 1970979474127129694209)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 12), (3, 2), (419, 1), (22013, 1), (5796774251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 12), (3, 2), (419, 1), (22013, 1), (5796774251, 1)] : List FactorBlock).map factorBlockValue).prod) = 1970979474127129694209 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_419
      · exact prime_fortyTwoAN_22013
      · exact prime_fortyTwoAN_5796774251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 1970979474127129694209) ^ 985489737063564847104 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (17 : ZMod 1970979474127129694209) ^ 656993158042376564736 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (17 : ZMod 1970979474127129694209) ^ 4704008291472863232 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (17 : ZMod 1970979474127129694209) ^ 89537067829334016 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (17 : ZMod 1970979474127129694209) ^ 340013150208 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_2291539082278737626663 : Nat.Prime 2291539082278737626663 := by
  apply lucas_primality 2291539082278737626663 (10 : ZMod 2291539082278737626663)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (107, 1), (563585608037072707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (107, 1), (563585608037072707, 1)] : List FactorBlock).map factorBlockValue).prod) = 2291539082278737626663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_19
      · exact prime_fortyTwoAN_107
      · exact prime_fortyTwoAN_563585608037072707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 2291539082278737626663) ^ 1145769541139368813331 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 120607320119933559298 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 21416253105408762866 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 4066 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_3376719396603664660873 : Nat.Prime 3376719396603664660873 := by
  apply lucas_primality 3376719396603664660873 (15 : ZMod 3376719396603664660873)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 5), (2633, 1), (659702079143411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 5), (2633, 1), (659702079143411, 1)] : List FactorBlock).map factorBlockValue).prod) = 3376719396603664660873 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_2633
      · exact prime_fortyTwoAN_659702079143411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (15 : ZMod 3376719396603664660873) ^ 1688359698301832330436 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (15 : ZMod 3376719396603664660873) ^ 1125573132201221553624 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (15 : ZMod 3376719396603664660873) ^ 1282460841854790984 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (15 : ZMod 3376719396603664660873) ^ 5118552 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_4712696973609818164547 : Nat.Prime 4712696973609818164547 := by
  apply lucas_primality 4712696973609818164547 (2 : ZMod 4712696973609818164547)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (29, 1), (431, 1), (3532679, 1), (3139143389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (29, 1), (431, 1), (3532679, 1), (3139143389, 1)] : List FactorBlock).map factorBlockValue).prod) = 4712696973609818164547 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_17
      · exact prime_fortyTwoAN_29
      · exact prime_fortyTwoAN_431
      · exact prime_fortyTwoAN_3532679
      · exact prime_fortyTwoAN_3139143389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4712696973609818164547) ^ 2356348486804909082273 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 4712696973609818164547) ^ 277217469035871656738 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 4712696973609818164547) ^ 162506792193442005674 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 4712696973609818164547) ^ 10934331725312803166 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 4712696973609818164547) ^ 1334029209449774 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 4712696973609818164547) ^ 1501268463914 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_7522557978948218149093 : Nat.Prime 7522557978948218149093 := by
  apply lucas_primality 7522557978948218149093 (2 : ZMod 7522557978948218149093)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 2), (19, 1), (79, 1), (1445126159443919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 2), (19, 1), (79, 1), (1445126159443919, 1)] : List FactorBlock).map factorBlockValue).prod) = 7522557978948218149093 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_17
      · exact prime_fortyTwoAN_19
      · exact prime_fortyTwoAN_79
      · exact prime_fortyTwoAN_1445126159443919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7522557978948218149093) ^ 3761278989474109074546 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 7522557978948218149093) ^ 2507519326316072716364 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 7522557978948218149093) ^ 442503410526365773476 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 7522557978948218149093) ^ 395924104155169376268 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 7522557978948218149093) ^ 95222252898078710748 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 7522557978948218149093) ^ 5205468 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_11178509871247551844717 : Nat.Prime 11178509871247551844717 := by
  apply lucas_primality 11178509871247551844717 (2 : ZMod 11178509871247551844717)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (117497, 1), (7928223608012369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (117497, 1), (7928223608012369, 1)] : List FactorBlock).map factorBlockValue).prod) = 11178509871247551844717 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_117497
      · exact prime_fortyTwoAN_7928223608012369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 11178509871247551844717) ^ 5589254935623775922358 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 11178509871247551844717) ^ 3726169957082517281572 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 11178509871247551844717) ^ 95138683296148428 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 11178509871247551844717) ^ 1409964 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_11249345925914014905457 : Nat.Prime 11249345925914014905457 := by
  apply lucas_primality 11249345925914014905457 (5 : ZMod 11249345925914014905457)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (29, 1), (8081426670915240593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (29, 1), (8081426670915240593, 1)] : List FactorBlock).map factorBlockValue).prod) = 11249345925914014905457 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_29
      · exact prime_fortyTwoAN_8081426670915240593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 11249345925914014905457) ^ 5624672962957007452728 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 11249345925914014905457) ^ 3749781975304671635152 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 11249345925914014905457) ^ 387908480203931548464 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 11249345925914014905457) ^ 1392 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_11380112522338097407091 : Nat.Prime 11380112522338097407091 := by
  apply lucas_primality 11380112522338097407091 (2 : ZMod 11380112522338097407091)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (67, 1), (19379, 1), (311677, 1), (216317813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (67, 1), (19379, 1), (311677, 1), (216317813, 1)] : List FactorBlock).map factorBlockValue).prod) = 11380112522338097407091 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_5
      · exact prime_fortyTwoAN_13
      · exact prime_fortyTwoAN_67
      · exact prime_fortyTwoAN_19379
      · exact prime_fortyTwoAN_311677
      · exact prime_fortyTwoAN_216317813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 11380112522338097407091) ^ 5690056261169048703545 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 11380112522338097407091) ^ 2276022504467619481418 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 11380112522338097407091) ^ 875393270949084415930 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 11380112522338097407091) ^ 169852425706538767270 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 11380112522338097407091) ^ 587239409790912710 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 11380112522338097407091) ^ 36512519442686170 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 11380112522338097407091) ^ 52608300557930 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_11403597493703654977229 : Nat.Prime 11403597493703654977229 := by
  apply lucas_primality 11403597493703654977229 (2 : ZMod 11403597493703654977229)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (461, 1), (28537, 1), (216706854253751, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (461, 1), (28537, 1), (216706854253751, 1)] : List FactorBlock).map factorBlockValue).prod) = 11403597493703654977229 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_461
      · exact prime_fortyTwoAN_28537
      · exact prime_fortyTwoAN_216706854253751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 11403597493703654977229) ^ 5701798746851827488614 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 11403597493703654977229) ^ 24736653999357169148 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 11403597493703654977229) ^ 399607439243916844 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 11403597493703654977229) ^ 52622228 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_32457694465787711188511 : Nat.Prime 32457694465787711188511 := by
  apply lucas_primality 32457694465787711188511 (7 : ZMod 32457694465787711188511)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (6475879, 1), (38554545693913, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (6475879, 1), (38554545693913, 1)] : List FactorBlock).map factorBlockValue).prod) = 32457694465787711188511 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_5
      · exact prime_fortyTwoAN_13
      · exact prime_fortyTwoAN_6475879
      · exact prime_fortyTwoAN_38554545693913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 32457694465787711188511) ^ 16228847232893855594255 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (7 : ZMod 32457694465787711188511) ^ 6491538893157542237702 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (7 : ZMod 32457694465787711188511) ^ 2496745728137516245270 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (7 : ZMod 32457694465787711188511) ^ 5012090940208690 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (7 : ZMod 32457694465787711188511) ^ 841864270 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_39856778780212350721703 : Nat.Prime 39856778780212350721703 := by
  apply lucas_primality 39856778780212350721703 (5 : ZMod 39856778780212350721703)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (53, 1), (275558879, 1), (194932333439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (53, 1), (275558879, 1), (194932333439, 1)] : List FactorBlock).map factorBlockValue).prod) = 39856778780212350721703 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_7
      · exact prime_fortyTwoAN_53
      · exact prime_fortyTwoAN_275558879
      · exact prime_fortyTwoAN_194932333439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 39856778780212350721703) ^ 19928389390106175360851 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 39856778780212350721703) ^ 5693825540030335817386 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 39856778780212350721703) ^ 752014693966270768334 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 39856778780212350721703) ^ 144639791411738 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 39856778780212350721703) ^ 204464688218 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_64915388931575422377023 : Nat.Prime 64915388931575422377023 := by
  apply lucas_primality 64915388931575422377023 (5 : ZMod 64915388931575422377023)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (32457694465787711188511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (32457694465787711188511, 1)] : List FactorBlock).map factorBlockValue).prod) = 64915388931575422377023 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_32457694465787711188511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 64915388931575422377023) ^ 32457694465787711188511 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 64915388931575422377023) ^ 2 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_162940727733174517744327 : Nat.Prime 162940727733174517744327 := by
  apply lucas_primality 162940727733174517744327 (5 : ZMod 162940727733174517744327)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (4261, 1), (6373336764968102861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (4261, 1), (6373336764968102861, 1)] : List FactorBlock).map factorBlockValue).prod) = 162940727733174517744327 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_4261
      · exact prime_fortyTwoAN_6373336764968102861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 162940727733174517744327) ^ 81470363866587258872163 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 162940727733174517744327) ^ 54313575911058172581442 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 162940727733174517744327) ^ 38240020589808617166 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 162940727733174517744327) ^ 25566 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_547267357326645600117677 : Nat.Prime 547267357326645600117677 := by
  apply lucas_primality 547267357326645600117677 (2 : ZMod 547267357326645600117677)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (41, 1), (956242277, 1), (498528184081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (41, 1), (956242277, 1), (498528184081, 1)] : List FactorBlock).map factorBlockValue).prod) = 547267357326645600117677 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_7
      · exact prime_fortyTwoAN_41
      · exact prime_fortyTwoAN_956242277
      · exact prime_fortyTwoAN_498528184081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 547267357326645600117677) ^ 273633678663322800058838 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 547267357326645600117677) ^ 78181051046663657159668 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 547267357326645600117677) ^ 13347984325040136588236 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 547267357326645600117677) ^ 572310355324988 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 547267357326645600117677) ^ 1097766133996 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_567565941984255386287001 : Nat.Prime 567565941984255386287001 := by
  apply lucas_primality 567565941984255386287001 (3 : ZMod 567565941984255386287001)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 3), (41, 1), (4229, 1), (3273367641455083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 3), (41, 1), (4229, 1), (3273367641455083, 1)] : List FactorBlock).map factorBlockValue).prod) = 567565941984255386287001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_5
      · exact prime_fortyTwoAN_41
      · exact prime_fortyTwoAN_4229
      · exact prime_fortyTwoAN_3273367641455083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 567565941984255386287001) ^ 283782970992127693143500 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 567565941984255386287001) ^ 113513188396851077257400 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 567565941984255386287001) ^ 13843071755713546007000 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 567565941984255386287001) ^ 134208073299658403000 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 567565941984255386287001) ^ 173389000 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_1135131883968510772574003 : Nat.Prime 1135131883968510772574003 := by
  apply lucas_primality 1135131883968510772574003 (2 : ZMod 1135131883968510772574003)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (567565941984255386287001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (567565941984255386287001, 1)] : List FactorBlock).map factorBlockValue).prod) = 1135131883968510772574003 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_567565941984255386287001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 1135131883968510772574003) ^ 567565941984255386287001 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (2 : ZMod 1135131883968510772574003) ^ 2 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_1328354220922889575866809 : Nat.Prime 1328354220922889575866809 := by
  apply lucas_primality 1328354220922889575866809 (6 : ZMod 1328354220922889575866809)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (23, 1), (379, 1), (6474341, 1), (420303742769, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (23, 1), (379, 1), (6474341, 1), (420303742769, 1)] : List FactorBlock).map factorBlockValue).prod) = 1328354220922889575866809 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_7
      · exact prime_fortyTwoAN_23
      · exact prime_fortyTwoAN_379
      · exact prime_fortyTwoAN_6474341
      · exact prime_fortyTwoAN_420303742769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1328354220922889575866809) ^ 664177110461444787933404 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (6 : ZMod 1328354220922889575866809) ^ 189764888703269939409544 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (6 : ZMod 1328354220922889575866809) ^ 57754531344473459820296 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (6 : ZMod 1328354220922889575866809) ^ 3504892403490473814952 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (6 : ZMod 1328354220922889575866809) ^ 205172112640172888 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (6 : ZMod 1328354220922889575866809) ^ 3160462507832 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_3491436445810612799569483 : Nat.Prime 3491436445810612799569483 := by
  apply lucas_primality 3491436445810612799569483 (5 : ZMod 3491436445810612799569483)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (47717, 1), (436081, 1), (1634609, 1), (2443997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (47717, 1), (436081, 1), (1634609, 1), (2443997, 1)] : List FactorBlock).map factorBlockValue).prod) = 3491436445810612799569483 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_7
      · exact prime_fortyTwoAN_47717
      · exact prime_fortyTwoAN_436081
      · exact prime_fortyTwoAN_1634609
      · exact prime_fortyTwoAN_2443997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 3491436445810612799569483) ^ 1745718222905306399784741 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 3491436445810612799569483) ^ 1163812148603537599856494 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 3491436445810612799569483) ^ 498776635115801828509926 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 3491436445810612799569483) ^ 73169655380904348546 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 3491436445810612799569483) ^ 8006394329976799722 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 3491436445810612799569483) ^ 2135945933131784298 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 3491436445810612799569483) ^ 1428576404067031506 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_5360018256942847067732857 : Nat.Prime 5360018256942847067732857 := by
  apply lucas_primality 5360018256942847067732857 (5 : ZMod 5360018256942847067732857)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (239, 1), (4519, 1), (15661, 1), (13203689273969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (239, 1), (4519, 1), (15661, 1), (13203689273969, 1)] : List FactorBlock).map factorBlockValue).prod) = 5360018256942847067732857 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_239
      · exact prime_fortyTwoAN_4519
      · exact prime_fortyTwoAN_15661
      · exact prime_fortyTwoAN_13203689273969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 5360018256942847067732857) ^ 2680009128471423533866428 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 5360018256942847067732857) ^ 1786672752314282355910952 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 5360018256942847067732857) ^ 22426854631560029572104 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 5360018256942847067732857) ^ 1186107160199789127624 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 5360018256942847067732857) ^ 342252618411522065496 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (5 : ZMod 5360018256942847067732857) ^ 405948530424 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_9858091946062842016175737 : Nat.Prime 9858091946062842016175737 := by
  apply lucas_primality 9858091946062842016175737 (10 : ZMod 9858091946062842016175737)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (4703, 1), (215497, 1), (135096519595393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (4703, 1), (215497, 1), (135096519595393, 1)] : List FactorBlock).map factorBlockValue).prod) = 9858091946062842016175737 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_4703
      · exact prime_fortyTwoAN_215497
      · exact prime_fortyTwoAN_135096519595393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 9858091946062842016175737) ^ 4929045973031421008087868 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (10 : ZMod 9858091946062842016175737) ^ 3286030648687614005391912 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (10 : ZMod 9858091946062842016175737) ^ 2096128417193885183112 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (10 : ZMod 9858091946062842016175737) ^ 45745843079313596088 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (10 : ZMod 9858091946062842016175737) ^ 72970732152 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_16792427843191929399890831 : Nat.Prime 16792427843191929399890831 := by
  apply lucas_primality 16792427843191929399890831 (11 : ZMod 16792427843191929399890831)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (107, 1), (923168105727978526657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (107, 1), (923168105727978526657, 1)] : List FactorBlock).map factorBlockValue).prod) = 16792427843191929399890831 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_5
      · exact prime_fortyTwoAN_17
      · exact prime_fortyTwoAN_107
      · exact prime_fortyTwoAN_923168105727978526657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 16792427843191929399890831) ^ 8396213921595964699945415 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (11 : ZMod 16792427843191929399890831) ^ 3358485568638385879978166 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (11 : ZMod 16792427843191929399890831) ^ 987789873128937023522990 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (11 : ZMod 16792427843191929399890831) ^ 156938577973756349531690 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (11 : ZMod 16792427843191929399890831) ^ 18190 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_18597456603864619938380969 : Nat.Prime 18597456603864619938380969 := by
  apply lucas_primality 18597456603864619938380969 (3 : ZMod 18597456603864619938380969)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (1173959, 1), (180018837229260329, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (1173959, 1), (180018837229260329, 1)] : List FactorBlock).map factorBlockValue).prod) = 18597456603864619938380969 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_11
      · exact prime_fortyTwoAN_1173959
      · exact prime_fortyTwoAN_180018837229260329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 18597456603864619938380969) ^ 9298728301932309969190484 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 18597456603864619938380969) ^ 1690677873078601812580088 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 18597456603864619938380969) ^ 15841657676174908952 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 18597456603864619938380969) ^ 103308392 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_20135932332651474142529273 : Nat.Prime 20135932332651474142529273 := by
  apply lucas_primality 20135932332651474142529273 (3 : ZMod 20135932332651474142529273)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17, 1), (991, 1), (3779417, 1), (39530687550041, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17, 1), (991, 1), (3779417, 1), (39530687550041, 1)] : List FactorBlock).map factorBlockValue).prod) = 20135932332651474142529273 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_17
      · exact prime_fortyTwoAN_991
      · exact prime_fortyTwoAN_3779417
      · exact prime_fortyTwoAN_39530687550041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 20135932332651474142529273) ^ 10067966166325737071264636 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 20135932332651474142529273) ^ 1184466607803027890737016 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 20135932332651474142529273) ^ 20318801546570609629192 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 20135932332651474142529273) ^ 5327787945244325816 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (3 : ZMod 20135932332651474142529273) ^ 509374705592 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_455552377360720506747497131 : Nat.Prime 455552377360720506747497131 := by
  apply lucas_primality 455552377360720506747497131 (7 : ZMod 455552377360720506747497131)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (1217, 1), (2861, 1), (3581, 1), (1217879459003443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (1217, 1), (2861, 1), (3581, 1), (1217879459003443, 1)] : List FactorBlock).map factorBlockValue).prod) = 455552377360720506747497131 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_5
      · exact prime_fortyTwoAN_1217
      · exact prime_fortyTwoAN_2861
      · exact prime_fortyTwoAN_3581
      · exact prime_fortyTwoAN_1217879459003443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 455552377360720506747497131) ^ 227776188680360253373748565 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (7 : ZMod 455552377360720506747497131) ^ 151850792453573502249165710 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (7 : ZMod 455552377360720506747497131) ^ 91110475472144101349499426 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (7 : ZMod 455552377360720506747497131) ^ 374324056993196800942890 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (7 : ZMod 455552377360720506747497131) ^ 159228373771660435773330 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (7 : ZMod 455552377360720506747497131) ^ 127213732856945128943730 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (7 : ZMod 455552377360720506747497131) ^ 374053748910 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_539730534046940600385621601 : Nat.Prime 539730534046940600385621601 := by
  apply lucas_primality 539730534046940600385621601 (46 : ZMod 539730534046940600385621601)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 4), (5, 2), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 4), (5, 2), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 539730534046940600385621601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_5
      · exact prime_fortyTwoAN_7
      · exact prime_fortyTwoAN_11
      · exact prime_fortyTwoAN_13
      · exact prime_fortyTwoAN_17
      · exact prime_fortyTwoAN_19
      · exact prime_fortyTwoAN_29
      · exact prime_fortyTwoAN_31
      · exact prime_fortyTwoAN_37
      · exact prime_fortyTwoAN_41
      · exact prime_fortyTwoAN_43
      · exact prime_fortyTwoAN_47
      · exact prime_fortyTwoAN_53
      · exact prime_fortyTwoAN_59
      · exact prime_fortyTwoAN_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (46 : ZMod 539730534046940600385621601) ^ 269865267023470300192810800 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (46 : ZMod 539730534046940600385621601) ^ 179910178015646866795207200 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (46 : ZMod 539730534046940600385621601) ^ 107946106809388120077124320 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (46 : ZMod 539730534046940600385621601) ^ 77104362006705800055088800 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (46 : ZMod 539730534046940600385621601) ^ 49066412186085509125965600 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (46 : ZMod 539730534046940600385621601) ^ 41517733388226200029663200 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (46 : ZMod 539730534046940600385621601) ^ 31748854943937682375624800 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (46 : ZMod 539730534046940600385621601) ^ 28406870212996873704506400 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (46 : ZMod 539730534046940600385621601) ^ 18611397725756572427090400 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (46 : ZMod 539730534046940600385621601) ^ 17410662388610987109213600 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (46 : ZMod 539730534046940600385621601) ^ 14587311730998394605016800 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (46 : ZMod 539730534046940600385621601) ^ 13164159366998551228917600 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (46 : ZMod 539730534046940600385621601) ^ 12551872884812572101991200 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (46 : ZMod 539730534046940600385621601) ^ 11483628383977459582672800 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (46 : ZMod 539730534046940600385621601) ^ 10183594982017747177087200 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (46 : ZMod 539730534046940600385621601) ^ 9147975153337976277722400 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (46 : ZMod 539730534046940600385621601) ^ 8848041541753124596485600 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_545661638816687200389859201 : Nat.Prime 545661638816687200389859201 := by
  apply lucas_primality 545661638816687200389859201 (13 : ZMod 545661638816687200389859201)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 4), (5, 2), (7, 2), (11, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 4), (5, 2), (7, 2), (11, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 545661638816687200389859201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_5
      · exact prime_fortyTwoAN_7
      · exact prime_fortyTwoAN_11
      · exact prime_fortyTwoAN_17
      · exact prime_fortyTwoAN_19
      · exact prime_fortyTwoAN_23
      · exact prime_fortyTwoAN_29
      · exact prime_fortyTwoAN_31
      · exact prime_fortyTwoAN_37
      · exact prime_fortyTwoAN_41
      · exact prime_fortyTwoAN_43
      · exact prime_fortyTwoAN_47
      · exact prime_fortyTwoAN_53
      · exact prime_fortyTwoAN_59
      · exact prime_fortyTwoAN_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 545661638816687200389859201) ^ 272830819408343600194929600 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 181887212938895733463286400 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 109132327763337440077971840 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 77951662688098171484265600 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 49605603528789745489987200 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 32097743459805129434697600 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 28719033621930905283676800 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 23724419078986400016950400 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 18815918579885765530684800 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 17601988348925393560963200 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 14747611859910464875401600 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 13308820458943590253411200 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 12689805553876446520694400 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 11609822102482706391273600 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 10295502619182777365846400 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 9248502352825206786268800 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (13 : ZMod 545661638816687200389859201) ^ 8945272767486675416227200 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_752351653519977806598139201 : Nat.Prime 752351653519977806598139201 := by
  apply lucas_primality 752351653519977806598139201 (22 : ZMod 752351653519977806598139201)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (5, 2), (7, 3), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (5, 2), (7, 3), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 752351653519977806598139201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_5
      · exact prime_fortyTwoAN_7
      · exact prime_fortyTwoAN_13
      · exact prime_fortyTwoAN_17
      · exact prime_fortyTwoAN_19
      · exact prime_fortyTwoAN_23
      · exact prime_fortyTwoAN_29
      · exact prime_fortyTwoAN_31
      · exact prime_fortyTwoAN_37
      · exact prime_fortyTwoAN_41
      · exact prime_fortyTwoAN_43
      · exact prime_fortyTwoAN_47
      · exact prime_fortyTwoAN_53
      · exact prime_fortyTwoAN_59
      · exact prime_fortyTwoAN_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (22 : ZMod 752351653519977806598139201) ^ 376175826759988903299069600 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 250783884506659268866046400 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 150470330703995561319627840 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 107478807645711115228305600 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 57873204116921369738318400 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 44255979618822223917537600 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 39597455448419884557796800 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 32710941457390339417310400 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 25943160466206131262004800 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 24269408178063800212843200 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 20333828473512913691841600 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 18350040329755556258491200 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 17496550081859948990654400 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 16007481989786761842513600 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 14195314217358071822606400 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 12751722941016572993188800 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (22 : ZMod 752351653519977806598139201) ^ 12333633664261931255707200 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_814019821841287462876675201 : Nat.Prime 814019821841287462876675201 := by
  apply lucas_primality 814019821841287462876675201 (79 : ZMod 814019821841287462876675201)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 4), (5, 2), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 4), (5, 2), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1)] : List FactorBlock).map factorBlockValue).prod) = 814019821841287462876675201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_5
      · exact prime_fortyTwoAN_7
      · exact prime_fortyTwoAN_11
      · exact prime_fortyTwoAN_13
      · exact prime_fortyTwoAN_17
      · exact prime_fortyTwoAN_19
      · exact prime_fortyTwoAN_23
      · exact prime_fortyTwoAN_29
      · exact prime_fortyTwoAN_31
      · exact prime_fortyTwoAN_37
      · exact prime_fortyTwoAN_41
      · exact prime_fortyTwoAN_43
      · exact prime_fortyTwoAN_47
      · exact prime_fortyTwoAN_53
      · exact prime_fortyTwoAN_59
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (79 : ZMod 814019821841287462876675201) ^ 407009910920643731438337600 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (79 : ZMod 814019821841287462876675201) ^ 271339940613762487625558400 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (79 : ZMod 814019821841287462876675201) ^ 162803964368257492575335040 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (79 : ZMod 814019821841287462876675201) ^ 116288545977326780410953600 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (79 : ZMod 814019821841287462876675201) ^ 74001801985571587534243200 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (79 : ZMod 814019821841287462876675201) ^ 62616909372406727913590400 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (79 : ZMod 814019821841287462876675201) ^ 47883518931840438992745600 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (79 : ZMod 814019821841287462876675201) ^ 42843148517962498046140800 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (79 : ZMod 814019821841287462876675201) ^ 35392166167012498385942400 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (79 : ZMod 814019821841287462876675201) ^ 28069649029009912512988800 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (79 : ZMod 814019821841287462876675201) ^ 26258703930364111705699200 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (79 : ZMod 814019821841287462876675201) ^ 22000535725440201699369600 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (79 : ZMod 814019821841287462876675201) ^ 19854141996128962509187200 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (79 : ZMod 814019821841287462876675201) ^ 18930693531192731694806400 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (79 : ZMod 814019821841287462876675201) ^ 17319570677474201337801600 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (79 : ZMod 814019821841287462876675201) ^ 15358864563043159676918400 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (79 : ZMod 814019821841287462876675201) ^ 13796946132903177336892800 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_919540909857750652508836801 : Nat.Prime 919540909857750652508836801 := by
  apply lucas_primality 919540909857750652508836801 (113 : ZMod 919540909857750652508836801)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (5, 2), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (5, 2), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 919540909857750652508836801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_5
      · exact prime_fortyTwoAN_7
      · exact prime_fortyTwoAN_11
      · exact prime_fortyTwoAN_13
      · exact prime_fortyTwoAN_17
      · exact prime_fortyTwoAN_19
      · exact prime_fortyTwoAN_23
      · exact prime_fortyTwoAN_29
      · exact prime_fortyTwoAN_31
      · exact prime_fortyTwoAN_37
      · exact prime_fortyTwoAN_41
      · exact prime_fortyTwoAN_43
      · exact prime_fortyTwoAN_47
      · exact prime_fortyTwoAN_53
      · exact prime_fortyTwoAN_59
      · exact prime_fortyTwoAN_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (113 : ZMod 919540909857750652508836801) ^ 459770454928875326254418400 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 306513636619250217502945600 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 183908181971550130501767360 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 131362987122535807501262400 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 83594628168886422955348800 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 70733916142903896346833600 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 54090641756338273676990400 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 48396889992513192237307200 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 39980039559032637065601600 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 31708307236474160431339200 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 29662609995411311371252800 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 24852457023182450067806400 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 22427827069701235427044800 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 21384672322273270988577600 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 19564700209739375585294400 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 17349828487882087783185600 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 15585439150131366991675200 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (113 : ZMod 919540909857750652508836801) ^ 15074441145209027090308800 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_2257054960559933419794417601 : Nat.Prime 2257054960559933419794417601 := by
  apply lucas_primality 2257054960559933419794417601 (142 : ZMod 2257054960559933419794417601)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 4), (5, 2), (7, 3), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 4), (5, 2), (7, 3), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 2257054960559933419794417601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_5
      · exact prime_fortyTwoAN_7
      · exact prime_fortyTwoAN_13
      · exact prime_fortyTwoAN_17
      · exact prime_fortyTwoAN_19
      · exact prime_fortyTwoAN_23
      · exact prime_fortyTwoAN_29
      · exact prime_fortyTwoAN_31
      · exact prime_fortyTwoAN_37
      · exact prime_fortyTwoAN_41
      · exact prime_fortyTwoAN_43
      · exact prime_fortyTwoAN_47
      · exact prime_fortyTwoAN_53
      · exact prime_fortyTwoAN_59
      · exact prime_fortyTwoAN_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (142 : ZMod 2257054960559933419794417601) ^ 1128527480279966709897208800 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (142 : ZMod 2257054960559933419794417601) ^ 752351653519977806598139200 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (142 : ZMod 2257054960559933419794417601) ^ 451410992111986683958883520 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (142 : ZMod 2257054960559933419794417601) ^ 322436422937133345684916800 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (142 : ZMod 2257054960559933419794417601) ^ 173619612350764109214955200 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (142 : ZMod 2257054960559933419794417601) ^ 132767938856466671752612800 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (142 : ZMod 2257054960559933419794417601) ^ 118792366345259653673390400 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (142 : ZMod 2257054960559933419794417601) ^ 98132824372171018251931200 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (142 : ZMod 2257054960559933419794417601) ^ 77829481398618393786014400 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (142 : ZMod 2257054960559933419794417601) ^ 72808224534191400638529600 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (142 : ZMod 2257054960559933419794417601) ^ 61001485420538741075524800 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (142 : ZMod 2257054960559933419794417601) ^ 55050120989266668775473600 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (142 : ZMod 2257054960559933419794417601) ^ 52489650245579846971963200 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (142 : ZMod 2257054960559933419794417601) ^ 48022445969360285527540800 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (142 : ZMod 2257054960559933419794417601) ^ 42585942652074215467819200 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (142 : ZMod 2257054960559933419794417601) ^ 38255168823049718979566400 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (142 : ZMod 2257054960559933419794417601) ^ 37000900992785793767121600 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_2482760456615926761773859361 : Nat.Prime 2482760456615926761773859361 := by
  apply lucas_primality 2482760456615926761773859361 (103 : ZMod 2482760456615926761773859361)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 4), (5, 1), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 4), (5, 1), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 2482760456615926761773859361 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_5
      · exact prime_fortyTwoAN_7
      · exact prime_fortyTwoAN_11
      · exact prime_fortyTwoAN_13
      · exact prime_fortyTwoAN_17
      · exact prime_fortyTwoAN_19
      · exact prime_fortyTwoAN_23
      · exact prime_fortyTwoAN_29
      · exact prime_fortyTwoAN_31
      · exact prime_fortyTwoAN_37
      · exact prime_fortyTwoAN_41
      · exact prime_fortyTwoAN_43
      · exact prime_fortyTwoAN_47
      · exact prime_fortyTwoAN_53
      · exact prime_fortyTwoAN_59
      · exact prime_fortyTwoAN_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (103 : ZMod 2482760456615926761773859361) ^ 1241380228307963380886929680 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (103 : ZMod 2482760456615926761773859361) ^ 827586818871975587257953120 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (103 : ZMod 2482760456615926761773859361) ^ 496552091323185352354771872 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (103 : ZMod 2482760456615926761773859361) ^ 354680065230846680253408480 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (103 : ZMod 2482760456615926761773859361) ^ 225705496055993341979441760 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (103 : ZMod 2482760456615926761773859361) ^ 190981573585840520136450720 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (103 : ZMod 2482760456615926761773859361) ^ 146044732742113338927874080 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (103 : ZMod 2482760456615926761773859361) ^ 130671602979785619040729440 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (103 : ZMod 2482760456615926761773859361) ^ 107946106809388120077124320 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (103 : ZMod 2482760456615926761773859361) ^ 85612429538480233164615840 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (103 : ZMod 2482760456615926761773859361) ^ 80089046987610540702382560 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (103 : ZMod 2482760456615926761773859361) ^ 67101633962592615183077280 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (103 : ZMod 2482760456615926761773859361) ^ 60555133088193335653020960 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (103 : ZMod 2482760456615926761773859361) ^ 57738615270137831669159520 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (103 : ZMod 2482760456615926761773859361) ^ 52824690566296314080294880 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (103 : ZMod 2482760456615926761773859361) ^ 46844536917281637014601120 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (103 : ZMod 2482760456615926761773859361) ^ 42080685705354690877523040 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (103 : ZMod 2482760456615926761773859361) ^ 40700991092064373143833760 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_12413802283079633808869296801 : Nat.Prime 12413802283079633808869296801 := by
  apply lucas_primality 12413802283079633808869296801 (71 : ZMod 12413802283079633808869296801)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 4), (5, 2), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 4), (5, 2), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 12413802283079633808869296801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_5
      · exact prime_fortyTwoAN_7
      · exact prime_fortyTwoAN_11
      · exact prime_fortyTwoAN_13
      · exact prime_fortyTwoAN_17
      · exact prime_fortyTwoAN_19
      · exact prime_fortyTwoAN_23
      · exact prime_fortyTwoAN_29
      · exact prime_fortyTwoAN_31
      · exact prime_fortyTwoAN_37
      · exact prime_fortyTwoAN_41
      · exact prime_fortyTwoAN_43
      · exact prime_fortyTwoAN_47
      · exact prime_fortyTwoAN_53
      · exact prime_fortyTwoAN_59
      · exact prime_fortyTwoAN_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (71 : ZMod 12413802283079633808869296801) ^ 6206901141539816904434648400 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (71 : ZMod 12413802283079633808869296801) ^ 4137934094359877936289765600 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (71 : ZMod 12413802283079633808869296801) ^ 2482760456615926761773859360 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (71 : ZMod 12413802283079633808869296801) ^ 1773400326154233401267042400 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (71 : ZMod 12413802283079633808869296801) ^ 1128527480279966709897208800 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (71 : ZMod 12413802283079633808869296801) ^ 954907867929202600682253600 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (71 : ZMod 12413802283079633808869296801) ^ 730223663710566694639370400 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (71 : ZMod 12413802283079633808869296801) ^ 653358014898928095203647200 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (71 : ZMod 12413802283079633808869296801) ^ 539730534046940600385621600 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (71 : ZMod 12413802283079633808869296801) ^ 428062147692401165823079200 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (71 : ZMod 12413802283079633808869296801) ^ 400445234938052703511912800 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (71 : ZMod 12413802283079633808869296801) ^ 335508169812963075915386400 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (71 : ZMod 12413802283079633808869296801) ^ 302775665440966678265104800 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (71 : ZMod 12413802283079633808869296801) ^ 288693076350689158345797600 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (71 : ZMod 12413802283079633808869296801) ^ 264123452831481570401474400 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (71 : ZMod 12413802283079633808869296801) ^ 234222684586408185073005600 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (71 : ZMod 12413802283079633808869296801) ^ 210403428526773454387615200 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (71 : ZMod 12413802283079633808869296801) ^ 203504955460321865719168800 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem prime_fortyTwoAN_49655209132318535235477187273 : Nat.Prime 49655209132318535235477187273 := by
  apply lucas_primality 49655209132318535235477187273 (11 : ZMod 49655209132318535235477187273)
  · rw [← fortyTwoANFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (131, 1), (233, 1), (550990241, 1), (41007301887107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (131, 1), (233, 1), (550990241, 1), (41007301887107, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187273 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fortyTwoAN_2
      · exact prime_fortyTwoAN_3
      · exact prime_fortyTwoAN_131
      · exact prime_fortyTwoAN_233
      · exact prime_fortyTwoAN_550990241
      · exact prime_fortyTwoAN_41007301887107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 49655209132318535235477187273) ^ 24827604566159267617738593636 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (11 : ZMod 49655209132318535235477187273) ^ 16551736377439511745159062424 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (11 : ZMod 49655209132318535235477187273) ^ 379047397956630039965474712 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (11 : ZMod 49655209132318535235477187273) ^ 213112485546431481697326984 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (11 : ZMod 49655209132318535235477187273) ^ 90119943036012021192 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide
    · change (11 : ZMod 49655209132318535235477187273) ^ 1210887009075096 ≠ 1
      rw [← fortyTwoANFastPow_eq_pow]
      decide

private theorem phi_fortyTwoAN_49655209132318535235477187200 : Nat.totient 49655209132318535235477187200 = 6533997475293146854195200000 := by
  rw [← show ((([(2, 7), (3, 4), (5, 2), (7, 3), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187200 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_2, prime_fortyTwoAN_3, prime_fortyTwoAN_5, prime_fortyTwoAN_7, prime_fortyTwoAN_11, prime_fortyTwoAN_13, prime_fortyTwoAN_17, prime_fortyTwoAN_19, prime_fortyTwoAN_23, prime_fortyTwoAN_29, prime_fortyTwoAN_31, prime_fortyTwoAN_37, prime_fortyTwoAN_41, prime_fortyTwoAN_43, prime_fortyTwoAN_47, prime_fortyTwoAN_53, prime_fortyTwoAN_59, prime_fortyTwoAN_61]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187201 : Nat.totient 49655209132318535235477187201 = 49640025881774073403490364000 := by
  rw [← show ((([(3271, 1), (17642671, 1), (860438700574923961, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187201 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_3271, prime_fortyTwoAN_17642671, prime_fortyTwoAN_860438700574923961]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187202 : Nat.totient 49655209132318535235477187202 = 24776621600609126786919635520 := by
  rw [← show ((([(2, 1), (487, 1), (10972711, 1), (4646135993926002193, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187202 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_2, prime_fortyTwoAN_487, prime_fortyTwoAN_10972711, prime_fortyTwoAN_4646135993926002193]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187203 : Nat.totient 49655209132318535235477187203 = 32975677887885050105571210240 := by
  rw [← show ((([(3, 1), (269, 1), (7691, 1), (111869, 1), (218857, 1), (326767060643, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187203 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_3, prime_fortyTwoAN_269, prime_fortyTwoAN_7691, prime_fortyTwoAN_111869, prime_fortyTwoAN_218857, prime_fortyTwoAN_326767060643]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187204 : Nat.totient 49655209132318535235477187204 = 24827604566159267617738593600 := by
  rw [← show ((([(2, 2), (12413802283079633808869296801, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187204 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_2, prime_fortyTwoAN_12413802283079633808869296801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187205 : Nat.totient 49655209132318535235477187205 = 39721449678728098130251871040 := by
  rw [← show ((([(5, 1), (19163, 1), (61631, 1), (266215399, 1), (31586312203, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187205 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_5, prime_fortyTwoAN_19163, prime_fortyTwoAN_61631, prime_fortyTwoAN_266215399, prime_fortyTwoAN_31586312203]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187206 : Nat.totient 49655209132318535235477187206 = 16551606546661648594314053384 := by
  rw [← show ((([(2, 1), (3, 1), (127487, 1), (64915388931575422377023, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187206 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_2, prime_fortyTwoAN_3, prime_fortyTwoAN_127487, prime_fortyTwoAN_64915388931575422377023]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187207 : Nat.totient 49655209132318535235477187207 = 42561240608877117829114754880 := by
  rw [← show ((([(7, 1), (115903, 1), (32244294937, 1), (1898100541591, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187207 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_7, prime_fortyTwoAN_115903, prime_fortyTwoAN_32244294937, prime_fortyTwoAN_1898100541591]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187208 : Nat.totient 49655209132318535235477187208 = 24827559852119782627528993728 := by
  rw [← show ((([(2, 3), (555253, 1), (11178509871247551844717, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187208 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_2, prime_fortyTwoAN_555253, prime_fortyTwoAN_11178509871247551844717]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187209 : Nat.totient 49655209132318535235477187209 = 32900383964568297342037936320 := by
  rw [← show ((([(3, 2), (163, 1), (81554969011, 1), (415034571917257, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187209 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_3, prime_fortyTwoAN_163, prime_fortyTwoAN_81554969011, prime_fortyTwoAN_415034571917257]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187210 : Nat.totient 49655209132318535235477187210 = 19862082389554222650585244800 := by
  rw [← show ((([(2, 1), (5, 1), (15756119, 1), (8977309801, 1), (35105030159, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187210 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_2, prime_fortyTwoAN_5, prime_fortyTwoAN_15756119, prime_fortyTwoAN_8977309801, prime_fortyTwoAN_35105030159]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187211 : Nat.totient 49655209132318535235477187211 = 44776188138698429839050240000 := by
  rw [← show ((([(11, 1), (251, 1), (353, 1), (787, 1), (72797, 1), (393247, 1), (2261361899, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187211 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_11, prime_fortyTwoAN_251, prime_fortyTwoAN_353, prime_fortyTwoAN_787, prime_fortyTwoAN_72797, prime_fortyTwoAN_393247, prime_fortyTwoAN_2261361899]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187212 : Nat.totient 49655209132318535235477187212 = 16551690856989422392767979600 := by
  rw [← show ((([(2, 2), (3, 1), (363611, 1), (11380112522338097407091, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187212 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_2, prime_fortyTwoAN_3, prime_fortyTwoAN_363611, prime_fortyTwoAN_11380112522338097407091]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187213 : Nat.totient 49655209132318535235477187213 = 45835487389905977454124290624 := by
  rw [← show ((([(13, 1), (507757, 1), (7522557978948218149093, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187213 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_13, prime_fortyTwoAN_507757, prime_fortyTwoAN_7522557978948218149093]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187214 : Nat.totient 49655209132318535235477187214 = 21280803913151441936032356600 := by
  rw [← show ((([(2, 1), (7, 1), (30429025931, 1), (116559782766332771, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187214 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_2, prime_fortyTwoAN_7, prime_fortyTwoAN_30429025931, prime_fortyTwoAN_116559782766332771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187215 : Nat.totient 49655209132318535235477187215 = 26454529784472973252186266240 := by
  rw [← show ((([(3, 1), (5, 1), (1667, 1), (2141, 1), (927515741733830445223, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187215 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_3, prime_fortyTwoAN_5, prime_fortyTwoAN_1667, prime_fortyTwoAN_2141, prime_fortyTwoAN_927515741733830445223]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187216 : Nat.totient 49655209132318535235477187216 = 24581785209291274606978329600 := by
  rw [← show ((([(2, 4), (101, 1), (16499213, 1), (1862345396350691977, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187216 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_2, prime_fortyTwoAN_101, prime_fortyTwoAN_16499213, prime_fortyTwoAN_1862345396350691977]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187217 : Nat.totient 49655209132318535235477187217 = 46142740874510208124496052480 := by
  rw [← show ((([(17, 1), (79, 1), (23241977389, 1), (1590800534845771, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187217 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_17, prime_fortyTwoAN_79, prime_fortyTwoAN_23241977389, prime_fortyTwoAN_1590800534845771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187218 : Nat.totient 49655209132318535235477187218 = 16430920783443602900303885952 := by
  rw [← show ((([(2, 1), (3, 2), (137, 1), (20135932332651474142529273, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187218 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_2, prime_fortyTwoAN_3, prime_fortyTwoAN_137, prime_fortyTwoAN_20135932332651474142529273]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187219 : Nat.totient 49655209132318535235477187219 = 47040927323581311508101036960 := by
  rw [← show ((([(19, 1), (55511, 1), (20298013, 1), (2319415937889107, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187219 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_19, prime_fortyTwoAN_55511, prime_fortyTwoAN_20298013, prime_fortyTwoAN_2319415937889107]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187220 : Nat.totient 49655209132318535235477187220 = 19862083652927414094190874880 := by
  rw [← show ((([(2, 2), (5, 1), (2482760456615926761773859361, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187220 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_2, prime_fortyTwoAN_5, prime_fortyTwoAN_2482760456615926761773859361]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187221 : Nat.totient 49655209132318535235477187221 = 28374270226316623452091290624 := by
  rw [← show ((([(3, 1), (7, 1), (210193, 1), (11249345925914014905457, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187221 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_3, prime_fortyTwoAN_7, prime_fortyTwoAN_210193, prime_fortyTwoAN_11249345925914014905457]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187222 : Nat.totient 49655209132318535235477187222 = 22570549605599334197944176000 := by
  rw [← show ((([(2, 1), (11, 1), (2257054960559933419794417601, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187222 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_2, prime_fortyTwoAN_11, prime_fortyTwoAN_2257054960559933419794417601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187223 : Nat.totient 49655209132318535235477187223 = 47495410146997608162217631704 := by
  rw [← show ((([(23, 1), (54167, 1), (39856778780212350721703, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187223 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_23, prime_fortyTwoAN_54167, prime_fortyTwoAN_39856778780212350721703]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187224 : Nat.totient 49655209132318535235477187224 = 16543997288938364065731985536 := by
  rw [← show ((([(2, 3), (3, 1), (3023, 1), (7309, 1), (93639150386551147643, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187224 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_2, prime_fortyTwoAN_3, prime_fortyTwoAN_3023, prime_fortyTwoAN_7309, prime_fortyTwoAN_93639150386551147643]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187225 : Nat.totient 49655209132318535235477187225 = 39723295950526693029492695040 := by
  rw [← show ((([(5, 2), (45589, 1), (36793525309, 1), (1184113519489, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187225 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_5, prime_fortyTwoAN_45589, prime_fortyTwoAN_36793525309, prime_fortyTwoAN_1184113519489]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187226 : Nat.totient 49655209132318535235477187226 = 22875891592951135062779246064 := by
  rw [← show ((([(2, 1), (13, 1), (547, 1), (3491436445810612799569483, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187226 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_2, prime_fortyTwoAN_13, prime_fortyTwoAN_547, prime_fortyTwoAN_3491436445810612799569483]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187227 : Nat.totient 49655209132318535235477187227 = 32935429281494926955649404160 := by
  rw [← show ((([(3, 3), (197, 1), (5944361, 1), (1570470015063981253, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187227 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_3, prime_fortyTwoAN_197, prime_fortyTwoAN_5944361, prime_fortyTwoAN_1570470015063981253]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187228 : Nat.totient 49655209132318535235477187228 = 21277989704366903307463050240 := by
  rw [← show ((([(2, 2), (7, 1), (8233, 1), (93811, 1), (8274073, 1), (277508030299, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187228 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_2, prime_fortyTwoAN_7, prime_fortyTwoAN_8233, prime_fortyTwoAN_93811, prime_fortyTwoAN_8274073, prime_fortyTwoAN_277508030299]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187229 : Nat.totient 49655209132318535235477187229 = 47905766623363089664060563712 := by
  rw [← show ((([(29, 1), (1289, 1), (1328354220922889575866809, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187229 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_29, prime_fortyTwoAN_1289, prime_fortyTwoAN_1328354220922889575866809]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187230 : Nat.totient 49655209132318535235477187230 = 13092609449120692436620201472 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (89, 1), (18597456603864619938380969, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187230 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_2, prime_fortyTwoAN_3, prime_fortyTwoAN_5, prime_fortyTwoAN_89, prime_fortyTwoAN_18597456603864619938380969]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187231 : Nat.totient 49655209132318535235477187231 = 48053416445425909155581397120 := by
  rw [← show ((([(31, 1), (4090649, 1), (391571347175524180649, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187231 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_31, prime_fortyTwoAN_4090649, prime_fortyTwoAN_391571347175524180649]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187232 : Nat.totient 49655209132318535235477187232 = 24809442456015771445377387712 := by
  rw [← show ((([(2, 5), (1367, 1), (1135131883968510772574003, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187232 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_2, prime_fortyTwoAN_1367, prime_fortyTwoAN_1135131883968510772574003]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187233 : Nat.totient 49655209132318535235477187233 = 30040170703737860275477401600 := by
  rw [← show ((([(3, 1), (11, 1), (643, 1), (4289, 1), (344543, 1), (1583581521533941, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187233 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_3, prime_fortyTwoAN_11, prime_fortyTwoAN_643, prime_fortyTwoAN_4289, prime_fortyTwoAN_344543, prime_fortyTwoAN_1583581521533941]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187234 : Nat.totient 49655209132318535235477187234 = 23070663703901839199049875712 := by
  rw [← show ((([(2, 1), (17, 1), (83, 1), (1543, 1), (11403597493703654977229, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187234 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_2, prime_fortyTwoAN_17, prime_fortyTwoAN_83, prime_fortyTwoAN_1543, prime_fortyTwoAN_11403597493703654977229]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187235 : Nat.totient 49655209132318535235477187235 = 34016583479430296035966205952 := by
  rw [← show ((([(5, 1), (7, 1), (1049, 1), (139537, 1), (175593973, 1), (55197867029, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187235 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_5, prime_fortyTwoAN_7, prime_fortyTwoAN_1049, prime_fortyTwoAN_139537, prime_fortyTwoAN_175593973, prime_fortyTwoAN_55197867029]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187236 : Nat.totient 49655209132318535235477187236 = 16488227495127107506625879040 := by
  rw [← show ((([(2, 2), (3, 2), (263, 1), (33811, 1), (189853, 1), (817016986973969, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187236 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_2, prime_fortyTwoAN_3, prime_fortyTwoAN_263, prime_fortyTwoAN_33811, prime_fortyTwoAN_189853, prime_fortyTwoAN_817016986973969]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187237 : Nat.totient 49655209132318535235477187237 = 48313176452122430383348430592 := by
  rw [← show ((([(37, 1), (51165623833, 1), (26229186291798697, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187237 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_37, prime_fortyTwoAN_51165623833, prime_fortyTwoAN_26229186291798697]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187238 : Nat.totient 49655209132318535235477187238 = 23520887723631847361264566272 := by
  rw [← show ((([(2, 1), (19, 1), (28940609, 1), (45151642448085877889, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187238 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_2, prime_fortyTwoAN_19, prime_fortyTwoAN_28940609, prime_fortyTwoAN_45151642448085877889]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187239 : Nat.totient 49655209132318535235477187239 = 30557051773732709505301727328 := by
  rw [← show ((([(3, 1), (13, 1), (27346626158783, 1), (46558229274047, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187239 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_3, prime_fortyTwoAN_13, prime_fortyTwoAN_27346626158783, prime_fortyTwoAN_46558229274047]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187240 : Nat.totient 49655209132318535235477187240 = 19862083652697308269217160000 := by
  rw [← show ((([(2, 3), (5, 1), (86317688251, 1), (14381527743168931, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187240 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_2, prime_fortyTwoAN_5, prime_fortyTwoAN_86317688251, prime_fortyTwoAN_14381527743168931]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187241 : Nat.totient 49655209132318535235477187241 = 48422215776261602698411972480 := by
  rw [← show ((([(41, 1), (2213, 1), (547267357326645600117677, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187241 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_41, prime_fortyTwoAN_2213, prime_fortyTwoAN_547267357326645600117677]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187242 : Nat.totient 49655209132318535235477187242 = 14046657934239547674011714304 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (103, 1), (5009, 1), (2291539082278737626663, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187242 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_2, prime_fortyTwoAN_3, prime_fortyTwoAN_7, prime_fortyTwoAN_103, prime_fortyTwoAN_5009, prime_fortyTwoAN_2291539082278737626663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187243 : Nat.totient 49655209132318535235477187243 = 48500436824033714861976907944 := by
  rw [← show ((([(43, 1), (16828374767, 1), (68620548412508303, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187243 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_43, prime_fortyTwoAN_16828374767, prime_fortyTwoAN_68620548412508303]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187244 : Nat.totient 49655209132318535235477187244 = 22507678993301971338309000960 := by
  rw [← show ((([(2, 2), (11, 1), (359, 1), (38651421607, 1), (81330270790577, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187244 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_2, prime_fortyTwoAN_11, prime_fortyTwoAN_359, prime_fortyTwoAN_38651421607, prime_fortyTwoAN_81330270790577]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187245 : Nat.totient 49655209132318535235477187245 = 26482773451824590207379461088 := by
  rw [← show ((([(3, 2), (5, 1), (5572883, 1), (198003276191030887067, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187245 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_3, prime_fortyTwoAN_5, prime_fortyTwoAN_5572883, prime_fortyTwoAN_198003276191030887067]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187246 : Nat.totient 49655209132318535235477187246 = 23748143350125118194406762560 := by
  rw [← show ((([(2, 1), (23, 1), (213426679, 1), (712658239, 1), (7097035321, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187246 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_2, prime_fortyTwoAN_23, prime_fortyTwoAN_213426679, prime_fortyTwoAN_712658239, prime_fortyTwoAN_7097035321]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187247 : Nat.totient 49655209132318535235477187247 = 48595195426223933021970864000 := by
  rw [← show ((([(47, 1), (13807, 1), (1422302993, 1), (53799161710751, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187247 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_47, prime_fortyTwoAN_13807, prime_fortyTwoAN_1422302993, prime_fortyTwoAN_53799161710751]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187248 : Nat.totient 49655209132318535235477187248 = 16465976085328426192075333632 := by
  rw [← show ((([(2, 4), (3, 1), (193, 1), (5360018256942847067732857, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187248 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_2, prime_fortyTwoAN_3, prime_fortyTwoAN_193, prime_fortyTwoAN_5360018256942847067732857]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187249 : Nat.totient 49655209132318535235477187249 = 42427070739375155652852411840 := by
  rw [← show ((([(7, 2), (331, 1), (7129, 1), (429449525106920937499, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187249 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_7, prime_fortyTwoAN_331, prime_fortyTwoAN_7129, prime_fortyTwoAN_429449525106920937499]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187250 : Nat.totient 49655209132318535235477187250 = 19805171063092871920342329600 := by
  rw [← show ((([(2, 1), (5, 3), (349, 1), (16850357, 1), (33774604584521293, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187250 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_2, prime_fortyTwoAN_5, prime_fortyTwoAN_349, prime_fortyTwoAN_16850357, prime_fortyTwoAN_33774604584521293]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187251 : Nat.totient 49655209132318535235477187251 = 31152148304177604050214912000 := by
  rw [← show ((([(3, 1), (17, 1), (7681, 1), (6135331, 1), (20660407174714891, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187251 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_3, prime_fortyTwoAN_17, prime_fortyTwoAN_7681, prime_fortyTwoAN_6135331, prime_fortyTwoAN_20660407174714891]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187252 : Nat.totient 49655209132318535235477187252 = 22640583631096406971146977280 := by
  rw [← show ((([(2, 2), (13, 1), (167, 1), (173, 1), (2731, 1), (142700137, 1), (84811121713, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187252 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_2, prime_fortyTwoAN_13, prime_fortyTwoAN_167, prime_fortyTwoAN_173, prime_fortyTwoAN_2731, prime_fortyTwoAN_142700137, prime_fortyTwoAN_84811121713]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187253 : Nat.totient 49655209132318535235477187253 = 48718318393940670062337591504 := by
  rw [← show ((([(53, 1), (1515172544143, 1), (618339305293807, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187253 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_53, prime_fortyTwoAN_1515172544143, prime_fortyTwoAN_618339305293807]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187254 : Nat.totient 49655209132318535235477187254 = 16551736377439511745159062400 := by
  rw [← show ((([(2, 1), (3, 3), (919540909857750652508836801, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187254 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_2, prime_fortyTwoAN_3, prime_fortyTwoAN_919540909857750652508836801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187255 : Nat.totient 49655209132318535235477187255 = 35518987229413616178639417600 := by
  rw [← show ((([(5, 1), (11, 2), (67, 1), (677, 1), (15131, 1), (119585448875776439, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187255 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_5, prime_fortyTwoAN_11, prime_fortyTwoAN_67, prime_fortyTwoAN_677, prime_fortyTwoAN_15131, prime_fortyTwoAN_119585448875776439]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187256 : Nat.totient 49655209132318535235477187256 = 21240739924839212415211929600 := by
  rw [← show ((([(2, 3), (7, 1), (769, 1), (2143, 1), (8597, 1), (9792301, 1), (6391408799, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187256 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_2, prime_fortyTwoAN_7, prime_fortyTwoAN_769, prime_fortyTwoAN_2143, prime_fortyTwoAN_8597, prime_fortyTwoAN_9792301, prime_fortyTwoAN_6391408799]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187257 : Nat.totient 49655209132318535235477187257 = 31334855801589423198421862400 := by
  rw [← show ((([(3, 1), (19, 1), (1201, 1), (201823, 1), (512903, 1), (7007144209529, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187257 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_3, prime_fortyTwoAN_19, prime_fortyTwoAN_1201, prime_fortyTwoAN_201823, prime_fortyTwoAN_512903, prime_fortyTwoAN_7007144209529]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187258 : Nat.totient 49655209132318535235477187258 = 23971478923180627879786433856 := by
  rw [← show ((([(2, 1), (29, 1), (17788357, 1), (48128351335921711693, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187258 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_2, prime_fortyTwoAN_29, prime_fortyTwoAN_17788357, prime_fortyTwoAN_48128351335921711693]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187259 : Nat.totient 49655209132318535235477187259 = 48813595417753213018589876232 := by
  rw [← show ((([(59, 1), (106528215379, 1), (7900383115523419, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187259 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_59, prime_fortyTwoAN_106528215379, prime_fortyTwoAN_7900383115523419]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187260 : Nat.totient 49655209132318535235477187260 = 13104633240301487415494860800 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (97, 1), (72973, 1), (195271, 1), (598744972004371, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187260 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_2, prime_fortyTwoAN_3, prime_fortyTwoAN_5, prime_fortyTwoAN_97, prime_fortyTwoAN_72973, prime_fortyTwoAN_195271, prime_fortyTwoAN_598744972004371]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187261 : Nat.totient 49655209132318535235477187261 = 48841189310477247772600512000 := by
  rw [← show ((([(61, 1), (814019821841287462876675201, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187261 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_61, prime_fortyTwoAN_814019821841287462876675201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187262 : Nat.totient 49655209132318535235477187262 = 24025232520523386471524086560 := by
  rw [← show ((([(2, 1), (31, 2), (16217, 1), (1593092214812622769463, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187262 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_2, prime_fortyTwoAN_31, prime_fortyTwoAN_16217, prime_fortyTwoAN_1593092214812622769463]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187263 : Nat.totient 49655209132318535235477187263 = 28287895126696180418596608000 := by
  rw [← show ((([(3, 2), (7, 1), (421, 1), (1483, 1), (2072201, 1), (2567179, 1), (237308333, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187263 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_3, prime_fortyTwoAN_7, prime_fortyTwoAN_421, prime_fortyTwoAN_1483, prime_fortyTwoAN_2072201, prime_fortyTwoAN_2567179, prime_fortyTwoAN_237308333]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187264 : Nat.totient 49655209132318535235477187264 = 24465845066978806818058368000 := by
  rw [← show ((([(2, 6), (71, 1), (2029, 1), (2245339, 1), (2398625938490051, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187264 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_2, prime_fortyTwoAN_71, prime_fortyTwoAN_2029, prime_fortyTwoAN_2245339, prime_fortyTwoAN_2398625938490051]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187265 : Nat.totient 49655209132318535235477187265 = 36668462123093456135237455872 := by
  rw [← show ((([(5, 1), (13, 1), (6805676209, 1), (112248404256013009, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187265 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_5, prime_fortyTwoAN_13, prime_fortyTwoAN_6805676209, prime_fortyTwoAN_112248404256013009]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187266 : Nat.totient 49655209132318535235477187266 = 15047033070399556131962784000 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (752351653519977806598139201, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187266 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_2, prime_fortyTwoAN_3, prime_fortyTwoAN_11, prime_fortyTwoAN_752351653519977806598139201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187267 : Nat.totient 49655209132318535235477187267 = 49638416704475343306077293480 := by
  rw [← show ((([(2957, 1), (16792427843191929399890831, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187267 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_2957, prime_fortyTwoAN_16792427843191929399890831]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187268 : Nat.totient 49655209132318535235477187268 = 23344309015057236659434074624 := by
  rw [← show ((([(2, 2), (17, 1), (1879, 1), (2243, 1), (173260613935464457133, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187268 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_2, prime_fortyTwoAN_17, prime_fortyTwoAN_1879, prime_fortyTwoAN_2243, prime_fortyTwoAN_173260613935464457133]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187269 : Nat.totient 49655209132318535235477187269 = 31230435285127083507244731648 := by
  rw [← show ((([(3, 1), (23, 1), (73, 1), (9858091946062842016175737, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187269 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_3, prime_fortyTwoAN_23, prime_fortyTwoAN_73, prime_fortyTwoAN_9858091946062842016175737]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187270 : Nat.totient 49655209132318535235477187270 = 16941101785182382994115471360 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (281, 1), (739, 1), (3540386347, 1), (964862349257, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187270 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_2, prime_fortyTwoAN_5, prime_fortyTwoAN_7, prime_fortyTwoAN_281, prime_fortyTwoAN_739, prime_fortyTwoAN_3540386347, prime_fortyTwoAN_964862349257]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187271 : Nat.totient 49655209132318535235477187271 = 49622210866297053200739489120 := by
  rw [← show ((([(2039, 1), (5741, 1), (89401187, 1), (47447873988967, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187271 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_2039, prime_fortyTwoAN_5741, prime_fortyTwoAN_89401187, prime_fortyTwoAN_47447873988967]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187272 : Nat.totient 49655209132318535235477187272 = 16354891990877622562043289600 := by
  rw [← show ((([(2, 3), (3, 2), (131, 1), (233, 1), (550990241, 1), (41007301887107, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187272 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_2, prime_fortyTwoAN_3, prime_fortyTwoAN_131, prime_fortyTwoAN_233, prime_fortyTwoAN_550990241, prime_fortyTwoAN_41007301887107]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187273 : Nat.totient 49655209132318535235477187273 = 49655209132318535235477187272 := by
  rw [← show ((([(49655209132318535235477187273, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187273 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_49655209132318535235477187273]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187274 : Nat.totient 49655209132318535235477187274 = 24125337065643036484669013952 := by
  rw [← show ((([(2, 1), (37, 1), (773, 1), (33352703, 1), (26026907316507379, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187274 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_2, prime_fortyTwoAN_37, prime_fortyTwoAN_773, prime_fortyTwoAN_33352703, prime_fortyTwoAN_26026907316507379]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187275 : Nat.totient 49655209132318535235477187275 = 26482154536320289014227806080 := by
  rw [← show ((([(3, 1), (5, 2), (42463, 1), (102310987907, 1), (152394958517, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187275 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_3, prime_fortyTwoAN_5, prime_fortyTwoAN_42463, prime_fortyTwoAN_102310987907, prime_fortyTwoAN_152394958517]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187276 : Nat.totient 49655209132318535235477187276 = 23520817581100342850650374144 := by
  rw [← show ((([(2, 2), (19, 1), (331489, 1), (1970979474127129694209, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187276 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_2, prime_fortyTwoAN_19, prime_fortyTwoAN_331489, prime_fortyTwoAN_1970979474127129694209]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187277 : Nat.totient 49655209132318535235477187277 = 38691778006785699526546146240 := by
  rw [← show ((([(7, 1), (11, 1), (97327, 1), (208223, 1), (4129087, 1), (7706514863, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187277 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_7, prime_fortyTwoAN_11, prime_fortyTwoAN_97327, prime_fortyTwoAN_208223, prime_fortyTwoAN_4129087, prime_fortyTwoAN_7706514863]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187278 : Nat.totient 49655209132318535235477187278 = 15277055525411475347645477280 := by
  rw [← show ((([(2, 1), (3, 1), (13, 2), (10391, 1), (4712696973609818164547, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187278 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_2, prime_fortyTwoAN_3, prime_fortyTwoAN_13, prime_fortyTwoAN_10391, prime_fortyTwoAN_4712696973609818164547]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187279 : Nat.totient 49655209132318535235477187279 = 49199656754957814728729690040 := by
  rw [← show ((([(109, 1), (455552377360720506747497131, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187279 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_109, prime_fortyTwoAN_455552377360720506747497131]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187280 : Nat.totient 49655209132318535235477187280 = 19862038426617723956590108800 := by
  rw [← show ((([(2, 4), (5, 1), (439171, 1), (1413322177816799584771, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187280 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_2, prime_fortyTwoAN_5, prime_fortyTwoAN_439171, prime_fortyTwoAN_1413322177816799584771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187281 : Nat.totient 49655209132318535235477187281 = 33099948296605652127005059200 := by
  rw [← show ((([(3, 5), (10141, 1), (127241, 1), (158361893331124207, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187281 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_3, prime_fortyTwoAN_10141, prime_fortyTwoAN_127241, prime_fortyTwoAN_158361893331124207]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187282 : Nat.totient 49655209132318535235477187282 = 24157200706463363325713815680 := by
  rw [← show ((([(2, 1), (41, 2), (683, 1), (823, 1), (26275232482769198029, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187282 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_2, prime_fortyTwoAN_41, prime_fortyTwoAN_683, prime_fortyTwoAN_823, prime_fortyTwoAN_26275232482769198029]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187283 : Nat.totient 49655209132318535235477187283 = 49624309809636086728133244864 := by
  rw [← show ((([(1607, 1), (32976288733, 1), (937016334000793, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187283 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_1607, prime_fortyTwoAN_32976288733, prime_fortyTwoAN_937016334000793]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187284 : Nat.totient 49655209132318535235477187284 = 14187202597629893889172946400 := by
  rw [← show ((([(2, 2), (3, 1), (7, 1), (1222615931, 1), (483498887150858771, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187284 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_2, prime_fortyTwoAN_3, prime_fortyTwoAN_7, prime_fortyTwoAN_1222615931, prime_fortyTwoAN_483498887150858771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187285 : Nat.totient 49655209132318535235477187285 = 37093062198913346893947144192 := by
  rw [← show ((([(5, 1), (17, 1), (127, 1), (69747157289, 1), (65950130168807, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187285 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_5, prime_fortyTwoAN_17, prime_fortyTwoAN_127, prime_fortyTwoAN_69747157289, prime_fortyTwoAN_65950130168807]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187286 : Nat.totient 49655209132318535235477187286 = 24250218400348903079929471968 := by
  rw [← show ((([(2, 1), (43, 1), (1849892749, 1), (312118717700524549, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187286 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_2, prime_fortyTwoAN_43, prime_fortyTwoAN_1849892749, prime_fortyTwoAN_312118717700524549]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187287 : Nat.totient 49655209132318535235477187287 = 31961973506338070478142064352 := by
  rw [← show ((([(3, 1), (29, 1), (169985287, 1), (3357640771913012023, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187287 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_3, prime_fortyTwoAN_29, prime_fortyTwoAN_169985287, prime_fortyTwoAN_3357640771913012023]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187288 : Nat.totient 49655209132318535235477187288 = 22564031976490007217234264480 := by
  rw [← show ((([(2, 3), (11, 1), (3463, 1), (162940727733174517744327, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187288 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_2, prime_fortyTwoAN_11, prime_fortyTwoAN_3463, prime_fortyTwoAN_162940727733174517744327]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187289 : Nat.totient 49655209132318535235477187289 = 49636059415893638683834064896 := by
  rw [← show ((([(2657, 1), (107609, 1), (173669944451063813153, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187289 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_2657, prime_fortyTwoAN_107609, prime_fortyTwoAN_173669944451063813153]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187290 : Nat.totient 49655209132318535235477187290 = 13241389101420110042942182368 := by
  rw [← show ((([(2, 1), (3, 2), (5, 1), (24913302187, 1), (22145781469408963, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187290 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_2, prime_fortyTwoAN_3, prime_fortyTwoAN_5, prime_fortyTwoAN_24913302187, prime_fortyTwoAN_22145781469408963]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187291 : Nat.totient 49655209132318535235477187291 = 39287637994801478428069862400 := by
  rw [← show ((([(7, 1), (13, 1), (545661638816687200389859201, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187291 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_7, prime_fortyTwoAN_13, prime_fortyTwoAN_545661638816687200389859201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187292 : Nat.totient 49655209132318535235477187292 = 23748143498065386416967350400 := by
  rw [← show ((([(2, 2), (23, 1), (539730534046940600385621601, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187292 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_2, prime_fortyTwoAN_23, prime_fortyTwoAN_539730534046940600385621601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187293 : Nat.totient 49655209132318535235477187293 = 31781223983721692289967718400 := by
  rw [← show ((([(3, 1), (31, 1), (139, 1), (1381, 1), (35747, 1), (10167809, 1), (7652554093, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187293 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_3, prime_fortyTwoAN_31, prime_fortyTwoAN_139, prime_fortyTwoAN_1381, prime_fortyTwoAN_35747, prime_fortyTwoAN_10167809, prime_fortyTwoAN_7652554093]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187294 : Nat.totient 49655209132318535235477187294 = 24165103886507228905746180000 := by
  rw [← show ((([(2, 1), (47, 1), (181, 1), (7601051, 1), (383958901408250471, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187294 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_2, prime_fortyTwoAN_47, prime_fortyTwoAN_181, prime_fortyTwoAN_7601051, prime_fortyTwoAN_383958901408250471]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187295 : Nat.totient 49655209132318535235477187295 = 37515701453233999204742400000 := by
  rw [← show ((([(5, 1), (19, 1), (701, 1), (1031, 1), (1361, 1), (531381464747383571, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187295 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_5, prime_fortyTwoAN_19, prime_fortyTwoAN_701, prime_fortyTwoAN_1031, prime_fortyTwoAN_1361, prime_fortyTwoAN_531381464747383571]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187296 : Nat.totient 49655209132318535235477187296 = 16339597154564897015566073856 := by
  rw [← show ((([(2, 5), (3, 1), (79, 1), (6229, 1), (8696692033, 1), (120863194567, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187296 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_2, prime_fortyTwoAN_3, prime_fortyTwoAN_79, prime_fortyTwoAN_6229, prime_fortyTwoAN_8696692033, prime_fortyTwoAN_120863194567]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187297 : Nat.totient 49655209132318535235477187297 = 49655209132317051785222295856 := by
  rw [← show ((([(34264205873333, 1), (1449186049018109, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187297 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_34264205873333, prime_fortyTwoAN_1449186049018109]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187298 : Nat.totient 49655209132318535235477187298 = 21251531304717083199877503456 := by
  rw [← show ((([(2, 1), (7, 2), (727, 1), (40346827, 1), (17274080639688469, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187298 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_2, prime_fortyTwoAN_7, prime_fortyTwoAN_727, prime_fortyTwoAN_40346827, prime_fortyTwoAN_17274080639688469]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187299 : Nat.totient 49655209132318535235477187299 = 30093863537635316044037003520 := by
  rw [← show ((([(3, 2), (11, 1), (148537, 1), (3376719396603664660873, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187299 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_3, prime_fortyTwoAN_11, prime_fortyTwoAN_148537, prime_fortyTwoAN_3376719396603664660873]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fortyTwoAN_49655209132318535235477187300 : Nat.totient 49655209132318535235477187300 = 19860011003998989023078309760 := by
  rw [← show ((([(2, 2), (5, 2), (12853, 1), (37663, 1), (1025759145018831907, 1)] : List FactorBlock).map factorBlockValue).prod) = 49655209132318535235477187300 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fortyTwoAN_2, prime_fortyTwoAN_5, prime_fortyTwoAN_12853, prime_fortyTwoAN_37663, prime_fortyTwoAN_1025759145018831907]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64FortyTwoAN : certifiedKill 1 49655209132318535235477187199 100 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_fortyTwoAN_49655209132318535235477187200, phi_fortyTwoAN_49655209132318535235477187201, phi_fortyTwoAN_49655209132318535235477187202,
    phi_fortyTwoAN_49655209132318535235477187203, phi_fortyTwoAN_49655209132318535235477187204, phi_fortyTwoAN_49655209132318535235477187205,
    phi_fortyTwoAN_49655209132318535235477187206, phi_fortyTwoAN_49655209132318535235477187207, phi_fortyTwoAN_49655209132318535235477187208,
    phi_fortyTwoAN_49655209132318535235477187209, phi_fortyTwoAN_49655209132318535235477187210, phi_fortyTwoAN_49655209132318535235477187211,
    phi_fortyTwoAN_49655209132318535235477187212, phi_fortyTwoAN_49655209132318535235477187213, phi_fortyTwoAN_49655209132318535235477187214,
    phi_fortyTwoAN_49655209132318535235477187215, phi_fortyTwoAN_49655209132318535235477187216, phi_fortyTwoAN_49655209132318535235477187217,
    phi_fortyTwoAN_49655209132318535235477187218, phi_fortyTwoAN_49655209132318535235477187219, phi_fortyTwoAN_49655209132318535235477187220,
    phi_fortyTwoAN_49655209132318535235477187221, phi_fortyTwoAN_49655209132318535235477187222, phi_fortyTwoAN_49655209132318535235477187223,
    phi_fortyTwoAN_49655209132318535235477187224, phi_fortyTwoAN_49655209132318535235477187225, phi_fortyTwoAN_49655209132318535235477187226,
    phi_fortyTwoAN_49655209132318535235477187227, phi_fortyTwoAN_49655209132318535235477187228, phi_fortyTwoAN_49655209132318535235477187229,
    phi_fortyTwoAN_49655209132318535235477187230, phi_fortyTwoAN_49655209132318535235477187231, phi_fortyTwoAN_49655209132318535235477187232,
    phi_fortyTwoAN_49655209132318535235477187233, phi_fortyTwoAN_49655209132318535235477187234, phi_fortyTwoAN_49655209132318535235477187235,
    phi_fortyTwoAN_49655209132318535235477187236, phi_fortyTwoAN_49655209132318535235477187237, phi_fortyTwoAN_49655209132318535235477187238,
    phi_fortyTwoAN_49655209132318535235477187239, phi_fortyTwoAN_49655209132318535235477187240, phi_fortyTwoAN_49655209132318535235477187241,
    phi_fortyTwoAN_49655209132318535235477187242, phi_fortyTwoAN_49655209132318535235477187243, phi_fortyTwoAN_49655209132318535235477187244,
    phi_fortyTwoAN_49655209132318535235477187245, phi_fortyTwoAN_49655209132318535235477187246, phi_fortyTwoAN_49655209132318535235477187247,
    phi_fortyTwoAN_49655209132318535235477187248, phi_fortyTwoAN_49655209132318535235477187249, phi_fortyTwoAN_49655209132318535235477187250,
    phi_fortyTwoAN_49655209132318535235477187251, phi_fortyTwoAN_49655209132318535235477187252, phi_fortyTwoAN_49655209132318535235477187253,
    phi_fortyTwoAN_49655209132318535235477187254, phi_fortyTwoAN_49655209132318535235477187255, phi_fortyTwoAN_49655209132318535235477187256,
    phi_fortyTwoAN_49655209132318535235477187257, phi_fortyTwoAN_49655209132318535235477187258, phi_fortyTwoAN_49655209132318535235477187259,
    phi_fortyTwoAN_49655209132318535235477187260, phi_fortyTwoAN_49655209132318535235477187261, phi_fortyTwoAN_49655209132318535235477187262,
    phi_fortyTwoAN_49655209132318535235477187263, phi_fortyTwoAN_49655209132318535235477187264, phi_fortyTwoAN_49655209132318535235477187265,
    phi_fortyTwoAN_49655209132318535235477187266, phi_fortyTwoAN_49655209132318535235477187267, phi_fortyTwoAN_49655209132318535235477187268,
    phi_fortyTwoAN_49655209132318535235477187269, phi_fortyTwoAN_49655209132318535235477187270, phi_fortyTwoAN_49655209132318535235477187271,
    phi_fortyTwoAN_49655209132318535235477187272, phi_fortyTwoAN_49655209132318535235477187273, phi_fortyTwoAN_49655209132318535235477187274,
    phi_fortyTwoAN_49655209132318535235477187275, phi_fortyTwoAN_49655209132318535235477187276, phi_fortyTwoAN_49655209132318535235477187277,
    phi_fortyTwoAN_49655209132318535235477187278, phi_fortyTwoAN_49655209132318535235477187279, phi_fortyTwoAN_49655209132318535235477187280,
    phi_fortyTwoAN_49655209132318535235477187281, phi_fortyTwoAN_49655209132318535235477187282, phi_fortyTwoAN_49655209132318535235477187283,
    phi_fortyTwoAN_49655209132318535235477187284, phi_fortyTwoAN_49655209132318535235477187285, phi_fortyTwoAN_49655209132318535235477187286,
    phi_fortyTwoAN_49655209132318535235477187287, phi_fortyTwoAN_49655209132318535235477187288, phi_fortyTwoAN_49655209132318535235477187289,
    phi_fortyTwoAN_49655209132318535235477187290, phi_fortyTwoAN_49655209132318535235477187291, phi_fortyTwoAN_49655209132318535235477187292,
    phi_fortyTwoAN_49655209132318535235477187293, phi_fortyTwoAN_49655209132318535235477187294, phi_fortyTwoAN_49655209132318535235477187295,
    phi_fortyTwoAN_49655209132318535235477187296, phi_fortyTwoAN_49655209132318535235477187297, phi_fortyTwoAN_49655209132318535235477187298,
    phi_fortyTwoAN_49655209132318535235477187299, phi_fortyTwoAN_49655209132318535235477187300
  ]

end TotientTailPeriodKiller
end Erdos249257
