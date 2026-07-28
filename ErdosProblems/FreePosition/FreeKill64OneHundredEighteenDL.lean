import Erdos249257.DiagonalPincerCertificatesT64

/- Kernel-checked off-diagonal certificate at a freely chosen position. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def oneHundredEighteenDLFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem oneHundredEighteenDLFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : oneHundredEighteenDLFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [oneHundredEighteenDLFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [oneHundredEighteenDLFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then oneHundredEighteenDLFastPow a n * oneHundredEighteenDLFastPow a n * a else oneHundredEighteenDLFastPow a n * oneHundredEighteenDLFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_oneHundredEighteenDL_2 : Nat.Prime 2 := by norm_num

private theorem prime_oneHundredEighteenDL_3 : Nat.Prime 3 := by norm_num

private theorem prime_oneHundredEighteenDL_5 : Nat.Prime 5 := by norm_num

private theorem prime_oneHundredEighteenDL_7 : Nat.Prime 7 := by norm_num

private theorem prime_oneHundredEighteenDL_11 : Nat.Prime 11 := by norm_num

private theorem prime_oneHundredEighteenDL_13 : Nat.Prime 13 := by norm_num

private theorem prime_oneHundredEighteenDL_17 : Nat.Prime 17 := by norm_num

private theorem prime_oneHundredEighteenDL_19 : Nat.Prime 19 := by norm_num

private theorem prime_oneHundredEighteenDL_23 : Nat.Prime 23 := by norm_num

private theorem prime_oneHundredEighteenDL_29 : Nat.Prime 29 := by norm_num

private theorem prime_oneHundredEighteenDL_31 : Nat.Prime 31 := by norm_num

private theorem prime_oneHundredEighteenDL_37 : Nat.Prime 37 := by norm_num

private theorem prime_oneHundredEighteenDL_41 : Nat.Prime 41 := by norm_num

private theorem prime_oneHundredEighteenDL_43 : Nat.Prime 43 := by norm_num

private theorem prime_oneHundredEighteenDL_47 : Nat.Prime 47 := by norm_num

private theorem prime_oneHundredEighteenDL_53 : Nat.Prime 53 := by norm_num

private theorem prime_oneHundredEighteenDL_59 : Nat.Prime 59 := by norm_num

private theorem prime_oneHundredEighteenDL_61 : Nat.Prime 61 := by norm_num

private theorem prime_oneHundredEighteenDL_67 : Nat.Prime 67 := by norm_num

private theorem prime_oneHundredEighteenDL_71 : Nat.Prime 71 := by norm_num

private theorem prime_oneHundredEighteenDL_73 : Nat.Prime 73 := by norm_num

private theorem prime_oneHundredEighteenDL_79 : Nat.Prime 79 := by norm_num

private theorem prime_oneHundredEighteenDL_83 : Nat.Prime 83 := by norm_num

private theorem prime_oneHundredEighteenDL_89 : Nat.Prime 89 := by norm_num

private theorem prime_oneHundredEighteenDL_97 : Nat.Prime 97 := by norm_num

private theorem prime_oneHundredEighteenDL_101 : Nat.Prime 101 := by norm_num

private theorem prime_oneHundredEighteenDL_103 : Nat.Prime 103 := by norm_num

private theorem prime_oneHundredEighteenDL_107 : Nat.Prime 107 := by norm_num

private theorem prime_oneHundredEighteenDL_109 : Nat.Prime 109 := by norm_num

private theorem prime_oneHundredEighteenDL_113 : Nat.Prime 113 := by norm_num

private theorem prime_oneHundredEighteenDL_127 : Nat.Prime 127 := by norm_num

private theorem prime_oneHundredEighteenDL_131 : Nat.Prime 131 := by norm_num

private theorem prime_oneHundredEighteenDL_137 : Nat.Prime 137 := by norm_num

private theorem prime_oneHundredEighteenDL_139 : Nat.Prime 139 := by norm_num

private theorem prime_oneHundredEighteenDL_149 : Nat.Prime 149 := by norm_num

private theorem prime_oneHundredEighteenDL_151 : Nat.Prime 151 := by norm_num

private theorem prime_oneHundredEighteenDL_157 : Nat.Prime 157 := by norm_num

private theorem prime_oneHundredEighteenDL_163 : Nat.Prime 163 := by norm_num

private theorem prime_oneHundredEighteenDL_167 : Nat.Prime 167 := by norm_num

private theorem prime_oneHundredEighteenDL_173 : Nat.Prime 173 := by norm_num

private theorem prime_oneHundredEighteenDL_181 : Nat.Prime 181 := by norm_num

private theorem prime_oneHundredEighteenDL_191 : Nat.Prime 191 := by norm_num

private theorem prime_oneHundredEighteenDL_193 : Nat.Prime 193 := by norm_num

private theorem prime_oneHundredEighteenDL_197 : Nat.Prime 197 := by norm_num

private theorem prime_oneHundredEighteenDL_211 : Nat.Prime 211 := by norm_num

private theorem prime_oneHundredEighteenDL_223 : Nat.Prime 223 := by norm_num

private theorem prime_oneHundredEighteenDL_227 : Nat.Prime 227 := by norm_num

private theorem prime_oneHundredEighteenDL_229 : Nat.Prime 229 := by norm_num

private theorem prime_oneHundredEighteenDL_233 : Nat.Prime 233 := by norm_num

private theorem prime_oneHundredEighteenDL_241 : Nat.Prime 241 := by norm_num

private theorem prime_oneHundredEighteenDL_251 : Nat.Prime 251 := by norm_num

private theorem prime_oneHundredEighteenDL_257 : Nat.Prime 257 := by norm_num

private theorem prime_oneHundredEighteenDL_263 : Nat.Prime 263 := by norm_num

private theorem prime_oneHundredEighteenDL_269 : Nat.Prime 269 := by norm_num

private theorem prime_oneHundredEighteenDL_271 : Nat.Prime 271 := by norm_num

private theorem prime_oneHundredEighteenDL_277 : Nat.Prime 277 := by norm_num

private theorem prime_oneHundredEighteenDL_281 : Nat.Prime 281 := by norm_num

private theorem prime_oneHundredEighteenDL_293 : Nat.Prime 293 := by norm_num

private theorem prime_oneHundredEighteenDL_307 : Nat.Prime 307 := by norm_num

private theorem prime_oneHundredEighteenDL_311 : Nat.Prime 311 := by norm_num

private theorem prime_oneHundredEighteenDL_313 : Nat.Prime 313 := by norm_num

private theorem prime_oneHundredEighteenDL_331 : Nat.Prime 331 := by norm_num

private theorem prime_oneHundredEighteenDL_337 : Nat.Prime 337 := by norm_num

private theorem prime_oneHundredEighteenDL_349 : Nat.Prime 349 := by norm_num

private theorem prime_oneHundredEighteenDL_353 : Nat.Prime 353 := by norm_num

private theorem prime_oneHundredEighteenDL_367 : Nat.Prime 367 := by norm_num

private theorem prime_oneHundredEighteenDL_373 : Nat.Prime 373 := by norm_num

private theorem prime_oneHundredEighteenDL_383 : Nat.Prime 383 := by norm_num

private theorem prime_oneHundredEighteenDL_401 : Nat.Prime 401 := by norm_num

private theorem prime_oneHundredEighteenDL_419 : Nat.Prime 419 := by norm_num

private theorem prime_oneHundredEighteenDL_421 : Nat.Prime 421 := by norm_num

private theorem prime_oneHundredEighteenDL_431 : Nat.Prime 431 := by norm_num

private theorem prime_oneHundredEighteenDL_433 : Nat.Prime 433 := by norm_num

private theorem prime_oneHundredEighteenDL_443 : Nat.Prime 443 := by norm_num

private theorem prime_oneHundredEighteenDL_449 : Nat.Prime 449 := by norm_num

private theorem prime_oneHundredEighteenDL_457 : Nat.Prime 457 := by norm_num

private theorem prime_oneHundredEighteenDL_461 : Nat.Prime 461 := by norm_num

private theorem prime_oneHundredEighteenDL_467 : Nat.Prime 467 := by norm_num

private theorem prime_oneHundredEighteenDL_479 : Nat.Prime 479 := by norm_num

private theorem prime_oneHundredEighteenDL_491 : Nat.Prime 491 := by norm_num

private theorem prime_oneHundredEighteenDL_499 : Nat.Prime 499 := by norm_num

private theorem prime_oneHundredEighteenDL_509 : Nat.Prime 509 := by norm_num

private theorem prime_oneHundredEighteenDL_521 : Nat.Prime 521 := by norm_num

private theorem prime_oneHundredEighteenDL_541 : Nat.Prime 541 := by norm_num

private theorem prime_oneHundredEighteenDL_557 : Nat.Prime 557 := by norm_num

private theorem prime_oneHundredEighteenDL_563 : Nat.Prime 563 := by norm_num

private theorem prime_oneHundredEighteenDL_569 : Nat.Prime 569 := by norm_num

private theorem prime_oneHundredEighteenDL_571 : Nat.Prime 571 := by norm_num

private theorem prime_oneHundredEighteenDL_613 : Nat.Prime 613 := by norm_num

private theorem prime_oneHundredEighteenDL_617 : Nat.Prime 617 := by norm_num

private theorem prime_oneHundredEighteenDL_619 : Nat.Prime 619 := by norm_num

private theorem prime_oneHundredEighteenDL_659 : Nat.Prime 659 := by norm_num

private theorem prime_oneHundredEighteenDL_701 : Nat.Prime 701 := by norm_num

private theorem prime_oneHundredEighteenDL_709 : Nat.Prime 709 := by norm_num

private theorem prime_oneHundredEighteenDL_727 : Nat.Prime 727 := by norm_num

private theorem prime_oneHundredEighteenDL_787 : Nat.Prime 787 := by norm_num

private theorem prime_oneHundredEighteenDL_811 : Nat.Prime 811 := by norm_num

private theorem prime_oneHundredEighteenDL_839 : Nat.Prime 839 := by norm_num

private theorem prime_oneHundredEighteenDL_863 : Nat.Prime 863 := by norm_num

private theorem prime_oneHundredEighteenDL_877 : Nat.Prime 877 := by norm_num

private theorem prime_oneHundredEighteenDL_881 : Nat.Prime 881 := by norm_num

private theorem prime_oneHundredEighteenDL_887 : Nat.Prime 887 := by norm_num

private theorem prime_oneHundredEighteenDL_919 : Nat.Prime 919 := by norm_num

private theorem prime_oneHundredEighteenDL_941 : Nat.Prime 941 := by norm_num

private theorem prime_oneHundredEighteenDL_947 : Nat.Prime 947 := by norm_num

private theorem prime_oneHundredEighteenDL_967 : Nat.Prime 967 := by norm_num

private theorem prime_oneHundredEighteenDL_977 : Nat.Prime 977 := by norm_num

private theorem prime_oneHundredEighteenDL_1019 : Nat.Prime 1019 := by norm_num

private theorem prime_oneHundredEighteenDL_1033 : Nat.Prime 1033 := by norm_num

private theorem prime_oneHundredEighteenDL_1093 : Nat.Prime 1093 := by norm_num

private theorem prime_oneHundredEighteenDL_1117 : Nat.Prime 1117 := by norm_num

private theorem prime_oneHundredEighteenDL_1301 : Nat.Prime 1301 := by norm_num

private theorem prime_oneHundredEighteenDL_1319 : Nat.Prime 1319 := by norm_num

private theorem prime_oneHundredEighteenDL_1321 : Nat.Prime 1321 := by norm_num

private theorem prime_oneHundredEighteenDL_1447 : Nat.Prime 1447 := by norm_num

private theorem prime_oneHundredEighteenDL_1481 : Nat.Prime 1481 := by norm_num

private theorem prime_oneHundredEighteenDL_1493 : Nat.Prime 1493 := by norm_num

private theorem prime_oneHundredEighteenDL_1499 : Nat.Prime 1499 := by norm_num

private theorem prime_oneHundredEighteenDL_1543 : Nat.Prime 1543 := by norm_num

private theorem prime_oneHundredEighteenDL_1553 : Nat.Prime 1553 := by norm_num

private theorem prime_oneHundredEighteenDL_1559 : Nat.Prime 1559 := by norm_num

private theorem prime_oneHundredEighteenDL_1583 : Nat.Prime 1583 := by norm_num

private theorem prime_oneHundredEighteenDL_1621 : Nat.Prime 1621 := by norm_num

private theorem prime_oneHundredEighteenDL_1669 : Nat.Prime 1669 := by norm_num

private theorem prime_oneHundredEighteenDL_1699 : Nat.Prime 1699 := by norm_num

private theorem prime_oneHundredEighteenDL_1789 : Nat.Prime 1789 := by norm_num

private theorem prime_oneHundredEighteenDL_1811 : Nat.Prime 1811 := by norm_num

private theorem prime_oneHundredEighteenDL_1931 : Nat.Prime 1931 := by norm_num

private theorem prime_oneHundredEighteenDL_1993 : Nat.Prime 1993 := by norm_num

private theorem prime_oneHundredEighteenDL_1997 : Nat.Prime 1997 := by norm_num

private theorem prime_oneHundredEighteenDL_1999 : Nat.Prime 1999 := by norm_num

private theorem prime_oneHundredEighteenDL_2039 : Nat.Prime 2039 := by norm_num

private theorem prime_oneHundredEighteenDL_2053 : Nat.Prime 2053 := by norm_num

private theorem prime_oneHundredEighteenDL_2063 : Nat.Prime 2063 := by norm_num

private theorem prime_oneHundredEighteenDL_2089 : Nat.Prime 2089 := by norm_num

private theorem prime_oneHundredEighteenDL_2113 : Nat.Prime 2113 := by norm_num

private theorem prime_oneHundredEighteenDL_2237 : Nat.Prime 2237 := by norm_num

private theorem prime_oneHundredEighteenDL_2267 : Nat.Prime 2267 := by norm_num

private theorem prime_oneHundredEighteenDL_2273 : Nat.Prime 2273 := by norm_num

private theorem prime_oneHundredEighteenDL_2297 : Nat.Prime 2297 := by norm_num

private theorem prime_oneHundredEighteenDL_2381 : Nat.Prime 2381 := by norm_num

private theorem prime_oneHundredEighteenDL_2393 : Nat.Prime 2393 := by norm_num

private theorem prime_oneHundredEighteenDL_2399 : Nat.Prime 2399 := by norm_num

private theorem prime_oneHundredEighteenDL_2423 : Nat.Prime 2423 := by norm_num

private theorem prime_oneHundredEighteenDL_2447 : Nat.Prime 2447 := by norm_num

private theorem prime_oneHundredEighteenDL_2503 : Nat.Prime 2503 := by norm_num

private theorem prime_oneHundredEighteenDL_2617 : Nat.Prime 2617 := by norm_num

private theorem prime_oneHundredEighteenDL_2647 : Nat.Prime 2647 := by norm_num

private theorem prime_oneHundredEighteenDL_2699 : Nat.Prime 2699 := by norm_num

private theorem prime_oneHundredEighteenDL_2719 : Nat.Prime 2719 := by norm_num

private theorem prime_oneHundredEighteenDL_2897 : Nat.Prime 2897 := by norm_num

private theorem prime_oneHundredEighteenDL_3001 : Nat.Prime 3001 := by norm_num

private theorem prime_oneHundredEighteenDL_3061 : Nat.Prime 3061 := by norm_num

private theorem prime_oneHundredEighteenDL_3169 : Nat.Prime 3169 := by norm_num

private theorem prime_oneHundredEighteenDL_3463 : Nat.Prime 3463 := by norm_num

private theorem prime_oneHundredEighteenDL_3593 : Nat.Prime 3593 := by norm_num

private theorem prime_oneHundredEighteenDL_3631 : Nat.Prime 3631 := by norm_num

private theorem prime_oneHundredEighteenDL_3673 : Nat.Prime 3673 := by norm_num

private theorem prime_oneHundredEighteenDL_3761 : Nat.Prime 3761 := by norm_num

private theorem prime_oneHundredEighteenDL_3767 : Nat.Prime 3767 := by norm_num

private theorem prime_oneHundredEighteenDL_3889 : Nat.Prime 3889 := by norm_num

private theorem prime_oneHundredEighteenDL_3989 : Nat.Prime 3989 := by norm_num

private theorem prime_oneHundredEighteenDL_4027 : Nat.Prime 4027 := by norm_num

private theorem prime_oneHundredEighteenDL_4157 : Nat.Prime 4157 := by norm_num

private theorem prime_oneHundredEighteenDL_4231 : Nat.Prime 4231 := by norm_num

private theorem prime_oneHundredEighteenDL_4241 : Nat.Prime 4241 := by norm_num

private theorem prime_oneHundredEighteenDL_4243 : Nat.Prime 4243 := by norm_num

private theorem prime_oneHundredEighteenDL_4349 : Nat.Prime 4349 := by norm_num

private theorem prime_oneHundredEighteenDL_4547 : Nat.Prime 4547 := by norm_num

private theorem prime_oneHundredEighteenDL_4583 : Nat.Prime 4583 := by norm_num

private theorem prime_oneHundredEighteenDL_4639 : Nat.Prime 4639 := by norm_num

private theorem prime_oneHundredEighteenDL_4657 : Nat.Prime 4657 := by norm_num

private theorem prime_oneHundredEighteenDL_4729 : Nat.Prime 4729 := by norm_num

private theorem prime_oneHundredEighteenDL_4909 : Nat.Prime 4909 := by norm_num

private theorem prime_oneHundredEighteenDL_4973 : Nat.Prime 4973 := by norm_num

private theorem prime_oneHundredEighteenDL_5051 : Nat.Prime 5051 := by norm_num

private theorem prime_oneHundredEighteenDL_5077 : Nat.Prime 5077 := by norm_num

private theorem prime_oneHundredEighteenDL_5119 : Nat.Prime 5119 := by norm_num

private theorem prime_oneHundredEighteenDL_5189 : Nat.Prime 5189 := by norm_num

private theorem prime_oneHundredEighteenDL_5227 : Nat.Prime 5227 := by norm_num

private theorem prime_oneHundredEighteenDL_5279 : Nat.Prime 5279 := by norm_num

private theorem prime_oneHundredEighteenDL_5323 : Nat.Prime 5323 := by norm_num

private theorem prime_oneHundredEighteenDL_5417 : Nat.Prime 5417 := by norm_num

private theorem prime_oneHundredEighteenDL_5623 : Nat.Prime 5623 := by norm_num

private theorem prime_oneHundredEighteenDL_5639 : Nat.Prime 5639 := by norm_num

private theorem prime_oneHundredEighteenDL_5653 : Nat.Prime 5653 := by norm_num

private theorem prime_oneHundredEighteenDL_5741 : Nat.Prime 5741 := by norm_num

private theorem prime_oneHundredEighteenDL_5749 : Nat.Prime 5749 := by norm_num

private theorem prime_oneHundredEighteenDL_5779 : Nat.Prime 5779 := by norm_num

private theorem prime_oneHundredEighteenDL_5801 : Nat.Prime 5801 := by norm_num

private theorem prime_oneHundredEighteenDL_5939 : Nat.Prime 5939 := by norm_num

private theorem prime_oneHundredEighteenDL_6113 : Nat.Prime 6113 := by norm_num

private theorem prime_oneHundredEighteenDL_6221 : Nat.Prime 6221 := by norm_num

private theorem prime_oneHundredEighteenDL_6229 : Nat.Prime 6229 := by norm_num

private theorem prime_oneHundredEighteenDL_6247 : Nat.Prime 6247 := by norm_num

private theorem prime_oneHundredEighteenDL_6269 : Nat.Prime 6269 := by norm_num

private theorem prime_oneHundredEighteenDL_6367 : Nat.Prime 6367 := by norm_num

private theorem prime_oneHundredEighteenDL_6569 : Nat.Prime 6569 := by norm_num

private theorem prime_oneHundredEighteenDL_6947 : Nat.Prime 6947 := by norm_num

private theorem prime_oneHundredEighteenDL_7507 : Nat.Prime 7507 := by norm_num

private theorem prime_oneHundredEighteenDL_7841 : Nat.Prime 7841 := by norm_num

private theorem prime_oneHundredEighteenDL_7927 : Nat.Prime 7927 := by norm_num

private theorem prime_oneHundredEighteenDL_8081 : Nat.Prime 8081 := by norm_num

private theorem prime_oneHundredEighteenDL_8273 : Nat.Prime 8273 := by norm_num

private theorem prime_oneHundredEighteenDL_8737 : Nat.Prime 8737 := by norm_num

private theorem prime_oneHundredEighteenDL_8887 : Nat.Prime 8887 := by norm_num

private theorem prime_oneHundredEighteenDL_8963 : Nat.Prime 8963 := by norm_num

private theorem prime_oneHundredEighteenDL_9029 : Nat.Prime 9029 := by norm_num

private theorem prime_oneHundredEighteenDL_9133 : Nat.Prime 9133 := by norm_num

private theorem prime_oneHundredEighteenDL_9203 : Nat.Prime 9203 := by norm_num

private theorem prime_oneHundredEighteenDL_9349 : Nat.Prime 9349 := by norm_num

private theorem prime_oneHundredEighteenDL_10691 : Nat.Prime 10691 := by norm_num

private theorem prime_oneHundredEighteenDL_11027 : Nat.Prime 11027 := by norm_num

private theorem prime_oneHundredEighteenDL_11213 : Nat.Prime 11213 := by norm_num

private theorem prime_oneHundredEighteenDL_11483 : Nat.Prime 11483 := by norm_num

private theorem prime_oneHundredEighteenDL_11489 : Nat.Prime 11489 := by norm_num

private theorem prime_oneHundredEighteenDL_12049 : Nat.Prime 12049 := by norm_num

private theorem prime_oneHundredEighteenDL_12347 : Nat.Prime 12347 := by norm_num

private theorem prime_oneHundredEighteenDL_12547 : Nat.Prime 12547 := by norm_num

private theorem prime_oneHundredEighteenDL_13381 : Nat.Prime 13381 := by norm_num

private theorem prime_oneHundredEighteenDL_15299 : Nat.Prime 15299 := by norm_num

private theorem prime_oneHundredEighteenDL_16417 : Nat.Prime 16417 := by norm_num

private theorem prime_oneHundredEighteenDL_16421 : Nat.Prime 16421 := by norm_num

private theorem prime_oneHundredEighteenDL_16619 : Nat.Prime 16619 := by norm_num

private theorem prime_oneHundredEighteenDL_17203 : Nat.Prime 17203 := by norm_num

private theorem prime_oneHundredEighteenDL_17491 : Nat.Prime 17491 := by norm_num

private theorem prime_oneHundredEighteenDL_17623 : Nat.Prime 17623 := by norm_num

private theorem prime_oneHundredEighteenDL_19739 : Nat.Prime 19739 := by norm_num

private theorem prime_oneHundredEighteenDL_20753 : Nat.Prime 20753 := by norm_num

private theorem prime_oneHundredEighteenDL_21577 : Nat.Prime 21577 := by norm_num

private theorem prime_oneHundredEighteenDL_22171 : Nat.Prime 22171 := by norm_num

private theorem prime_oneHundredEighteenDL_23071 : Nat.Prime 23071 := by norm_num

private theorem prime_oneHundredEighteenDL_23203 : Nat.Prime 23203 := by norm_num

private theorem prime_oneHundredEighteenDL_23873 : Nat.Prime 23873 := by norm_num

private theorem prime_oneHundredEighteenDL_24121 : Nat.Prime 24121 := by norm_num

private theorem prime_oneHundredEighteenDL_25073 : Nat.Prime 25073 := by norm_num

private theorem prime_oneHundredEighteenDL_25189 : Nat.Prime 25189 := by norm_num

private theorem prime_oneHundredEighteenDL_25373 : Nat.Prime 25373 := by norm_num

private theorem prime_oneHundredEighteenDL_25391 : Nat.Prime 25391 := by norm_num

private theorem prime_oneHundredEighteenDL_25561 : Nat.Prime 25561 := by norm_num

private theorem prime_oneHundredEighteenDL_25759 : Nat.Prime 25759 := by norm_num

private theorem prime_oneHundredEighteenDL_25913 : Nat.Prime 25913 := by norm_num

private theorem prime_oneHundredEighteenDL_26177 : Nat.Prime 26177 := by norm_num

private theorem prime_oneHundredEighteenDL_26371 : Nat.Prime 26371 := by norm_num

private theorem prime_oneHundredEighteenDL_26431 : Nat.Prime 26431 := by norm_num

private theorem prime_oneHundredEighteenDL_27529 : Nat.Prime 27529 := by norm_num

private theorem prime_oneHundredEighteenDL_28027 : Nat.Prime 28027 := by norm_num

private theorem prime_oneHundredEighteenDL_29411 : Nat.Prime 29411 := by norm_num

private theorem prime_oneHundredEighteenDL_29537 : Nat.Prime 29537 := by norm_num

private theorem prime_oneHundredEighteenDL_29803 : Nat.Prime 29803 := by norm_num

private theorem prime_oneHundredEighteenDL_33599 : Nat.Prime 33599 := by norm_num

private theorem prime_oneHundredEighteenDL_34501 : Nat.Prime 34501 := by norm_num

private theorem prime_oneHundredEighteenDL_37217 : Nat.Prime 37217 := by norm_num

private theorem prime_oneHundredEighteenDL_39161 : Nat.Prime 39161 := by norm_num

private theorem prime_oneHundredEighteenDL_40009 : Nat.Prime 40009 := by norm_num

private theorem prime_oneHundredEighteenDL_42569 : Nat.Prime 42569 := by norm_num

private theorem prime_oneHundredEighteenDL_43933 : Nat.Prime 43933 := by norm_num

private theorem prime_oneHundredEighteenDL_47317 : Nat.Prime 47317 := by norm_num

private theorem prime_oneHundredEighteenDL_47777 : Nat.Prime 47777 := by norm_num

private theorem prime_oneHundredEighteenDL_48017 : Nat.Prime 48017 := by norm_num

private theorem prime_oneHundredEighteenDL_48091 : Nat.Prime 48091 := by norm_num

private theorem prime_oneHundredEighteenDL_48767 : Nat.Prime 48767 := by norm_num

private theorem prime_oneHundredEighteenDL_51329 : Nat.Prime 51329 := by norm_num

private theorem prime_oneHundredEighteenDL_52103 : Nat.Prime 52103 := by norm_num

private theorem prime_oneHundredEighteenDL_52837 : Nat.Prime 52837 := by norm_num

private theorem prime_oneHundredEighteenDL_53161 : Nat.Prime 53161 := by norm_num

private theorem prime_oneHundredEighteenDL_53699 : Nat.Prime 53699 := by norm_num

private theorem prime_oneHundredEighteenDL_53887 : Nat.Prime 53887 := by norm_num

private theorem prime_oneHundredEighteenDL_57571 : Nat.Prime 57571 := by norm_num

private theorem prime_oneHundredEighteenDL_62297 : Nat.Prime 62297 := by norm_num

private theorem prime_oneHundredEighteenDL_62761 : Nat.Prime 62761 := by norm_num

private theorem prime_oneHundredEighteenDL_66617 : Nat.Prime 66617 := by norm_num

private theorem prime_oneHundredEighteenDL_68111 : Nat.Prime 68111 := by norm_num

private theorem prime_oneHundredEighteenDL_69997 : Nat.Prime 69997 := by norm_num

private theorem prime_oneHundredEighteenDL_70373 : Nat.Prime 70373 := by norm_num

private theorem prime_oneHundredEighteenDL_73019 : Nat.Prime 73019 := by norm_num

private theorem prime_oneHundredEighteenDL_74411 : Nat.Prime 74411 := by norm_num

private theorem prime_oneHundredEighteenDL_77621 : Nat.Prime 77621 := by norm_num

private theorem prime_oneHundredEighteenDL_78721 : Nat.Prime 78721 := by norm_num

private theorem prime_oneHundredEighteenDL_87629 : Nat.Prime 87629 := by norm_num

private theorem prime_oneHundredEighteenDL_87641 : Nat.Prime 87641 := by norm_num

private theorem prime_oneHundredEighteenDL_89137 : Nat.Prime 89137 := by norm_num

private theorem prime_oneHundredEighteenDL_90407 : Nat.Prime 90407 := by norm_num

private theorem prime_oneHundredEighteenDL_102359 : Nat.Prime 102359 := by norm_num

private theorem prime_oneHundredEighteenDL_104417 : Nat.Prime 104417 := by norm_num

private theorem prime_oneHundredEighteenDL_110491 : Nat.Prime 110491 := by norm_num

private theorem prime_oneHundredEighteenDL_117709 : Nat.Prime 117709 := by norm_num

private theorem prime_oneHundredEighteenDL_120539 : Nat.Prime 120539 := by norm_num

private theorem prime_oneHundredEighteenDL_120943 : Nat.Prime 120943 := by norm_num

private theorem prime_oneHundredEighteenDL_126233 : Nat.Prime 126233 := by norm_num

private theorem prime_oneHundredEighteenDL_131893 : Nat.Prime 131893 := by norm_num

private theorem prime_oneHundredEighteenDL_140227 : Nat.Prime 140227 := by norm_num

private theorem prime_oneHundredEighteenDL_141619 : Nat.Prime 141619 := by norm_num

private theorem prime_oneHundredEighteenDL_160813 : Nat.Prime 160813 := by norm_num

private theorem prime_oneHundredEighteenDL_171401 : Nat.Prime 171401 := by norm_num

private theorem prime_oneHundredEighteenDL_192263 : Nat.Prime 192263 := by norm_num

private theorem prime_oneHundredEighteenDL_202621 : Nat.Prime 202621 := by norm_num

private theorem prime_oneHundredEighteenDL_205847 : Nat.Prime 205847 := by norm_num

private theorem prime_oneHundredEighteenDL_210709 : Nat.Prime 210709 := by norm_num

private theorem prime_oneHundredEighteenDL_238213 : Nat.Prime 238213 := by norm_num

private theorem prime_oneHundredEighteenDL_240473 : Nat.Prime 240473 := by norm_num

private theorem prime_oneHundredEighteenDL_241663 : Nat.Prime 241663 := by norm_num

private theorem prime_oneHundredEighteenDL_245257 : Nat.Prime 245257 := by norm_num

private theorem prime_oneHundredEighteenDL_247603 : Nat.Prime 247603 := by norm_num

private theorem prime_oneHundredEighteenDL_255179 : Nat.Prime 255179 := by norm_num

private theorem prime_oneHundredEighteenDL_270619 : Nat.Prime 270619 := by norm_num

private theorem prime_oneHundredEighteenDL_277331 : Nat.Prime 277331 := by norm_num

private theorem prime_oneHundredEighteenDL_280223 : Nat.Prime 280223 := by norm_num

private theorem prime_oneHundredEighteenDL_291007 : Nat.Prime 291007 := by norm_num

private theorem prime_oneHundredEighteenDL_298369 : Nat.Prime 298369 := by norm_num

private theorem prime_oneHundredEighteenDL_326141 : Nat.Prime 326141 := by norm_num

private theorem prime_oneHundredEighteenDL_333497 : Nat.Prime 333497 := by norm_num

private theorem prime_oneHundredEighteenDL_338717 : Nat.Prime 338717 := by norm_num

private theorem prime_oneHundredEighteenDL_348247 : Nat.Prime 348247 := by norm_num

private theorem prime_oneHundredEighteenDL_359407 : Nat.Prime 359407 := by norm_num

private theorem prime_oneHundredEighteenDL_365929 : Nat.Prime 365929 := by norm_num

private theorem prime_oneHundredEighteenDL_369991 : Nat.Prime 369991 := by norm_num

private theorem prime_oneHundredEighteenDL_372149 : Nat.Prime 372149 := by norm_num

private theorem prime_oneHundredEighteenDL_376603 : Nat.Prime 376603 := by norm_num

private theorem prime_oneHundredEighteenDL_379033 : Nat.Prime 379033 := by norm_num

private theorem prime_oneHundredEighteenDL_384599 : Nat.Prime 384599 := by norm_num

private theorem prime_oneHundredEighteenDL_393209 : Nat.Prime 393209 := by norm_num

private theorem prime_oneHundredEighteenDL_405401 : Nat.Prime 405401 := by norm_num

private theorem prime_oneHundredEighteenDL_428339 : Nat.Prime 428339 := by norm_num

private theorem prime_oneHundredEighteenDL_484373 : Nat.Prime 484373 := by norm_num

private theorem prime_oneHundredEighteenDL_484769 : Nat.Prime 484769 := by norm_num

private theorem prime_oneHundredEighteenDL_514313 : Nat.Prime 514313 := by norm_num

private theorem prime_oneHundredEighteenDL_519307 : Nat.Prime 519307 := by norm_num

private theorem prime_oneHundredEighteenDL_573557 : Nat.Prime 573557 := by norm_num

private theorem prime_oneHundredEighteenDL_577097 : Nat.Prime 577097 := by norm_num

private theorem prime_oneHundredEighteenDL_594403 : Nat.Prime 594403 := by norm_num

private theorem prime_oneHundredEighteenDL_599959 : Nat.Prime 599959 := by norm_num

private theorem prime_oneHundredEighteenDL_643493 : Nat.Prime 643493 := by norm_num

private theorem prime_oneHundredEighteenDL_647771 : Nat.Prime 647771 := by norm_num

private theorem prime_oneHundredEighteenDL_654107 : Nat.Prime 654107 := by norm_num

private theorem prime_oneHundredEighteenDL_674761 : Nat.Prime 674761 := by norm_num

private theorem prime_oneHundredEighteenDL_708667 : Nat.Prime 708667 := by norm_num

private theorem prime_oneHundredEighteenDL_753197 : Nat.Prime 753197 := by norm_num

private theorem prime_oneHundredEighteenDL_771389 : Nat.Prime 771389 := by norm_num

private theorem prime_oneHundredEighteenDL_857977 : Nat.Prime 857977 := by norm_num

private theorem prime_oneHundredEighteenDL_885427 : Nat.Prime 885427 := by norm_num

private theorem prime_oneHundredEighteenDL_946901 : Nat.Prime 946901 := by norm_num

private theorem prime_oneHundredEighteenDL_956051 : Nat.Prime 956051 := by norm_num

private theorem prime_oneHundredEighteenDL_958319 : Nat.Prime 958319 := by norm_num

private theorem prime_oneHundredEighteenDL_1038601 : Nat.Prime 1038601 := by norm_num

private theorem prime_oneHundredEighteenDL_1040657 : Nat.Prime 1040657 := by norm_num

private theorem prime_oneHundredEighteenDL_1041619 : Nat.Prime 1041619 := by norm_num

private theorem prime_oneHundredEighteenDL_1054853 : Nat.Prime 1054853 := by norm_num

private theorem prime_oneHundredEighteenDL_1204447 : Nat.Prime 1204447 := by norm_num

private theorem prime_oneHundredEighteenDL_1210819 : Nat.Prime 1210819 := by norm_num

private theorem prime_oneHundredEighteenDL_1300031 : Nat.Prime 1300031 := by norm_num

private theorem prime_oneHundredEighteenDL_1330237 : Nat.Prime 1330237 := by norm_num

private theorem prime_oneHundredEighteenDL_1342181 : Nat.Prime 1342181 := by norm_num

private theorem prime_oneHundredEighteenDL_1386223 : Nat.Prime 1386223 := by norm_num

private theorem prime_oneHundredEighteenDL_1692541 : Nat.Prime 1692541 := by norm_num

private theorem prime_oneHundredEighteenDL_1719701 : Nat.Prime 1719701 := by norm_num

private theorem prime_oneHundredEighteenDL_1756187 : Nat.Prime 1756187 := by norm_num

private theorem prime_oneHundredEighteenDL_1765087 : Nat.Prime 1765087 := by norm_num

private theorem prime_oneHundredEighteenDL_1854497 : Nat.Prime 1854497 := by norm_num

private theorem prime_oneHundredEighteenDL_1883551 : Nat.Prime 1883551 := by norm_num

private theorem prime_oneHundredEighteenDL_1920227 : Nat.Prime 1920227 := by norm_num

private theorem prime_oneHundredEighteenDL_2031691 : Nat.Prime 2031691 := by norm_num

private theorem prime_oneHundredEighteenDL_2126303 : Nat.Prime 2126303 := by norm_num

private theorem prime_oneHundredEighteenDL_2132539 : Nat.Prime 2132539 := by norm_num

private theorem prime_oneHundredEighteenDL_2164963 : Nat.Prime 2164963 := by norm_num

private theorem prime_oneHundredEighteenDL_2261269 : Nat.Prime 2261269 := by norm_num

private theorem prime_oneHundredEighteenDL_2442151 : Nat.Prime 2442151 := by norm_num

private theorem prime_oneHundredEighteenDL_2511793 : Nat.Prime 2511793 := by norm_num

private theorem prime_oneHundredEighteenDL_2531369 : Nat.Prime 2531369 := by norm_num

private theorem prime_oneHundredEighteenDL_3037079 : Nat.Prime 3037079 := by norm_num

private theorem prime_oneHundredEighteenDL_3160127 : Nat.Prime 3160127 := by norm_num

private theorem prime_oneHundredEighteenDL_3243341 : Nat.Prime 3243341 := by norm_num

private theorem prime_oneHundredEighteenDL_3251093 : Nat.Prime 3251093 := by norm_num

private theorem prime_oneHundredEighteenDL_3568463 : Nat.Prime 3568463 := by norm_num

private theorem prime_oneHundredEighteenDL_3948149 : Nat.Prime 3948149 := by norm_num

private theorem prime_oneHundredEighteenDL_4291589 : Nat.Prime 4291589 := by norm_num

private theorem prime_oneHundredEighteenDL_5820797 : Nat.Prime 5820797 := by norm_num

private theorem prime_oneHundredEighteenDL_5871911 : Nat.Prime 5871911 := by norm_num

private theorem prime_oneHundredEighteenDL_5983283 : Nat.Prime 5983283 := by norm_num

private theorem prime_oneHundredEighteenDL_6692759 : Nat.Prime 6692759 := by norm_num

private theorem prime_oneHundredEighteenDL_6899579 : Nat.Prime 6899579 := by norm_num

private theorem prime_oneHundredEighteenDL_8055661 : Nat.Prime 8055661 := by norm_num

private theorem prime_oneHundredEighteenDL_8373229 : Nat.Prime 8373229 := by norm_num

private theorem prime_oneHundredEighteenDL_8796187 : Nat.Prime 8796187 := by norm_num

private theorem prime_oneHundredEighteenDL_8990497 : Nat.Prime 8990497 := by norm_num

private theorem prime_oneHundredEighteenDL_9543029 : Nat.Prime 9543029 := by norm_num

private theorem prime_oneHundredEighteenDL_10756099 : Nat.Prime 10756099 := by norm_num

private theorem prime_oneHundredEighteenDL_10820141 : Nat.Prime 10820141 := by norm_num

private theorem prime_oneHundredEighteenDL_10934939 : Nat.Prime 10934939 := by norm_num

private theorem prime_oneHundredEighteenDL_11210851 : Nat.Prime 11210851 := by norm_num

private theorem prime_oneHundredEighteenDL_11247409 : Nat.Prime 11247409 := by norm_num

private theorem prime_oneHundredEighteenDL_11756551 : Nat.Prime 11756551 := by norm_num

private theorem prime_oneHundredEighteenDL_12058873 : Nat.Prime 12058873 := by norm_num

private theorem prime_oneHundredEighteenDL_13360231 : Nat.Prime 13360231 := by norm_num

private theorem prime_oneHundredEighteenDL_14060239 : Nat.Prime 14060239 := by norm_num

private theorem prime_oneHundredEighteenDL_14163089 : Nat.Prime 14163089 := by norm_num

private theorem prime_oneHundredEighteenDL_14525981 : Nat.Prime 14525981 := by norm_num

private theorem prime_oneHundredEighteenDL_14794849 : Nat.Prime 14794849 := by norm_num

private theorem prime_oneHundredEighteenDL_17113051 : Nat.Prime 17113051 := by norm_num

private theorem prime_oneHundredEighteenDL_17401051 : Nat.Prime 17401051 := by norm_num

private theorem prime_oneHundredEighteenDL_18039583 : Nat.Prime 18039583 := by norm_num

private theorem prime_oneHundredEighteenDL_18316537 : Nat.Prime 18316537 := by norm_num

private theorem prime_oneHundredEighteenDL_18884839 : Nat.Prime 18884839 := by norm_num

private theorem prime_oneHundredEighteenDL_20256823 : Nat.Prime 20256823 := by norm_num

private theorem prime_oneHundredEighteenDL_20998583 : Nat.Prime 20998583 := by norm_num

private theorem prime_oneHundredEighteenDL_21355949 : Nat.Prime 21355949 := by norm_num

private theorem prime_oneHundredEighteenDL_21520069 : Nat.Prime 21520069 := by norm_num

private theorem prime_oneHundredEighteenDL_24570551 : Nat.Prime 24570551 := by norm_num

private theorem prime_oneHundredEighteenDL_24903817 : Nat.Prime 24903817 := by norm_num

private theorem prime_oneHundredEighteenDL_25912303 : Nat.Prime 25912303 := by norm_num

private theorem prime_oneHundredEighteenDL_27683219 : Nat.Prime 27683219 := by norm_num

private theorem prime_oneHundredEighteenDL_28906673 : Nat.Prime 28906673 := by norm_num

private theorem prime_oneHundredEighteenDL_29281061 : Nat.Prime 29281061 := by norm_num

private theorem prime_oneHundredEighteenDL_29591819 : Nat.Prime 29591819 := by norm_num

private theorem prime_oneHundredEighteenDL_31585193 : Nat.Prime 31585193 := by
  apply lucas_primality 31585193 (3 : ZMod 31585193)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3948149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3948149, 1)] : List FactorBlock).map factorBlockValue).prod) = 31585193 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3948149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 31585193) ^ 15792596 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 31585193) ^ 8 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_31922857 : Nat.Prime 31922857 := by
  apply lucas_primality 31922857 (20 : ZMod 31922857)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (7, 1), (43, 1), (491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (7, 1), (43, 1), (491, 1)] : List FactorBlock).map factorBlockValue).prod) = 31922857 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_7
      · exact prime_oneHundredEighteenDL_43
      · exact prime_oneHundredEighteenDL_491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (20 : ZMod 31922857) ^ 15961428 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (20 : ZMod 31922857) ^ 10640952 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (20 : ZMod 31922857) ^ 4560408 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (20 : ZMod 31922857) ^ 742392 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (20 : ZMod 31922857) ^ 65016 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_32459123 : Nat.Prime 32459123 := by
  apply lucas_primality 32459123 (2 : ZMod 32459123)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (157, 1), (167, 1), (619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (157, 1), (167, 1), (619, 1)] : List FactorBlock).map factorBlockValue).prod) = 32459123 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_157
      · exact prime_oneHundredEighteenDL_167
      · exact prime_oneHundredEighteenDL_619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 32459123) ^ 16229561 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 32459123) ^ 206746 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 32459123) ^ 194366 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 32459123) ^ 52438 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_33940681 : Nat.Prime 33940681 := by
  apply lucas_primality 33940681 (13 : ZMod 33940681)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (113, 1), (2503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (113, 1), (2503, 1)] : List FactorBlock).map factorBlockValue).prod) = 33940681 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_5
      · exact prime_oneHundredEighteenDL_113
      · exact prime_oneHundredEighteenDL_2503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 33940681) ^ 16970340 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (13 : ZMod 33940681) ^ 11313560 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (13 : ZMod 33940681) ^ 6788136 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (13 : ZMod 33940681) ^ 300360 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (13 : ZMod 33940681) ^ 13560 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_35240221 : Nat.Prime 35240221 := by
  apply lucas_primality 35240221 (2 : ZMod 35240221)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (29, 1), (43, 1), (157, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (29, 1), (43, 1), (157, 1)] : List FactorBlock).map factorBlockValue).prod) = 35240221 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_5
      · exact prime_oneHundredEighteenDL_29
      · exact prime_oneHundredEighteenDL_43
      · exact prime_oneHundredEighteenDL_157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 35240221) ^ 17620110 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 35240221) ^ 11746740 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 35240221) ^ 7048044 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 35240221) ^ 1215180 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 35240221) ^ 819540 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 35240221) ^ 224460 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_41287261 : Nat.Prime 41287261 := by
  apply lucas_primality 41287261 (2 : ZMod 41287261)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (197, 1), (499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (197, 1), (499, 1)] : List FactorBlock).map factorBlockValue).prod) = 41287261 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_5
      · exact prime_oneHundredEighteenDL_7
      · exact prime_oneHundredEighteenDL_197
      · exact prime_oneHundredEighteenDL_499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 41287261) ^ 20643630 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 41287261) ^ 13762420 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 41287261) ^ 8257452 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 41287261) ^ 5898180 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 41287261) ^ 209580 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 41287261) ^ 82740 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_41701007 : Nat.Prime 41701007 := by
  apply lucas_primality 41701007 (5 : ZMod 41701007)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3989, 1), (5227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3989, 1), (5227, 1)] : List FactorBlock).map factorBlockValue).prod) = 41701007 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3989
      · exact prime_oneHundredEighteenDL_5227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 41701007) ^ 20850503 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 41701007) ^ 10454 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 41701007) ^ 7978 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_42330181 : Nat.Prime 42330181 := by
  apply lucas_primality 42330181 (6 : ZMod 42330181)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (89, 1), (7927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (89, 1), (7927, 1)] : List FactorBlock).map factorBlockValue).prod) = 42330181 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_5
      · exact prime_oneHundredEighteenDL_89
      · exact prime_oneHundredEighteenDL_7927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 42330181) ^ 21165090 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (6 : ZMod 42330181) ^ 14110060 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (6 : ZMod 42330181) ^ 8466036 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (6 : ZMod 42330181) ^ 475620 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (6 : ZMod 42330181) ^ 5340 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_47099851 : Nat.Prime 47099851 := by
  apply lucas_primality 47099851 (7 : ZMod 47099851)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (7, 1), (31, 1), (1447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (7, 1), (31, 1), (1447, 1)] : List FactorBlock).map factorBlockValue).prod) = 47099851 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_5
      · exact prime_oneHundredEighteenDL_7
      · exact prime_oneHundredEighteenDL_31
      · exact prime_oneHundredEighteenDL_1447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 47099851) ^ 23549925 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (7 : ZMod 47099851) ^ 15699950 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (7 : ZMod 47099851) ^ 9419970 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (7 : ZMod 47099851) ^ 6728550 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (7 : ZMod 47099851) ^ 1519350 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (7 : ZMod 47099851) ^ 32550 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_49919581 : Nat.Prime 49919581 := by
  apply lucas_primality 49919581 (7 : ZMod 49919581)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (277331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (277331, 1)] : List FactorBlock).map factorBlockValue).prod) = 49919581 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_5
      · exact prime_oneHundredEighteenDL_277331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 49919581) ^ 24959790 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (7 : ZMod 49919581) ^ 16639860 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (7 : ZMod 49919581) ^ 9983916 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (7 : ZMod 49919581) ^ 180 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_53942983 : Nat.Prime 53942983 := by
  apply lucas_primality 53942983 (3 : ZMod 53942983)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (8990497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (8990497, 1)] : List FactorBlock).map factorBlockValue).prod) = 53942983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_8990497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 53942983) ^ 26971491 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 53942983) ^ 17980994 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 53942983) ^ 6 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_55875667 : Nat.Prime 55875667 := by
  apply lucas_primality 55875667 (3 : ZMod 55875667)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (11, 1), (120943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (11, 1), (120943, 1)] : List FactorBlock).map factorBlockValue).prod) = 55875667 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_7
      · exact prime_oneHundredEighteenDL_11
      · exact prime_oneHundredEighteenDL_120943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 55875667) ^ 27937833 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 55875667) ^ 18625222 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 55875667) ^ 7982238 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 55875667) ^ 5079606 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 55875667) ^ 462 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_59649929 : Nat.Prime 59649929 := by
  apply lucas_primality 59649929 (3 : ZMod 59649929)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (573557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (573557, 1)] : List FactorBlock).map factorBlockValue).prod) = 59649929 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_13
      · exact prime_oneHundredEighteenDL_573557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 59649929) ^ 29824964 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 59649929) ^ 4588456 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 59649929) ^ 104 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_59929613 : Nat.Prime 59929613 := by
  apply lucas_primality 59929613 (2 : ZMod 59929613)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1811, 1), (8273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1811, 1), (8273, 1)] : List FactorBlock).map factorBlockValue).prod) = 59929613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_1811
      · exact prime_oneHundredEighteenDL_8273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 59929613) ^ 29964806 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 59929613) ^ 33092 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 59929613) ^ 7244 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_61961981 : Nat.Prime 61961981 := by
  apply lucas_primality 61961981 (2 : ZMod 61961981)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (29, 1), (47, 1), (2273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (29, 1), (47, 1), (2273, 1)] : List FactorBlock).map factorBlockValue).prod) = 61961981 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_5
      · exact prime_oneHundredEighteenDL_29
      · exact prime_oneHundredEighteenDL_47
      · exact prime_oneHundredEighteenDL_2273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 61961981) ^ 30980990 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 61961981) ^ 12392396 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 61961981) ^ 2136620 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 61961981) ^ 1318340 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 61961981) ^ 27260 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_64965493 : Nat.Prime 64965493 := by
  apply lucas_primality 64965493 (2 : ZMod 64965493)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (53, 1), (79, 1), (431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (53, 1), (79, 1), (431, 1)] : List FactorBlock).map factorBlockValue).prod) = 64965493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_53
      · exact prime_oneHundredEighteenDL_79
      · exact prime_oneHundredEighteenDL_431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 64965493) ^ 32482746 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 64965493) ^ 21655164 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 64965493) ^ 1225764 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 64965493) ^ 822348 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 64965493) ^ 150732 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_75361057 : Nat.Prime 75361057 := by
  apply lucas_primality 75361057 (5 : ZMod 75361057)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (113, 1), (6947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (113, 1), (6947, 1)] : List FactorBlock).map factorBlockValue).prod) = 75361057 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_113
      · exact prime_oneHundredEighteenDL_6947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 75361057) ^ 37680528 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 75361057) ^ 25120352 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 75361057) ^ 666912 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 75361057) ^ 10848 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_82370699 : Nat.Prime 82370699 := by
  apply lucas_primality 82370699 (2 : ZMod 82370699)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3673, 1), (11213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3673, 1), (11213, 1)] : List FactorBlock).map factorBlockValue).prod) = 82370699 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3673
      · exact prime_oneHundredEighteenDL_11213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 82370699) ^ 41185349 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 82370699) ^ 22426 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 82370699) ^ 7346 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_83431813 : Nat.Prime 83431813 := by
  apply lucas_primality 83431813 (5 : ZMod 83431813)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (365929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (365929, 1)] : List FactorBlock).map factorBlockValue).prod) = 83431813 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_19
      · exact prime_oneHundredEighteenDL_365929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 83431813) ^ 41715906 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 83431813) ^ 27810604 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 83431813) ^ 4391148 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 83431813) ^ 228 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_89971993 : Nat.Prime 89971993 := by
  apply lucas_primality 89971993 (5 : ZMod 89971993)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (11, 1), (19, 1), (1993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (11, 1), (19, 1), (1993, 1)] : List FactorBlock).map factorBlockValue).prod) = 89971993 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_11
      · exact prime_oneHundredEighteenDL_19
      · exact prime_oneHundredEighteenDL_1993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 89971993) ^ 44985996 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 89971993) ^ 29990664 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 89971993) ^ 8179272 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 89971993) ^ 4735368 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 89971993) ^ 45144 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_96409217 : Nat.Prime 96409217 := by
  apply lucas_primality 96409217 (3 : ZMod 96409217)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (753197, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (753197, 1)] : List FactorBlock).map factorBlockValue).prod) = 96409217 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_753197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 96409217) ^ 48204608 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 96409217) ^ 128 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_108098663 : Nat.Prime 108098663 := by
  apply lucas_primality 108098663 (5 : ZMod 108098663)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (2053, 1), (3761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (2053, 1), (3761, 1)] : List FactorBlock).map factorBlockValue).prod) = 108098663 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_7
      · exact prime_oneHundredEighteenDL_2053
      · exact prime_oneHundredEighteenDL_3761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 108098663) ^ 54049331 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 108098663) ^ 15442666 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 108098663) ^ 52654 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 108098663) ^ 28742 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_123923963 : Nat.Prime 123923963 := by
  apply lucas_primality 123923963 (2 : ZMod 123923963)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (61961981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (61961981, 1)] : List FactorBlock).map factorBlockValue).prod) = 123923963 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_61961981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 123923963) ^ 61961981 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 123923963) ^ 2 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_128849377 : Nat.Prime 128849377 := by
  apply lucas_primality 128849377 (5 : ZMod 128849377)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (1342181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (1342181, 1)] : List FactorBlock).map factorBlockValue).prod) = 128849377 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_1342181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 128849377) ^ 64424688 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 128849377) ^ 42949792 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 128849377) ^ 96 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_138779393 : Nat.Prime 138779393 := by
  apply lucas_primality 138779393 (3 : ZMod 138779393)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (61, 1), (8887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (61, 1), (8887, 1)] : List FactorBlock).map factorBlockValue).prod) = 138779393 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_61
      · exact prime_oneHundredEighteenDL_8887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 138779393) ^ 69389696 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 138779393) ^ 2275072 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 138779393) ^ 15616 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_145030441 : Nat.Prime 145030441 := by
  apply lucas_primality 145030441 (7 : ZMod 145030441)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (349, 1), (3463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (349, 1), (3463, 1)] : List FactorBlock).map factorBlockValue).prod) = 145030441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_5
      · exact prime_oneHundredEighteenDL_349
      · exact prime_oneHundredEighteenDL_3463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 145030441) ^ 72515220 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (7 : ZMod 145030441) ^ 48343480 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (7 : ZMod 145030441) ^ 29006088 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (7 : ZMod 145030441) ^ 415560 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (7 : ZMod 145030441) ^ 41880 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_146137543 : Nat.Prime 146137543 := by
  apply lucas_primality 146137543 (5 : ZMod 146137543)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (919, 1), (1559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (919, 1), (1559, 1)] : List FactorBlock).map factorBlockValue).prod) = 146137543 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_17
      · exact prime_oneHundredEighteenDL_919
      · exact prime_oneHundredEighteenDL_1559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 146137543) ^ 73068771 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 146137543) ^ 48712514 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 146137543) ^ 8596326 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 146137543) ^ 159018 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 146137543) ^ 93738 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_179491561 : Nat.Prime 179491561 := by
  apply lucas_primality 179491561 (13 : ZMod 179491561)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (281, 1), (5323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (281, 1), (5323, 1)] : List FactorBlock).map factorBlockValue).prod) = 179491561 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_5
      · exact prime_oneHundredEighteenDL_281
      · exact prime_oneHundredEighteenDL_5323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 179491561) ^ 89745780 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (13 : ZMod 179491561) ^ 59830520 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (13 : ZMod 179491561) ^ 35898312 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (13 : ZMod 179491561) ^ 638760 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (13 : ZMod 179491561) ^ 33720 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_190896269 : Nat.Prime 190896269 := by
  apply lucas_primality 190896269 (2 : ZMod 190896269)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (2511793, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (2511793, 1)] : List FactorBlock).map factorBlockValue).prod) = 190896269 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_19
      · exact prime_oneHundredEighteenDL_2511793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 190896269) ^ 95448134 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 190896269) ^ 10047172 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 190896269) ^ 76 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_194754739 : Nat.Prime 194754739 := by
  apply lucas_primality 194754739 (2 : ZMod 194754739)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (32459123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (32459123, 1)] : List FactorBlock).map factorBlockValue).prod) = 194754739 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_32459123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 194754739) ^ 97377369 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 194754739) ^ 64918246 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 194754739) ^ 6 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_202568231 : Nat.Prime 202568231 := by
  apply lucas_primality 202568231 (13 : ZMod 202568231)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (20256823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (20256823, 1)] : List FactorBlock).map factorBlockValue).prod) = 202568231 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_5
      · exact prime_oneHundredEighteenDL_20256823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 202568231) ^ 101284115 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (13 : ZMod 202568231) ^ 40513646 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (13 : ZMod 202568231) ^ 10 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_208812613 : Nat.Prime 208812613 := by
  apply lucas_primality 208812613 (6 : ZMod 208812613)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17401051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17401051, 1)] : List FactorBlock).map factorBlockValue).prod) = 208812613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_17401051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 208812613) ^ 104406306 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (6 : ZMod 208812613) ^ 69604204 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (6 : ZMod 208812613) ^ 12 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_215214047 : Nat.Prime 215214047 := by
  apply lucas_primality 215214047 (5 : ZMod 215214047)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (877, 1), (4231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (877, 1), (4231, 1)] : List FactorBlock).map factorBlockValue).prod) = 215214047 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_29
      · exact prime_oneHundredEighteenDL_877
      · exact prime_oneHundredEighteenDL_4231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 215214047) ^ 107607023 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 215214047) ^ 7421174 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 215214047) ^ 245398 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 215214047) ^ 50866 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_226618069 : Nat.Prime 226618069 := by
  apply lucas_primality 226618069 (6 : ZMod 226618069)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (18884839, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (18884839, 1)] : List FactorBlock).map factorBlockValue).prod) = 226618069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_18884839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 226618069) ^ 113309034 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (6 : ZMod 226618069) ^ 75539356 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (6 : ZMod 226618069) ^ 12 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_231017117 : Nat.Prime 231017117 := by
  apply lucas_primality 231017117 (2 : ZMod 231017117)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (1931, 1), (2719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (1931, 1), (2719, 1)] : List FactorBlock).map factorBlockValue).prod) = 231017117 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_11
      · exact prime_oneHundredEighteenDL_1931
      · exact prime_oneHundredEighteenDL_2719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 231017117) ^ 115508558 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 231017117) ^ 21001556 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 231017117) ^ 119636 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 231017117) ^ 84964 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_234078697 : Nat.Prime 234078697 := by
  apply lucas_primality 234078697 (13 : ZMod 234078697)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (3251093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (3251093, 1)] : List FactorBlock).map factorBlockValue).prod) = 234078697 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_3251093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 234078697) ^ 117039348 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (13 : ZMod 234078697) ^ 78026232 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (13 : ZMod 234078697) ^ 72 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_315017711 : Nat.Prime 315017711 := by
  apply lucas_primality 315017711 (7 : ZMod 315017711)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (151, 1), (29803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (151, 1), (29803, 1)] : List FactorBlock).map factorBlockValue).prod) = 315017711 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_5
      · exact prime_oneHundredEighteenDL_7
      · exact prime_oneHundredEighteenDL_151
      · exact prime_oneHundredEighteenDL_29803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 315017711) ^ 157508855 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (7 : ZMod 315017711) ^ 63003542 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (7 : ZMod 315017711) ^ 45002530 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (7 : ZMod 315017711) ^ 2086210 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (7 : ZMod 315017711) ^ 10570 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_327442069 : Nat.Prime 327442069 := by
  apply lucas_primality 327442069 (2 : ZMod 327442069)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (127, 1), (23873, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (127, 1), (23873, 1)] : List FactorBlock).map factorBlockValue).prod) = 327442069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_127
      · exact prime_oneHundredEighteenDL_23873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 327442069) ^ 163721034 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 327442069) ^ 109147356 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 327442069) ^ 2578284 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 327442069) ^ 13716 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_367174909 : Nat.Prime 367174909 := by
  apply lucas_primality 367174909 (6 : ZMod 367174909)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (17, 1), (599959, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (17, 1), (599959, 1)] : List FactorBlock).map factorBlockValue).prod) = 367174909 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_17
      · exact prime_oneHundredEighteenDL_599959
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 367174909) ^ 183587454 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (6 : ZMod 367174909) ^ 122391636 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (6 : ZMod 367174909) ^ 21598524 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (6 : ZMod 367174909) ^ 612 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_394103803 : Nat.Prime 394103803 := by
  apply lucas_primality 394103803 (3 : ZMod 394103803)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1543, 1), (42569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1543, 1), (42569, 1)] : List FactorBlock).map factorBlockValue).prod) = 394103803 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_1543
      · exact prime_oneHundredEighteenDL_42569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 394103803) ^ 197051901 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 394103803) ^ 131367934 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 394103803) ^ 255414 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 394103803) ^ 9258 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_434194219 : Nat.Prime 434194219 := by
  apply lucas_primality 434194219 (2 : ZMod 434194219)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (61, 1), (73, 1), (5417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (61, 1), (73, 1), (5417, 1)] : List FactorBlock).map factorBlockValue).prod) = 434194219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_61
      · exact prime_oneHundredEighteenDL_73
      · exact prime_oneHundredEighteenDL_5417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 434194219) ^ 217097109 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 434194219) ^ 144731406 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 434194219) ^ 7117938 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 434194219) ^ 5947866 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 434194219) ^ 80154 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_603610541 : Nat.Prime 603610541 := by
  apply lucas_primality 603610541 (2 : ZMod 603610541)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (13, 2), (107, 1), (1669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (13, 2), (107, 1), (1669, 1)] : List FactorBlock).map factorBlockValue).prod) = 603610541 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_5
      · exact prime_oneHundredEighteenDL_13
      · exact prime_oneHundredEighteenDL_107
      · exact prime_oneHundredEighteenDL_1669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 603610541) ^ 301805270 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 603610541) ^ 120722108 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 603610541) ^ 46431580 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 603610541) ^ 5641220 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 603610541) ^ 361660 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_618015611 : Nat.Prime 618015611 := by
  apply lucas_primality 618015611 (2 : ZMod 618015611)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (257, 1), (240473, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (257, 1), (240473, 1)] : List FactorBlock).map factorBlockValue).prod) = 618015611 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_5
      · exact prime_oneHundredEighteenDL_257
      · exact prime_oneHundredEighteenDL_240473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 618015611) ^ 309007805 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 618015611) ^ 123603122 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 618015611) ^ 2404730 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 618015611) ^ 2570 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_714027719 : Nat.Prime 714027719 := by
  apply lucas_primality 714027719 (11 : ZMod 714027719)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) = 714027719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_17203
      · exact prime_oneHundredEighteenDL_20753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 714027719) ^ 357013859 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 41506 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 34406 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_732653863 : Nat.Prime 732653863 := by
  apply lucas_primality 732653863 (3 : ZMod 732653863)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (193, 1), (37217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (193, 1), (37217, 1)] : List FactorBlock).map factorBlockValue).prod) = 732653863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_17
      · exact prime_oneHundredEighteenDL_193
      · exact prime_oneHundredEighteenDL_37217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 732653863) ^ 366326931 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 732653863) ^ 244217954 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 732653863) ^ 43097286 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 732653863) ^ 3796134 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 732653863) ^ 19686 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_802015873 : Nat.Prime 802015873 := by
  apply lucas_primality 802015873 (5 : ZMod 802015873)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (7, 1), (298369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (7, 1), (298369, 1)] : List FactorBlock).map factorBlockValue).prod) = 802015873 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_7
      · exact prime_oneHundredEighteenDL_298369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 802015873) ^ 401007936 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 802015873) ^ 267338624 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 802015873) ^ 114573696 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 802015873) ^ 2688 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_808190039 : Nat.Prime 808190039 := by
  apply lucas_primality 808190039 (13 : ZMod 808190039)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (37, 1), (376603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (37, 1), (376603, 1)] : List FactorBlock).map factorBlockValue).prod) = 808190039 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_29
      · exact prime_oneHundredEighteenDL_37
      · exact prime_oneHundredEighteenDL_376603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 808190039) ^ 404095019 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (13 : ZMod 808190039) ^ 27868622 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (13 : ZMod 808190039) ^ 21842974 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (13 : ZMod 808190039) ^ 2146 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_832676359 : Nat.Prime 832676359 := by
  apply lucas_primality 832676359 (3 : ZMod 832676359)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (138779393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (138779393, 1)] : List FactorBlock).map factorBlockValue).prod) = 832676359 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_138779393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 832676359) ^ 416338179 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 832676359) ^ 277558786 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 832676359) ^ 6 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_840249461 : Nat.Prime 840249461 := by
  apply lucas_primality 840249461 (2 : ZMod 840249461)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (1499, 1), (28027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (1499, 1), (28027, 1)] : List FactorBlock).map factorBlockValue).prod) = 840249461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_5
      · exact prime_oneHundredEighteenDL_1499
      · exact prime_oneHundredEighteenDL_28027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 840249461) ^ 420124730 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 840249461) ^ 168049892 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 840249461) ^ 560540 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 840249461) ^ 29980 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_884539837 : Nat.Prime 884539837 := by
  apply lucas_primality 884539837 (6 : ZMod 884539837)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (24570551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (24570551, 1)] : List FactorBlock).map factorBlockValue).prod) = 884539837 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_24570551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 884539837) ^ 442269918 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (6 : ZMod 884539837) ^ 294846612 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (6 : ZMod 884539837) ^ 36 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_964425391 : Nat.Prime 964425391 := by
  apply lucas_primality 964425391 (3 : ZMod 964425391)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (227, 1), (141619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (227, 1), (141619, 1)] : List FactorBlock).map factorBlockValue).prod) = 964425391 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_5
      · exact prime_oneHundredEighteenDL_227
      · exact prime_oneHundredEighteenDL_141619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 964425391) ^ 482212695 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 964425391) ^ 321475130 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 964425391) ^ 192885078 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 964425391) ^ 4248570 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 964425391) ^ 6810 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_1060765831 : Nat.Prime 1060765831 := by
  apply lucas_primality 1060765831 (3 : ZMod 1060765831)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (17, 3), (2399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (17, 3), (2399, 1)] : List FactorBlock).map factorBlockValue).prod) = 1060765831 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_5
      · exact prime_oneHundredEighteenDL_17
      · exact prime_oneHundredEighteenDL_2399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1060765831) ^ 530382915 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 1060765831) ^ 353588610 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 1060765831) ^ 212153166 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 1060765831) ^ 62397990 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 1060765831) ^ 442170 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_1106744731 : Nat.Prime 1106744731 := by
  apply lucas_primality 1106744731 (7 : ZMod 1106744731)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (13, 1), (405401, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (13, 1), (405401, 1)] : List FactorBlock).map factorBlockValue).prod) = 1106744731 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_5
      · exact prime_oneHundredEighteenDL_7
      · exact prime_oneHundredEighteenDL_13
      · exact prime_oneHundredEighteenDL_405401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1106744731) ^ 553372365 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (7 : ZMod 1106744731) ^ 368914910 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (7 : ZMod 1106744731) ^ 221348946 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (7 : ZMod 1106744731) ^ 158106390 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (7 : ZMod 1106744731) ^ 85134210 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (7 : ZMod 1106744731) ^ 2730 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_1172258369 : Nat.Prime 1172258369 := by
  apply lucas_primality 1172258369 (3 : ZMod 1172258369)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (18316537, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (18316537, 1)] : List FactorBlock).map factorBlockValue).prod) = 1172258369 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_18316537
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 1172258369) ^ 586129184 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 1172258369) ^ 64 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_1298849977 : Nat.Prime 1298849977 := by
  apply lucas_primality 1298849977 (7 : ZMod 1298849977)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (18039583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (18039583, 1)] : List FactorBlock).map factorBlockValue).prod) = 1298849977 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_18039583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 1298849977) ^ 649424988 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (7 : ZMod 1298849977) ^ 432949992 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (7 : ZMod 1298849977) ^ 72 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_1306339753 : Nat.Prime 1306339753 := by
  apply lucas_primality 1306339753 (5 : ZMod 1306339753)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (31, 1), (881, 1), (1993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (31, 1), (881, 1), (1993, 1)] : List FactorBlock).map factorBlockValue).prod) = 1306339753 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_31
      · exact prime_oneHundredEighteenDL_881
      · exact prime_oneHundredEighteenDL_1993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1306339753) ^ 653169876 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 1306339753) ^ 435446584 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 1306339753) ^ 42139992 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 1306339753) ^ 1482792 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 1306339753) ^ 655464 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_1397964901 : Nat.Prime 1397964901 := by
  apply lucas_primality 1397964901 (10 : ZMod 1397964901)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (19, 1), (245257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (19, 1), (245257, 1)] : List FactorBlock).map factorBlockValue).prod) = 1397964901 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_5
      · exact prime_oneHundredEighteenDL_19
      · exact prime_oneHundredEighteenDL_245257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 1397964901) ^ 698982450 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (10 : ZMod 1397964901) ^ 465988300 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (10 : ZMod 1397964901) ^ 279592980 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (10 : ZMod 1397964901) ^ 73577100 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (10 : ZMod 1397964901) ^ 5700 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_1636712029 : Nat.Prime 1636712029 := by
  apply lucas_primality 1636712029 (10 : ZMod 1636712029)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (7, 1), (2164963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (7, 1), (2164963, 1)] : List FactorBlock).map factorBlockValue).prod) = 1636712029 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_7
      · exact prime_oneHundredEighteenDL_2164963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 1636712029) ^ 818356014 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (10 : ZMod 1636712029) ^ 545570676 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (10 : ZMod 1636712029) ^ 233816004 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (10 : ZMod 1636712029) ^ 756 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_1680498923 : Nat.Prime 1680498923 := by
  apply lucas_primality 1680498923 (2 : ZMod 1680498923)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (840249461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (840249461, 1)] : List FactorBlock).map factorBlockValue).prod) = 1680498923 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_840249461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 1680498923) ^ 840249461 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1680498923) ^ 2 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_1925936203 : Nat.Prime 1925936203 := by
  apply lucas_primality 1925936203 (5 : ZMod 1925936203)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (43, 1), (47, 1), (71, 1), (2237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (43, 1), (47, 1), (71, 1), (2237, 1)] : List FactorBlock).map factorBlockValue).prod) = 1925936203 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_43
      · exact prime_oneHundredEighteenDL_47
      · exact prime_oneHundredEighteenDL_71
      · exact prime_oneHundredEighteenDL_2237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1925936203) ^ 962968101 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 1925936203) ^ 641978734 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 1925936203) ^ 44789214 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 1925936203) ^ 40977366 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 1925936203) ^ 27125862 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 1925936203) ^ 860946 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_2128883969 : Nat.Prime 2128883969 := by
  apply lucas_primality 2128883969 (3 : ZMod 2128883969)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (29, 1), (139, 1), (2063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (29, 1), (139, 1), (2063, 1)] : List FactorBlock).map factorBlockValue).prod) = 2128883969 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_29
      · exact prime_oneHundredEighteenDL_139
      · exact prime_oneHundredEighteenDL_2063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2128883969) ^ 1064441984 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 2128883969) ^ 73409792 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 2128883969) ^ 15315712 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 2128883969) ^ 1031936 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_2240084947 : Nat.Prime 2240084947 := by
  apply lucas_primality 2240084947 (3 : ZMod 2240084947)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (33940681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (33940681, 1)] : List FactorBlock).map factorBlockValue).prod) = 2240084947 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_11
      · exact prime_oneHundredEighteenDL_33940681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2240084947) ^ 1120042473 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 2240084947) ^ 746694982 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 2240084947) ^ 203644086 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 2240084947) ^ 66 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_2267198501 : Nat.Prime 2267198501 := by
  apply lucas_primality 2267198501 (2 : ZMod 2267198501)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 3), (7, 1), (647771, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 3), (7, 1), (647771, 1)] : List FactorBlock).map factorBlockValue).prod) = 2267198501 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_5
      · exact prime_oneHundredEighteenDL_7
      · exact prime_oneHundredEighteenDL_647771
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2267198501) ^ 1133599250 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 2267198501) ^ 453439700 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 2267198501) ^ 323885500 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 2267198501) ^ 3500 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_2655950567 : Nat.Prime 2655950567 := by
  apply lucas_primality 2655950567 (5 : ZMod 2655950567)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (257, 1), (659, 1), (7841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (257, 1), (659, 1), (7841, 1)] : List FactorBlock).map factorBlockValue).prod) = 2655950567 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_257
      · exact prime_oneHundredEighteenDL_659
      · exact prime_oneHundredEighteenDL_7841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2655950567) ^ 1327975283 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 2655950567) ^ 10334438 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 2655950567) ^ 4030274 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 2655950567) ^ 338726 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_2785506599 : Nat.Prime 2785506599 := by
  apply lucas_primality 2785506599 (7 : ZMod 2785506599)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (4973, 1), (40009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (4973, 1), (40009, 1)] : List FactorBlock).map factorBlockValue).prod) = 2785506599 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_7
      · exact prime_oneHundredEighteenDL_4973
      · exact prime_oneHundredEighteenDL_40009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 2785506599) ^ 1392753299 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (7 : ZMod 2785506599) ^ 397929514 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (7 : ZMod 2785506599) ^ 560126 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (7 : ZMod 2785506599) ^ 69622 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_3149956679 : Nat.Prime 3149956679 := by
  apply lucas_primality 3149956679 (11 : ZMod 3149956679)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (5639, 1), (25391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (5639, 1), (25391, 1)] : List FactorBlock).map factorBlockValue).prod) = 3149956679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_11
      · exact prime_oneHundredEighteenDL_5639
      · exact prime_oneHundredEighteenDL_25391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 3149956679) ^ 1574978339 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (11 : ZMod 3149956679) ^ 286359698 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (11 : ZMod 3149956679) ^ 558602 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (11 : ZMod 3149956679) ^ 124058 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_3436726747 : Nat.Prime 3436726747 := by
  apply lucas_primality 3436726747 (3 : ZMod 3436726747)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (24903817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (24903817, 1)] : List FactorBlock).map factorBlockValue).prod) = 3436726747 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_23
      · exact prime_oneHundredEighteenDL_24903817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3436726747) ^ 1718363373 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 3436726747) ^ 1145575582 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 3436726747) ^ 149422902 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 3436726747) ^ 138 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_4031927483 : Nat.Prime 4031927483 := by
  apply lucas_primality 4031927483 (2 : ZMod 4031927483)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (269, 1), (401, 1), (1699, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (269, 1), (401, 1), (1699, 1)] : List FactorBlock).map factorBlockValue).prod) = 4031927483 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_11
      · exact prime_oneHundredEighteenDL_269
      · exact prime_oneHundredEighteenDL_401
      · exact prime_oneHundredEighteenDL_1699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4031927483) ^ 2015963741 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 4031927483) ^ 366538862 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 4031927483) ^ 14988578 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 4031927483) ^ 10054682 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 4031927483) ^ 2373118 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_4107295811 : Nat.Prime 4107295811 := by
  apply lucas_primality 4107295811 (10 : ZMod 4107295811)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (29, 1), (14163089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (29, 1), (14163089, 1)] : List FactorBlock).map factorBlockValue).prod) = 4107295811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_5
      · exact prime_oneHundredEighteenDL_29
      · exact prime_oneHundredEighteenDL_14163089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 4107295811) ^ 2053647905 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (10 : ZMod 4107295811) ^ 821459162 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (10 : ZMod 4107295811) ^ 141630890 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (10 : ZMod 4107295811) ^ 290 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_4158320863 : Nat.Prime 4158320863 := by
  apply lucas_primality 4158320863 (3 : ZMod 4158320863)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (521, 1), (1330237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (521, 1), (1330237, 1)] : List FactorBlock).map factorBlockValue).prod) = 4158320863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_521
      · exact prime_oneHundredEighteenDL_1330237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4158320863) ^ 2079160431 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 4158320863) ^ 1386106954 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 4158320863) ^ 7981422 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 4158320863) ^ 3126 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_4349810189 : Nat.Prime 4349810189 := by
  apply lucas_primality 4349810189 (2 : ZMod 4349810189)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (97, 1), (11210851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (97, 1), (11210851, 1)] : List FactorBlock).map factorBlockValue).prod) = 4349810189 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_97
      · exact prime_oneHundredEighteenDL_11210851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4349810189) ^ 2174905094 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 4349810189) ^ 44843404 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 4349810189) ^ 388 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_5138366503 : Nat.Prime 5138366503 := by
  apply lucas_primality 5138366503 (3 : ZMod 5138366503)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (271, 1), (3160127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (271, 1), (3160127, 1)] : List FactorBlock).map factorBlockValue).prod) = 5138366503 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_271
      · exact prime_oneHundredEighteenDL_3160127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 5138366503) ^ 2569183251 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 5138366503) ^ 1712788834 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 5138366503) ^ 18960762 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 5138366503) ^ 1626 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_6037638679 : Nat.Prime 6037638679 := by
  apply lucas_primality 6037638679 (3 : ZMod 6037638679)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) = 6037638679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_31
      · exact prime_oneHundredEighteenDL_10820141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6037638679) ^ 3018819339 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 2012546226 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 194762538 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 558 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_6090079717 : Nat.Prime 6090079717 := by
  apply lucas_primality 6090079717 (17 : ZMod 6090079717)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (7, 1), (8055661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (7, 1), (8055661, 1)] : List FactorBlock).map factorBlockValue).prod) = 6090079717 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_7
      · exact prime_oneHundredEighteenDL_8055661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 6090079717) ^ 3045039858 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (17 : ZMod 6090079717) ^ 2030026572 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (17 : ZMod 6090079717) ^ 870011388 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (17 : ZMod 6090079717) ^ 756 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_7446730517 : Nat.Prime 7446730517 := by
  apply lucas_primality 7446730517 (2 : ZMod 7446730517)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (421, 1), (192263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (421, 1), (192263, 1)] : List FactorBlock).map factorBlockValue).prod) = 7446730517 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_23
      · exact prime_oneHundredEighteenDL_421
      · exact prime_oneHundredEighteenDL_192263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7446730517) ^ 3723365258 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 7446730517) ^ 323770892 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 7446730517) ^ 17688196 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 7446730517) ^ 38732 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_7795194553 : Nat.Prime 7795194553 := by
  apply lucas_primality 7795194553 (5 : ZMod 7795194553)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (17, 1), (251, 1), (25373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (17, 1), (251, 1), (25373, 1)] : List FactorBlock).map factorBlockValue).prod) = 7795194553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_17
      · exact prime_oneHundredEighteenDL_251
      · exact prime_oneHundredEighteenDL_25373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 7795194553) ^ 3897597276 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 7795194553) ^ 2598398184 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 7795194553) ^ 458540856 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 7795194553) ^ 31056552 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 7795194553) ^ 307224 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_8268339533 : Nat.Prime 8268339533 := by
  apply lucas_primality 8268339533 (2 : ZMod 8268339533)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (37, 1), (59, 1), (946901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (37, 1), (59, 1), (946901, 1)] : List FactorBlock).map factorBlockValue).prod) = 8268339533 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_37
      · exact prime_oneHundredEighteenDL_59
      · exact prime_oneHundredEighteenDL_946901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 8268339533) ^ 4134169766 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 8268339533) ^ 223468636 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 8268339533) ^ 140141348 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 8268339533) ^ 8732 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_9587552111 : Nat.Prime 9587552111 := by
  apply lucas_primality 9587552111 (11 : ZMod 9587552111)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (37, 1), (25912303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (37, 1), (25912303, 1)] : List FactorBlock).map factorBlockValue).prod) = 9587552111 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_5
      · exact prime_oneHundredEighteenDL_37
      · exact prime_oneHundredEighteenDL_25912303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 9587552111) ^ 4793776055 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (11 : ZMod 9587552111) ^ 1917510422 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (11 : ZMod 9587552111) ^ 259123030 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (11 : ZMod 9587552111) ^ 370 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_9698280469 : Nat.Prime 9698280469 := by
  apply lucas_primality 9698280469 (6 : ZMod 9698280469)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (808190039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (808190039, 1)] : List FactorBlock).map factorBlockValue).prod) = 9698280469 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_808190039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 9698280469) ^ 4849140234 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (6 : ZMod 9698280469) ^ 3232760156 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (6 : ZMod 9698280469) ^ 12 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_11413453853 : Nat.Prime 11413453853 := by
  apply lucas_primality 11413453853 (2 : ZMod 11413453853)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (1699, 1), (73019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (1699, 1), (73019, 1)] : List FactorBlock).map factorBlockValue).prod) = 11413453853 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_23
      · exact prime_oneHundredEighteenDL_1699
      · exact prime_oneHundredEighteenDL_73019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 11413453853) ^ 5706726926 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 11413453853) ^ 496237124 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 11413453853) ^ 6717748 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 11413453853) ^ 156308 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_11539955681 : Nat.Prime 11539955681 := by
  apply lucas_primality 11539955681 (6 : ZMod 11539955681)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (11, 1), (571, 1), (11483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (11, 1), (571, 1), (11483, 1)] : List FactorBlock).map factorBlockValue).prod) = 11539955681 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_5
      · exact prime_oneHundredEighteenDL_11
      · exact prime_oneHundredEighteenDL_571
      · exact prime_oneHundredEighteenDL_11483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 11539955681) ^ 5769977840 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (6 : ZMod 11539955681) ^ 2307991136 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (6 : ZMod 11539955681) ^ 1049086880 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (6 : ZMod 11539955681) ^ 20210080 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (6 : ZMod 11539955681) ^ 1004960 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_11892496163 : Nat.Prime 11892496163 := by
  apply lucas_primality 11892496163 (2 : ZMod 11892496163)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (145030441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (145030441, 1)] : List FactorBlock).map factorBlockValue).prod) = 11892496163 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_41
      · exact prime_oneHundredEighteenDL_145030441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 11892496163) ^ 5946248081 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 11892496163) ^ 290060882 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 11892496163) ^ 82 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_12575621651 : Nat.Prime 12575621651 := by
  apply lucas_primality 12575621651 (2 : ZMod 12575621651)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (17, 1), (14794849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (17, 1), (14794849, 1)] : List FactorBlock).map factorBlockValue).prod) = 12575621651 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_5
      · exact prime_oneHundredEighteenDL_17
      · exact prime_oneHundredEighteenDL_14794849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 12575621651) ^ 6287810825 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 12575621651) ^ 2515124330 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 12575621651) ^ 739742450 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 12575621651) ^ 850 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_13220061457 : Nat.Prime 13220061457 := by
  apply lucas_primality 13220061457 (5 : ZMod 13220061457)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (7, 1), (449, 1), (87629, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (7, 1), (449, 1), (87629, 1)] : List FactorBlock).map factorBlockValue).prod) = 13220061457 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_7
      · exact prime_oneHundredEighteenDL_449
      · exact prime_oneHundredEighteenDL_87629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 13220061457) ^ 6610030728 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 13220061457) ^ 4406687152 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 13220061457) ^ 1888580208 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 13220061457) ^ 29443344 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 13220061457) ^ 150864 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_15743760127 : Nat.Prime 15743760127 := by
  apply lucas_primality 15743760127 (3 : ZMod 15743760127)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (6229, 1), (22171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (6229, 1), (22171, 1)] : List FactorBlock).map factorBlockValue).prod) = 15743760127 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_19
      · exact prime_oneHundredEighteenDL_6229
      · exact prime_oneHundredEighteenDL_22171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 15743760127) ^ 7871880063 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 15743760127) ^ 5247920042 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 15743760127) ^ 828618954 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 15743760127) ^ 2527494 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 15743760127) ^ 710106 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_16785869363 : Nat.Prime 16785869363 := by
  apply lucas_primality 16785869363 (2 : ZMod 16785869363)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (8081, 1), (1038601, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (8081, 1), (1038601, 1)] : List FactorBlock).map factorBlockValue).prod) = 16785869363 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_8081
      · exact prime_oneHundredEighteenDL_1038601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 16785869363) ^ 8392934681 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 16785869363) ^ 2077202 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 16785869363) ^ 16162 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_16870678009 : Nat.Prime 16870678009 := by
  apply lucas_primality 16870678009 (19 : ZMod 16870678009)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (17, 1), (167, 1), (247603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (17, 1), (167, 1), (247603, 1)] : List FactorBlock).map factorBlockValue).prod) = 16870678009 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_17
      · exact prime_oneHundredEighteenDL_167
      · exact prime_oneHundredEighteenDL_247603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 16870678009) ^ 8435339004 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (19 : ZMod 16870678009) ^ 5623559336 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (19 : ZMod 16870678009) ^ 992392824 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (19 : ZMod 16870678009) ^ 101022024 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (19 : ZMod 16870678009) ^ 68136 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_17228377109 : Nat.Prime 17228377109 := by
  apply lucas_primality 17228377109 (2 : ZMod 17228377109)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (149, 1), (28906673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (149, 1), (28906673, 1)] : List FactorBlock).map factorBlockValue).prod) = 17228377109 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_149
      · exact prime_oneHundredEighteenDL_28906673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 17228377109) ^ 8614188554 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 17228377109) ^ 115626692 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 17228377109) ^ 596 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_18805667849 : Nat.Prime 18805667849 := by
  apply lucas_primality 18805667849 (3 : ZMod 18805667849)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (19, 1), (11247409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (19, 1), (11247409, 1)] : List FactorBlock).map factorBlockValue).prod) = 18805667849 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_11
      · exact prime_oneHundredEighteenDL_19
      · exact prime_oneHundredEighteenDL_11247409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 18805667849) ^ 9402833924 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 18805667849) ^ 1709606168 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 18805667849) ^ 989771992 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 18805667849) ^ 1672 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_21357468337 : Nat.Prime 21357468337 := by
  apply lucas_primality 21357468337 (10 : ZMod 21357468337)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (4027, 1), (110491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (4027, 1), (110491, 1)] : List FactorBlock).map factorBlockValue).prod) = 21357468337 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_4027
      · exact prime_oneHundredEighteenDL_110491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 21357468337) ^ 10678734168 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (10 : ZMod 21357468337) ^ 7119156112 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (10 : ZMod 21357468337) ^ 5303568 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (10 : ZMod 21357468337) ^ 193296 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_22142553649 : Nat.Prime 22142553649 := by
  apply lucas_primality 22142553649 (7 : ZMod 22142553649)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (383, 1), (1204447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (383, 1), (1204447, 1)] : List FactorBlock).map factorBlockValue).prod) = 22142553649 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_383
      · exact prime_oneHundredEighteenDL_1204447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 22142553649) ^ 11071276824 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (7 : ZMod 22142553649) ^ 7380851216 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (7 : ZMod 22142553649) ^ 57813456 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (7 : ZMod 22142553649) ^ 18384 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_22284052793 : Nat.Prime 22284052793 := by
  apply lucas_primality 22284052793 (3 : ZMod 22284052793)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (2785506599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (2785506599, 1)] : List FactorBlock).map factorBlockValue).prod) = 22284052793 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_2785506599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 22284052793) ^ 11142026396 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 22284052793) ^ 8 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_22643170001 : Nat.Prime 22643170001 := by
  apply lucas_primality 22643170001 (6 : ZMod 22643170001)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 4), (11, 1), (205847, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 4), (11, 1), (205847, 1)] : List FactorBlock).map factorBlockValue).prod) = 22643170001 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_5
      · exact prime_oneHundredEighteenDL_11
      · exact prime_oneHundredEighteenDL_205847
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 22643170001) ^ 11321585000 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (6 : ZMod 22643170001) ^ 4528634000 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (6 : ZMod 22643170001) ^ 2058470000 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (6 : ZMod 22643170001) ^ 110000 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_24191564899 : Nat.Prime 24191564899 := by
  apply lucas_primality 24191564899 (2 : ZMod 24191564899)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (4031927483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (4031927483, 1)] : List FactorBlock).map factorBlockValue).prod) = 24191564899 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_4031927483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 24191564899) ^ 12095782449 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 24191564899) ^ 8063854966 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 24191564899) ^ 6 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_28087332431 : Nat.Prime 28087332431 := by
  apply lucas_primality 28087332431 (11 : ZMod 28087332431)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (2699, 1), (1040657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (2699, 1), (1040657, 1)] : List FactorBlock).map factorBlockValue).prod) = 28087332431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_5
      · exact prime_oneHundredEighteenDL_2699
      · exact prime_oneHundredEighteenDL_1040657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 28087332431) ^ 14043666215 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (11 : ZMod 28087332431) ^ 5617466486 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (11 : ZMod 28087332431) ^ 10406570 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (11 : ZMod 28087332431) ^ 26990 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_32523200639 : Nat.Prime 32523200639 := by
  apply lucas_primality 32523200639 (13 : ZMod 32523200639)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (127, 1), (1789, 1), (3767, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (127, 1), (1789, 1), (3767, 1)] : List FactorBlock).map factorBlockValue).prod) = 32523200639 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_19
      · exact prime_oneHundredEighteenDL_127
      · exact prime_oneHundredEighteenDL_1789
      · exact prime_oneHundredEighteenDL_3767
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 32523200639) ^ 16261600319 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (13 : ZMod 32523200639) ^ 1711747402 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (13 : ZMod 32523200639) ^ 256088194 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (13 : ZMod 32523200639) ^ 18179542 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (13 : ZMod 32523200639) ^ 8633714 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_35008012727 : Nat.Prime 35008012727 := by
  apply lucas_primality 35008012727 (5 : ZMod 35008012727)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (53, 1), (373, 1), (885427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (53, 1), (373, 1), (885427, 1)] : List FactorBlock).map factorBlockValue).prod) = 35008012727 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_53
      · exact prime_oneHundredEighteenDL_373
      · exact prime_oneHundredEighteenDL_885427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 35008012727) ^ 17504006363 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 35008012727) ^ 660528542 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 35008012727) ^ 93855262 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 35008012727) ^ 39538 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_50684133299 : Nat.Prime 50684133299 := by
  apply lucas_primality 50684133299 (2 : ZMod 50684133299)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29537, 1), (857977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29537, 1), (857977, 1)] : List FactorBlock).map factorBlockValue).prod) = 50684133299 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_29537
      · exact prime_oneHundredEighteenDL_857977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 50684133299) ^ 25342066649 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 50684133299) ^ 1715954 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 50684133299) ^ 59074 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_88512052703 : Nat.Prime 88512052703 := by
  apply lucas_primality 88512052703 (5 : ZMod 88512052703)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (25073, 1), (1765087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (25073, 1), (1765087, 1)] : List FactorBlock).map factorBlockValue).prod) = 88512052703 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_25073
      · exact prime_oneHundredEighteenDL_1765087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 88512052703) ^ 44256026351 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 88512052703) ^ 3530174 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 88512052703) ^ 50146 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_95530550279 : Nat.Prime 95530550279 := by
  apply lucas_primality 95530550279 (13 : ZMod 95530550279)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (23, 1), (2267, 1), (53887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (23, 1), (2267, 1), (53887, 1)] : List FactorBlock).map factorBlockValue).prod) = 95530550279 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_17
      · exact prime_oneHundredEighteenDL_23
      · exact prime_oneHundredEighteenDL_2267
      · exact prime_oneHundredEighteenDL_53887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 95530550279) ^ 47765275139 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (13 : ZMod 95530550279) ^ 5619444134 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (13 : ZMod 95530550279) ^ 4153502186 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (13 : ZMod 95530550279) ^ 42139634 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (13 : ZMod 95530550279) ^ 1772794 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_101222580439 : Nat.Prime 101222580439 := by
  apply lucas_primality 101222580439 (13 : ZMod 101222580439)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (163, 1), (461, 1), (10691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (163, 1), (461, 1), (10691, 1)] : List FactorBlock).map factorBlockValue).prod) = 101222580439 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_7
      · exact prime_oneHundredEighteenDL_163
      · exact prime_oneHundredEighteenDL_461
      · exact prime_oneHundredEighteenDL_10691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 101222580439) ^ 50611290219 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (13 : ZMod 101222580439) ^ 33740860146 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (13 : ZMod 101222580439) ^ 14460368634 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (13 : ZMod 101222580439) ^ 620997426 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (13 : ZMod 101222580439) ^ 219571758 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (13 : ZMod 101222580439) ^ 9468018 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_116724111547 : Nat.Prime 116724111547 := by
  apply lucas_primality 116724111547 (5 : ZMod 116724111547)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (43, 1), (3889, 1), (16619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (43, 1), (3889, 1), (16619, 1)] : List FactorBlock).map factorBlockValue).prod) = 116724111547 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_7
      · exact prime_oneHundredEighteenDL_43
      · exact prime_oneHundredEighteenDL_3889
      · exact prime_oneHundredEighteenDL_16619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 116724111547) ^ 58362055773 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 116724111547) ^ 38908037182 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 116724111547) ^ 16674873078 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 116724111547) ^ 2714514222 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 116724111547) ^ 30013914 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 116724111547) ^ 7023534 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_159695854057 : Nat.Prime 159695854057 := by
  apply lucas_primality 159695854057 (5 : ZMod 159695854057)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (17, 1), (5623, 1), (23203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (17, 1), (5623, 1), (23203, 1)] : List FactorBlock).map factorBlockValue).prod) = 159695854057 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_17
      · exact prime_oneHundredEighteenDL_5623
      · exact prime_oneHundredEighteenDL_23203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 159695854057) ^ 79847927028 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 159695854057) ^ 53231951352 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 159695854057) ^ 9393873768 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 159695854057) ^ 28400472 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 159695854057) ^ 6882552 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_159788353943 : Nat.Prime 159788353943 := by
  apply lucas_primality 159788353943 (5 : ZMod 159788353943)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11413453853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11413453853, 1)] : List FactorBlock).map factorBlockValue).prod) = 159788353943 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_7
      · exact prime_oneHundredEighteenDL_11413453853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 159788353943) ^ 79894176971 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 159788353943) ^ 22826907706 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 159788353943) ^ 14 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_179953378837 : Nat.Prime 179953378837 := by
  apply lucas_primality 179953378837 (6 : ZMod 179953378837)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (11, 1), (194754739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (11, 1), (194754739, 1)] : List FactorBlock).map factorBlockValue).prod) = 179953378837 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_7
      · exact prime_oneHundredEighteenDL_11
      · exact prime_oneHundredEighteenDL_194754739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 179953378837) ^ 89976689418 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (6 : ZMod 179953378837) ^ 59984459612 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (6 : ZMod 179953378837) ^ 25707625548 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (6 : ZMod 179953378837) ^ 16359398076 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (6 : ZMod 179953378837) ^ 924 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_184854881531 : Nat.Prime 184854881531 := by
  apply lucas_primality 184854881531 (2 : ZMod 184854881531)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (1680498923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (1680498923, 1)] : List FactorBlock).map factorBlockValue).prod) = 184854881531 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_5
      · exact prime_oneHundredEighteenDL_11
      · exact prime_oneHundredEighteenDL_1680498923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 184854881531) ^ 92427440765 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 184854881531) ^ 36970976306 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 184854881531) ^ 16804989230 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 184854881531) ^ 110 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_221403932777 : Nat.Prime 221403932777 := by
  apply lucas_primality 221403932777 (3 : ZMod 221403932777)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (2128883969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (2128883969, 1)] : List FactorBlock).map factorBlockValue).prod) = 221403932777 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_13
      · exact prime_oneHundredEighteenDL_2128883969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 221403932777) ^ 110701966388 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 221403932777) ^ 17031071752 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 221403932777) ^ 104 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_222185453099 : Nat.Prime 222185453099 := by
  apply lucas_primality 222185453099 (2 : ZMod 222185453099)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (2267198501, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (2267198501, 1)] : List FactorBlock).map factorBlockValue).prod) = 222185453099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_7
      · exact prime_oneHundredEighteenDL_2267198501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 222185453099) ^ 111092726549 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 222185453099) ^ 31740779014 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 222185453099) ^ 98 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_223080162269 : Nat.Prime 223080162269 := by
  apply lucas_primality 223080162269 (2 : ZMod 223080162269)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 2), (151, 1), (613, 1), (1669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 2), (151, 1), (613, 1), (1669, 1)] : List FactorBlock).map factorBlockValue).prod) = 223080162269 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_19
      · exact prime_oneHundredEighteenDL_151
      · exact prime_oneHundredEighteenDL_613
      · exact prime_oneHundredEighteenDL_1669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 223080162269) ^ 111540081134 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 223080162269) ^ 11741061172 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 223080162269) ^ 1477352068 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 223080162269) ^ 363915436 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 223080162269) ^ 133660972 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_261973410679 : Nat.Prime 261973410679 := by
  apply lucas_primality 261973410679 (3 : ZMod 261973410679)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (7, 1), (231017117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (7, 1), (231017117, 1)] : List FactorBlock).map factorBlockValue).prod) = 261973410679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_7
      · exact prime_oneHundredEighteenDL_231017117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 261973410679) ^ 130986705339 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 261973410679) ^ 87324470226 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 261973410679) ^ 37424772954 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 261973410679) ^ 1134 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_294767431087 : Nat.Prime 294767431087 := by
  apply lucas_primality 294767431087 (3 : ZMod 294767431087)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (59, 1), (832676359, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (59, 1), (832676359, 1)] : List FactorBlock).map factorBlockValue).prod) = 294767431087 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_59
      · exact prime_oneHundredEighteenDL_832676359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 294767431087) ^ 147383715543 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 294767431087) ^ 98255810362 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 294767431087) ^ 4996058154 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 294767431087) ^ 354 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_531054790963 : Nat.Prime 531054790963 := by
  apply lucas_primality 531054790963 (2 : ZMod 531054790963)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (307, 1), (313, 1), (401, 1), (2297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (307, 1), (313, 1), (401, 1), (2297, 1)] : List FactorBlock).map factorBlockValue).prod) = 531054790963 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_307
      · exact prime_oneHundredEighteenDL_313
      · exact prime_oneHundredEighteenDL_401
      · exact prime_oneHundredEighteenDL_2297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 531054790963) ^ 265527395481 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 531054790963) ^ 177018263654 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 531054790963) ^ 1729820166 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 531054790963) ^ 1696660674 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 531054790963) ^ 1324326162 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 531054790963) ^ 231194946 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_549267752989 : Nat.Prime 549267752989 := by
  apply lucas_primality 549267752989 (2 : ZMod 549267752989)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (59, 1), (67, 1), (151, 1), (25561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (59, 1), (67, 1), (151, 1), (25561, 1)] : List FactorBlock).map factorBlockValue).prod) = 549267752989 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_59
      · exact prime_oneHundredEighteenDL_67
      · exact prime_oneHundredEighteenDL_151
      · exact prime_oneHundredEighteenDL_25561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 549267752989) ^ 274633876494 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 549267752989) ^ 183089250996 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 549267752989) ^ 9309622932 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 549267752989) ^ 8198026164 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 549267752989) ^ 3637534788 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 549267752989) ^ 21488508 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_722099950267 : Nat.Prime 722099950267 := by
  apply lucas_primality 722099950267 (2 : ZMod 722099950267)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (67, 1), (167, 1), (10756099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (67, 1), (167, 1), (10756099, 1)] : List FactorBlock).map factorBlockValue).prod) = 722099950267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_67
      · exact prime_oneHundredEighteenDL_167
      · exact prime_oneHundredEighteenDL_10756099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 722099950267) ^ 361049975133 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 722099950267) ^ 240699983422 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 722099950267) ^ 10777611198 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 722099950267) ^ 4323951798 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 722099950267) ^ 67134 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_730768111753 : Nat.Prime 730768111753 := by
  apply lucas_primality 730768111753 (5 : ZMod 730768111753)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (4349810189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (4349810189, 1)] : List FactorBlock).map factorBlockValue).prod) = 730768111753 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_7
      · exact prime_oneHundredEighteenDL_4349810189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 730768111753) ^ 365384055876 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 730768111753) ^ 243589370584 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 730768111753) ^ 104395444536 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 730768111753) ^ 168 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_1050668988011 : Nat.Prime 1050668988011 := by
  apply lucas_primality 1050668988011 (2 : ZMod 1050668988011)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (19, 2), (53, 1), (1321, 1), (4157, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (19, 2), (53, 1), (1321, 1), (4157, 1)] : List FactorBlock).map factorBlockValue).prod) = 1050668988011 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_5
      · exact prime_oneHundredEighteenDL_19
      · exact prime_oneHundredEighteenDL_53
      · exact prime_oneHundredEighteenDL_1321
      · exact prime_oneHundredEighteenDL_4157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1050668988011) ^ 525334494005 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1050668988011) ^ 210133797602 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1050668988011) ^ 55298367790 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1050668988011) ^ 19823943170 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1050668988011) ^ 795358810 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1050668988011) ^ 252746930 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_1103780217269 : Nat.Prime 1103780217269 := by
  apply lucas_primality 1103780217269 (2 : ZMod 1103780217269)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (37, 1), (12547, 1), (594403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (37, 1), (12547, 1), (594403, 1)] : List FactorBlock).map factorBlockValue).prod) = 1103780217269 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_37
      · exact prime_oneHundredEighteenDL_12547
      · exact prime_oneHundredEighteenDL_594403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1103780217269) ^ 551890108634 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1103780217269) ^ 29831897764 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1103780217269) ^ 87971644 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1103780217269) ^ 1856956 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_1169681357543 : Nat.Prime 1169681357543 := by
  apply lucas_primality 1169681357543 (5 : ZMod 1169681357543)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (61, 1), (9587552111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (61, 1), (9587552111, 1)] : List FactorBlock).map factorBlockValue).prod) = 1169681357543 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_61
      · exact prime_oneHundredEighteenDL_9587552111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1169681357543) ^ 584840678771 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 1169681357543) ^ 19175104222 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 1169681357543) ^ 122 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_1273234492753 : Nat.Prime 1273234492753 := by
  apply lucas_primality 1273234492753 (5 : ZMod 1273234492753)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (23, 1), (2381, 1), (484373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (23, 1), (2381, 1), (484373, 1)] : List FactorBlock).map factorBlockValue).prod) = 1273234492753 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_23
      · exact prime_oneHundredEighteenDL_2381
      · exact prime_oneHundredEighteenDL_484373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1273234492753) ^ 636617246376 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 1273234492753) ^ 424411497584 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 1273234492753) ^ 55358021424 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 1273234492753) ^ 534747792 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 1273234492753) ^ 2628624 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_1586081060903 : Nat.Prime 1586081060903 := by
  apply lucas_primality 1586081060903 (5 : ZMod 1586081060903)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (90407, 1), (674761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (90407, 1), (674761, 1)] : List FactorBlock).map factorBlockValue).prod) = 1586081060903 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_13
      · exact prime_oneHundredEighteenDL_90407
      · exact prime_oneHundredEighteenDL_674761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1586081060903) ^ 793040530451 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 1586081060903) ^ 122006235454 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 1586081060903) ^ 17543786 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 1586081060903) ^ 2350582 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_2197071011957 : Nat.Prime 2197071011957 := by
  apply lucas_primality 2197071011957 (2 : ZMod 2197071011957)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (549267752989, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (549267752989, 1)] : List FactorBlock).map factorBlockValue).prod) = 2197071011957 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_549267752989
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 2197071011957) ^ 1098535505978 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 2197071011957) ^ 4 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_2920855544681 : Nat.Prime 2920855544681 := by
  apply lucas_primality 2920855544681 (3 : ZMod 2920855544681)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (17, 1), (251, 1), (17113051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (17, 1), (251, 1), (17113051, 1)] : List FactorBlock).map factorBlockValue).prod) = 2920855544681 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_5
      · exact prime_oneHundredEighteenDL_17
      · exact prime_oneHundredEighteenDL_251
      · exact prime_oneHundredEighteenDL_17113051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2920855544681) ^ 1460427772340 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 2920855544681) ^ 584171108936 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 2920855544681) ^ 171815032040 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 2920855544681) ^ 11636874680 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 2920855544681) ^ 170680 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_3362303597867 : Nat.Prime 3362303597867 := by
  apply lucas_primality 3362303597867 (2 : ZMod 3362303597867)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (59, 1), (83, 1), (8373229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (59, 1), (83, 1), (8373229, 1)] : List FactorBlock).map factorBlockValue).prod) = 3362303597867 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_41
      · exact prime_oneHundredEighteenDL_59
      · exact prime_oneHundredEighteenDL_83
      · exact prime_oneHundredEighteenDL_8373229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3362303597867) ^ 1681151798933 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 3362303597867) ^ 82007404826 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 3362303597867) ^ 56988196574 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 3362303597867) ^ 40509681902 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 3362303597867) ^ 401554 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_3704571807967 : Nat.Prime 3704571807967 := by
  apply lucas_primality 3704571807967 (3 : ZMod 3704571807967)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (31, 1), (349, 1), (2423, 1), (2617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (31, 1), (349, 1), (2423, 1), (2617, 1)] : List FactorBlock).map factorBlockValue).prod) = 3704571807967 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_31
      · exact prime_oneHundredEighteenDL_349
      · exact prime_oneHundredEighteenDL_2423
      · exact prime_oneHundredEighteenDL_2617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3704571807967) ^ 1852285903983 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 3704571807967) ^ 1234857269322 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 3704571807967) ^ 119502316386 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 3704571807967) ^ 10614818934 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 3704571807967) ^ 1528919442 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 3704571807967) ^ 1415579598 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_3772283211553 : Nat.Prime 3772283211553 := by
  apply lucas_primality 3772283211553 (5 : ZMod 3772283211553)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (1093, 1), (5779, 1), (6221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (1093, 1), (5779, 1), (6221, 1)] : List FactorBlock).map factorBlockValue).prod) = 3772283211553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_1093
      · exact prime_oneHundredEighteenDL_5779
      · exact prime_oneHundredEighteenDL_6221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 3772283211553) ^ 1886141605776 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 3772283211553) ^ 1257427737184 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 3772283211553) ^ 3451311264 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 3772283211553) ^ 652757088 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 3772283211553) ^ 606378912 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_4011129502741 : Nat.Prime 4011129502741 := by
  apply lucas_primality 4011129502741 (2 : ZMod 4011129502741)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (22284052793, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (22284052793, 1)] : List FactorBlock).map factorBlockValue).prod) = 4011129502741 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_5
      · exact prime_oneHundredEighteenDL_22284052793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4011129502741) ^ 2005564751370 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 4011129502741) ^ 1337043167580 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 4011129502741) ^ 802225900548 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 4011129502741) ^ 180 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_4528634000201 : Nat.Prime 4528634000201 := by
  apply lucas_primality 4528634000201 (3 : ZMod 4528634000201)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (22643170001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (22643170001, 1)] : List FactorBlock).map factorBlockValue).prod) = 4528634000201 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_5
      · exact prime_oneHundredEighteenDL_22643170001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 4528634000201) ^ 2264317000100 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 4528634000201) ^ 905726800040 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 4528634000201) ^ 200 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_5841711089363 : Nat.Prime 5841711089363 := by
  apply lucas_primality 5841711089363 (2 : ZMod 5841711089363)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2920855544681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2920855544681, 1)] : List FactorBlock).map factorBlockValue).prod) = 5841711089363 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_2920855544681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 5841711089363) ^ 2920855544681 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 5841711089363) ^ 2 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_6797626137803 : Nat.Prime 6797626137803 := by
  apply lucas_primality 6797626137803 (2 : ZMod 6797626137803)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (83, 1), (1106744731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (83, 1), (1106744731, 1)] : List FactorBlock).map factorBlockValue).prod) = 6797626137803 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_37
      · exact prime_oneHundredEighteenDL_83
      · exact prime_oneHundredEighteenDL_1106744731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 6797626137803) ^ 3398813068901 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 6797626137803) ^ 183719625346 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 6797626137803) ^ 81899110094 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 6797626137803) ^ 6142 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_7195321868923 : Nat.Prime 7195321868923 := by
  apply lucas_primality 7195321868923 (2 : ZMod 7195321868923)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (31, 1), (1172258369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (31, 1), (1172258369, 1)] : List FactorBlock).map factorBlockValue).prod) = 7195321868923 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_11
      · exact prime_oneHundredEighteenDL_31
      · exact prime_oneHundredEighteenDL_1172258369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7195321868923) ^ 3597660934461 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 7195321868923) ^ 2398440622974 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 7195321868923) ^ 654120169902 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 7195321868923) ^ 232107157062 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 7195321868923) ^ 6138 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_8643607837597 : Nat.Prime 8643607837597 := by
  apply lucas_primality 8643607837597 (5 : ZMod 8643607837597)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (41, 1), (53, 1), (433, 1), (255179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (41, 1), (53, 1), (433, 1), (255179, 1)] : List FactorBlock).map factorBlockValue).prod) = 8643607837597 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_41
      · exact prime_oneHundredEighteenDL_53
      · exact prime_oneHundredEighteenDL_433
      · exact prime_oneHundredEighteenDL_255179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 8643607837597) ^ 4321803918798 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 8643607837597) ^ 2881202612532 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 8643607837597) ^ 210819703356 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 8643607837597) ^ 163086940332 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 8643607837597) ^ 19962142812 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 8643607837597) ^ 33872724 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_10880858014333 : Nat.Prime 10880858014333 := by
  apply lucas_primality 10880858014333 (2 : ZMod 10880858014333)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (654107, 1), (1386223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (654107, 1), (1386223, 1)] : List FactorBlock).map factorBlockValue).prod) = 10880858014333 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_654107
      · exact prime_oneHundredEighteenDL_1386223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 10880858014333) ^ 5440429007166 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 10880858014333) ^ 3626952671444 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 10880858014333) ^ 16634676 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 10880858014333) ^ 7849284 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_14112454044391 : Nat.Prime 14112454044391 := by
  apply lucas_primality 14112454044391 (6 : ZMod 14112454044391)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (13, 1), (557, 1), (64965493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (13, 1), (557, 1), (64965493, 1)] : List FactorBlock).map factorBlockValue).prod) = 14112454044391 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_5
      · exact prime_oneHundredEighteenDL_13
      · exact prime_oneHundredEighteenDL_557
      · exact prime_oneHundredEighteenDL_64965493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 14112454044391) ^ 7056227022195 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (6 : ZMod 14112454044391) ^ 4704151348130 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (6 : ZMod 14112454044391) ^ 2822490808878 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (6 : ZMod 14112454044391) ^ 1085573388030 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (6 : ZMod 14112454044391) ^ 25336542270 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (6 : ZMod 14112454044391) ^ 217230 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_15278813913037 : Nat.Prime 15278813913037 := by
  apply lucas_primality 15278813913037 (2 : ZMod 15278813913037)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1273234492753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1273234492753, 1)] : List FactorBlock).map factorBlockValue).prod) = 15278813913037 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_1273234492753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 15278813913037) ^ 7639406956518 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 15278813913037) ^ 5092937971012 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 15278813913037) ^ 12 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_16859710603663 : Nat.Prime 16859710603663 := by
  apply lucas_primality 16859710603663 (6 : ZMod 16859710603663)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1999, 1), (26177, 1), (53699, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1999, 1), (26177, 1), (53699, 1)] : List FactorBlock).map factorBlockValue).prod) = 16859710603663 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_1999
      · exact prime_oneHundredEighteenDL_26177
      · exact prime_oneHundredEighteenDL_53699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 16859710603663) ^ 8429855301831 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (6 : ZMod 16859710603663) ^ 5619903534554 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (6 : ZMod 16859710603663) ^ 8434072338 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (6 : ZMod 16859710603663) ^ 644065806 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (6 : ZMod 16859710603663) ^ 313966938 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_19330398271207 : Nat.Prime 19330398271207 := by
  apply lucas_primality 19330398271207 (3 : ZMod 19330398271207)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (41, 1), (43, 1), (541, 1), (102359, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (41, 1), (43, 1), (541, 1), (102359, 1)] : List FactorBlock).map factorBlockValue).prod) = 19330398271207 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_11
      · exact prime_oneHundredEighteenDL_41
      · exact prime_oneHundredEighteenDL_43
      · exact prime_oneHundredEighteenDL_541
      · exact prime_oneHundredEighteenDL_102359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 19330398271207) ^ 9665199135603 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 19330398271207) ^ 6443466090402 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 19330398271207) ^ 1757308933746 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 19330398271207) ^ 471473128566 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 19330398271207) ^ 449544145842 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 19330398271207) ^ 35730865566 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 19330398271207) ^ 188849034 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_23758403961679 : Nat.Prime 23758403961679 := by
  apply lucas_primality 23758403961679 (6 : ZMod 23758403961679)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (41, 1), (277, 1), (5119, 1), (68111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (41, 1), (277, 1), (5119, 1), (68111, 1)] : List FactorBlock).map factorBlockValue).prod) = 23758403961679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_41
      · exact prime_oneHundredEighteenDL_277
      · exact prime_oneHundredEighteenDL_5119
      · exact prime_oneHundredEighteenDL_68111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 23758403961679) ^ 11879201980839 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (6 : ZMod 23758403961679) ^ 7919467987226 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (6 : ZMod 23758403961679) ^ 579473267358 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (6 : ZMod 23758403961679) ^ 85770411414 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (6 : ZMod 23758403961679) ^ 4641219762 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (6 : ZMod 23758403961679) ^ 348818898 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_25609888454543 : Nat.Prime 25609888454543 := by
  apply lucas_primality 25609888454543 (5 : ZMod 25609888454543)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (1041619, 1), (1756187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (1041619, 1), (1756187, 1)] : List FactorBlock).map factorBlockValue).prod) = 25609888454543 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_7
      · exact prime_oneHundredEighteenDL_1041619
      · exact prime_oneHundredEighteenDL_1756187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 25609888454543) ^ 12804944227271 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 25609888454543) ^ 3658555493506 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 25609888454543) ^ 24586618 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 25609888454543) ^ 14582666 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_34390593153349 : Nat.Prime 34390593153349 := by
  apply lucas_primality 34390593153349 (6 : ZMod 34390593153349)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (103, 1), (1636712029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (103, 1), (1636712029, 1)] : List FactorBlock).map factorBlockValue).prod) = 34390593153349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_17
      · exact prime_oneHundredEighteenDL_103
      · exact prime_oneHundredEighteenDL_1636712029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 34390593153349) ^ 17195296576674 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (6 : ZMod 34390593153349) ^ 11463531051116 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (6 : ZMod 34390593153349) ^ 2022976067844 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (6 : ZMod 34390593153349) ^ 333889253916 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (6 : ZMod 34390593153349) ^ 21012 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_36554100161399 : Nat.Prime 36554100161399 := by
  apply lucas_primality 36554100161399 (7 : ZMod 36554100161399)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (13381, 1), (47099851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (13381, 1), (47099851, 1)] : List FactorBlock).map factorBlockValue).prod) = 36554100161399 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_29
      · exact prime_oneHundredEighteenDL_13381
      · exact prime_oneHundredEighteenDL_47099851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 36554100161399) ^ 18277050080699 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (7 : ZMod 36554100161399) ^ 1260486212462 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (7 : ZMod 36554100161399) ^ 2731791358 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (7 : ZMod 36554100161399) ^ 776098 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_65666320948057 : Nat.Prime 65666320948057 := by
  apply lucas_primality 65666320948057 (5 : ZMod 65666320948057)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (163, 1), (16785869363, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (163, 1), (16785869363, 1)] : List FactorBlock).map factorBlockValue).prod) = 65666320948057 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_163
      · exact prime_oneHundredEighteenDL_16785869363
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 65666320948057) ^ 32833160474028 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 65666320948057) ^ 21888773649352 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 65666320948057) ^ 402860864712 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 65666320948057) ^ 3912 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_67840200427693 : Nat.Prime 67840200427693 := by
  apply lucas_primality 67840200427693 (2 : ZMod 67840200427693)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (11, 2), (167, 1), (211, 1), (307, 1), (617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (11, 2), (167, 1), (211, 1), (307, 1), (617, 1)] : List FactorBlock).map factorBlockValue).prod) = 67840200427693 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_7
      · exact prime_oneHundredEighteenDL_11
      · exact prime_oneHundredEighteenDL_167
      · exact prime_oneHundredEighteenDL_211
      · exact prime_oneHundredEighteenDL_307
      · exact prime_oneHundredEighteenDL_617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 67840200427693) ^ 33920100213846 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 67840200427693) ^ 22613400142564 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 67840200427693) ^ 9691457203956 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 67840200427693) ^ 6167290947972 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 67840200427693) ^ 406228745076 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 67840200427693) ^ 321517537572 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 67840200427693) ^ 220977851556 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 67840200427693) ^ 109951702476 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_81329626786489 : Nat.Prime 81329626786489 := by
  apply lucas_primality 81329626786489 (29 : ZMod 81329626786489)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (67, 1), (29411, 1), (1719701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (67, 1), (29411, 1), (1719701, 1)] : List FactorBlock).map factorBlockValue).prod) = 81329626786489 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_67
      · exact prime_oneHundredEighteenDL_29411
      · exact prime_oneHundredEighteenDL_1719701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (29 : ZMod 81329626786489) ^ 40664813393244 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (29 : ZMod 81329626786489) ^ 27109875595496 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (29 : ZMod 81329626786489) ^ 1213875026664 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (29 : ZMod 81329626786489) ^ 2765279208 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (29 : ZMod 81329626786489) ^ 47292888 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_83310427919011 : Nat.Prime 83310427919011 := by
  apply lucas_primality 83310427919011 (2 : ZMod 83310427919011)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (43, 1), (3001, 1), (21520069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (43, 1), (3001, 1), (21520069, 1)] : List FactorBlock).map factorBlockValue).prod) = 83310427919011 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_5
      · exact prime_oneHundredEighteenDL_43
      · exact prime_oneHundredEighteenDL_3001
      · exact prime_oneHundredEighteenDL_21520069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 83310427919011) ^ 41655213959505 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 83310427919011) ^ 27770142639670 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 83310427919011) ^ 16662085583802 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 83310427919011) ^ 1937451812070 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 83310427919011) ^ 27760889010 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 83310427919011) ^ 3871290 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_91028552693759 : Nat.Prime 91028552693759 := by
  apply lucas_primality 91028552693759 (7 : ZMod 91028552693759)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3169, 1), (4729, 1), (3037079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3169, 1), (4729, 1), (3037079, 1)] : List FactorBlock).map factorBlockValue).prod) = 91028552693759 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3169
      · exact prime_oneHundredEighteenDL_4729
      · exact prime_oneHundredEighteenDL_3037079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 91028552693759) ^ 45514276346879 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (7 : ZMod 91028552693759) ^ 28724693182 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (7 : ZMod 91028552693759) ^ 19249006702 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (7 : ZMod 91028552693759) ^ 29972402 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_115902620448737 : Nat.Prime 115902620448737 := by
  apply lucas_primality 115902620448737 (3 : ZMod 115902620448737)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (11, 1), (61, 2), (701, 1), (126233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (11, 1), (61, 2), (701, 1), (126233, 1)] : List FactorBlock).map factorBlockValue).prod) = 115902620448737 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_11
      · exact prime_oneHundredEighteenDL_61
      · exact prime_oneHundredEighteenDL_701
      · exact prime_oneHundredEighteenDL_126233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 115902620448737) ^ 57951310224368 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 115902620448737) ^ 10536601858976 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 115902620448737) ^ 1900042958176 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 115902620448737) ^ 165338973536 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 115902620448737) ^ 918164192 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_150481022080241 : Nat.Prime 150481022080241 := by
  apply lucas_primality 150481022080241 (3 : ZMod 150481022080241)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (163, 1), (11539955681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (163, 1), (11539955681, 1)] : List FactorBlock).map factorBlockValue).prod) = 150481022080241 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_5
      · exact prime_oneHundredEighteenDL_163
      · exact prime_oneHundredEighteenDL_11539955681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 150481022080241) ^ 75240511040120 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 150481022080241) ^ 30096204416048 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 150481022080241) ^ 923196454480 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 150481022080241) ^ 13040 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_168221083693387 : Nat.Prime 168221083693387 := by
  apply lucas_primality 168221083693387 (2 : ZMod 168221083693387)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (2039, 1), (23071, 1), (25913, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (2039, 1), (23071, 1), (25913, 1)] : List FactorBlock).map factorBlockValue).prod) = 168221083693387 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_23
      · exact prime_oneHundredEighteenDL_2039
      · exact prime_oneHundredEighteenDL_23071
      · exact prime_oneHundredEighteenDL_25913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 168221083693387) ^ 84110541846693 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 168221083693387) ^ 56073694564462 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 168221083693387) ^ 7313960160582 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 168221083693387) ^ 82501757574 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 168221083693387) ^ 7291451766 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 168221083693387) ^ 6491764122 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_207446588102329 : Nat.Prime 207446588102329 := by
  apply lucas_primality 207446588102329 (19 : ZMod 207446588102329)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (8643607837597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (8643607837597, 1)] : List FactorBlock).map factorBlockValue).prod) = 207446588102329 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_8643607837597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (19 : ZMod 207446588102329) ^ 103723294051164 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (19 : ZMod 207446588102329) ^ 69148862700776 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (19 : ZMod 207446588102329) ^ 24 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_265145024234393 : Nat.Prime 265145024234393 := by
  apply lucas_primality 265145024234393 (3 : ZMod 265145024234393)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (569, 1), (25759, 1), (2261269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (569, 1), (25759, 1), (2261269, 1)] : List FactorBlock).map factorBlockValue).prod) = 265145024234393 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_569
      · exact prime_oneHundredEighteenDL_25759
      · exact prime_oneHundredEighteenDL_2261269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 265145024234393) ^ 132572512117196 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 265145024234393) ^ 465984225368 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 265145024234393) ^ 10293296488 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 265145024234393) ^ 117254968 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_341303789052949 : Nat.Prime 341303789052949 := by
  apply lucas_primality 341303789052949 (2 : ZMod 341303789052949)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (41, 1), (43, 1), (57571, 1), (280223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (41, 1), (43, 1), (57571, 1), (280223, 1)] : List FactorBlock).map factorBlockValue).prod) = 341303789052949 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_41
      · exact prime_oneHundredEighteenDL_43
      · exact prime_oneHundredEighteenDL_57571
      · exact prime_oneHundredEighteenDL_280223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 341303789052949) ^ 170651894526474 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 341303789052949) ^ 113767929684316 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 341303789052949) ^ 8324482659828 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 341303789052949) ^ 7937297419836 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 341303789052949) ^ 5928397788 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 341303789052949) ^ 1217972076 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_430474284734911 : Nat.Prime 430474284734911 := by
  apply lucas_primality 430474284734911 (6 : ZMod 430474284734911)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (13, 1), (1103780217269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (13, 1), (1103780217269, 1)] : List FactorBlock).map factorBlockValue).prod) = 430474284734911 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_5
      · exact prime_oneHundredEighteenDL_13
      · exact prime_oneHundredEighteenDL_1103780217269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 430474284734911) ^ 215237142367455 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (6 : ZMod 430474284734911) ^ 143491428244970 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (6 : ZMod 430474284734911) ^ 86094856946982 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (6 : ZMod 430474284734911) ^ 33113406518070 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (6 : ZMod 430474284734911) ^ 390 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_871275936325357 : Nat.Prime 871275936325357 := by
  apply lucas_primality 871275936325357 (6 : ZMod 871275936325357)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (39161, 1), (618015611, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (39161, 1), (618015611, 1)] : List FactorBlock).map factorBlockValue).prod) = 871275936325357 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_39161
      · exact prime_oneHundredEighteenDL_618015611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 871275936325357) ^ 435637968162678 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (6 : ZMod 871275936325357) ^ 290425312108452 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (6 : ZMod 871275936325357) ^ 22248561996 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (6 : ZMod 871275936325357) ^ 1409796 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_985962202947919 : Nat.Prime 985962202947919 := by
  apply lucas_primality 985962202947919 (7 : ZMod 985962202947919)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 3), (159695854057, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 3), (159695854057, 1)] : List FactorBlock).map factorBlockValue).prod) = 985962202947919 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_7
      · exact prime_oneHundredEighteenDL_159695854057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 985962202947919) ^ 492981101473959 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (7 : ZMod 985962202947919) ^ 328654067649306 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (7 : ZMod 985962202947919) ^ 140851743278274 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (7 : ZMod 985962202947919) ^ 6174 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_1164898268108327 : Nat.Prime 1164898268108327 := by
  apply lucas_primality 1164898268108327 (5 : ZMod 1164898268108327)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (59, 1), (1621, 1), (6090079717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (59, 1), (1621, 1), (6090079717, 1)] : List FactorBlock).map factorBlockValue).prod) = 1164898268108327 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_59
      · exact prime_oneHundredEighteenDL_1621
      · exact prime_oneHundredEighteenDL_6090079717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1164898268108327) ^ 582449134054163 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 1164898268108327) ^ 19744038442514 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 1164898268108327) ^ 718629406606 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 1164898268108327) ^ 191278 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_1582098289002067 : Nat.Prime 1582098289002067 := by
  apply lucas_primality 1582098289002067 (3 : ZMod 1582098289002067)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (31, 1), (3593, 1), (215214047, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (31, 1), (3593, 1), (215214047, 1)] : List FactorBlock).map factorBlockValue).prod) = 1582098289002067 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_11
      · exact prime_oneHundredEighteenDL_31
      · exact prime_oneHundredEighteenDL_3593
      · exact prime_oneHundredEighteenDL_215214047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1582098289002067) ^ 791049144501033 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 1582098289002067) ^ 527366096334022 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 1582098289002067) ^ 143827117182006 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 1582098289002067) ^ 51035428677486 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 1582098289002067) ^ 440327940162 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 1582098289002067) ^ 7351278 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_1588007828000327 : Nat.Prime 1588007828000327 := by
  apply lucas_primality 1588007828000327 (5 : ZMod 1588007828000327)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (457, 1), (62761, 1), (27683219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (457, 1), (62761, 1), (27683219, 1)] : List FactorBlock).map factorBlockValue).prod) = 1588007828000327 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_457
      · exact prime_oneHundredEighteenDL_62761
      · exact prime_oneHundredEighteenDL_27683219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1588007828000327) ^ 794003914000163 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 1588007828000327) ^ 3474853015318 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 1588007828000327) ^ 25302462166 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 1588007828000327) ^ 57363554 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_1628083879652833 : Nat.Prime 1628083879652833 := by
  apply lucas_primality 1628083879652833 (10 : ZMod 1628083879652833)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (7, 3), (151, 1), (327442069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (7, 3), (151, 1), (327442069, 1)] : List FactorBlock).map factorBlockValue).prod) = 1628083879652833 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_7
      · exact prime_oneHundredEighteenDL_151
      · exact prime_oneHundredEighteenDL_327442069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 1628083879652833) ^ 814041939826416 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (10 : ZMod 1628083879652833) ^ 542694626550944 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (10 : ZMod 1628083879652833) ^ 232583411378976 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (10 : ZMod 1628083879652833) ^ 10782012448032 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (10 : ZMod 1628083879652833) ^ 4972128 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_1763235098500457 : Nat.Prime 1763235098500457 := by
  apply lucas_primality 1763235098500457 (3 : ZMod 1763235098500457)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (499, 1), (541, 1), (1117, 1), (104417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (499, 1), (541, 1), (1117, 1), (104417, 1)] : List FactorBlock).map factorBlockValue).prod) = 1763235098500457 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_7
      · exact prime_oneHundredEighteenDL_499
      · exact prime_oneHundredEighteenDL_541
      · exact prime_oneHundredEighteenDL_1117
      · exact prime_oneHundredEighteenDL_104417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1763235098500457) ^ 881617549250228 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 1763235098500457) ^ 251890728357208 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 1763235098500457) ^ 3533537271544 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 1763235098500457) ^ 3259214599816 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 1763235098500457) ^ 1578545298568 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 1763235098500457) ^ 16886475368 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_4614538195344313 : Nat.Prime 4614538195344313 := by
  apply lucas_primality 4614538195344313 (5 : ZMod 4614538195344313)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (61, 1), (1050668988011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (61, 1), (1050668988011, 1)] : List FactorBlock).map factorBlockValue).prod) = 4614538195344313 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_61
      · exact prime_oneHundredEighteenDL_1050668988011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 4614538195344313) ^ 2307269097672156 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 4614538195344313) ^ 1538179398448104 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 4614538195344313) ^ 75648167136792 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 4614538195344313) ^ 4392 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_6887588555758577 : Nat.Prime 6887588555758577 := by
  apply lucas_primality 6887588555758577 (3 : ZMod 6887588555758577)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (430474284734911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (430474284734911, 1)] : List FactorBlock).map factorBlockValue).prod) = 6887588555758577 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_430474284734911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 6887588555758577) ^ 3443794277879288 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 6887588555758577) ^ 16 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_9071004829670243 : Nat.Prime 9071004829670243 := by
  apply lucas_primality 9071004829670243 (2 : ZMod 9071004829670243)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (349, 1), (1883551, 1), (6899579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (349, 1), (1883551, 1), (6899579, 1)] : List FactorBlock).map factorBlockValue).prod) = 9071004829670243 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_349
      · exact prime_oneHundredEighteenDL_1883551
      · exact prime_oneHundredEighteenDL_6899579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 9071004829670243) ^ 4535502414835121 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 9071004829670243) ^ 25991417850058 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 9071004829670243) ^ 4815906142 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 9071004829670243) ^ 1314718598 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_11966874395741381 : Nat.Prime 11966874395741381 := by
  apply lucas_primality 11966874395741381 (2 : ZMod 11966874395741381)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (37, 1), (211, 1), (709, 1), (108098663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (37, 1), (211, 1), (709, 1), (108098663, 1)] : List FactorBlock).map factorBlockValue).prod) = 11966874395741381 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_5
      · exact prime_oneHundredEighteenDL_37
      · exact prime_oneHundredEighteenDL_211
      · exact prime_oneHundredEighteenDL_709
      · exact prime_oneHundredEighteenDL_108098663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 11966874395741381) ^ 5983437197870690 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 11966874395741381) ^ 2393374879148276 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 11966874395741381) ^ 323429037722740 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 11966874395741381) ^ 56715044529580 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 11966874395741381) ^ 16878525240820 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 11966874395741381) ^ 110703260 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_12821368695406591 : Nat.Prime 12821368695406591 := by
  apply lucas_primality 12821368695406591 (6 : ZMod 12821368695406591)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (19, 1), (348247, 1), (5871911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (19, 1), (348247, 1), (5871911, 1)] : List FactorBlock).map factorBlockValue).prod) = 12821368695406591 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_5
      · exact prime_oneHundredEighteenDL_11
      · exact prime_oneHundredEighteenDL_19
      · exact prime_oneHundredEighteenDL_348247
      · exact prime_oneHundredEighteenDL_5871911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 12821368695406591) ^ 6410684347703295 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (6 : ZMod 12821368695406591) ^ 4273789565135530 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (6 : ZMod 12821368695406591) ^ 2564273739081318 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (6 : ZMod 12821368695406591) ^ 1165578972309690 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (6 : ZMod 12821368695406591) ^ 674808878705610 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (6 : ZMod 12821368695406591) ^ 36816881970 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (6 : ZMod 12821368695406591) ^ 2183508690 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_14970383247363521 : Nat.Prime 14970383247363521 := by
  apply lucas_primality 14970383247363521 (3 : ZMod 14970383247363521)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (5, 1), (23, 1), (659, 1), (6367, 1), (484769, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (5, 1), (23, 1), (659, 1), (6367, 1), (484769, 1)] : List FactorBlock).map factorBlockValue).prod) = 14970383247363521 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_5
      · exact prime_oneHundredEighteenDL_23
      · exact prime_oneHundredEighteenDL_659
      · exact prime_oneHundredEighteenDL_6367
      · exact prime_oneHundredEighteenDL_484769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 14970383247363521) ^ 7485191623681760 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 14970383247363521) ^ 2994076649472704 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 14970383247363521) ^ 650886228146240 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 14970383247363521) ^ 22716818281280 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 14970383247363521) ^ 2351245994560 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 14970383247363521) ^ 30881478080 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_17242779322502959 : Nat.Prime 17242779322502959 := by
  apply lucas_primality 17242779322502959 (6 : ZMod 17242779322502959)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (563, 1), (393209, 1), (1854497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (563, 1), (393209, 1), (1854497, 1)] : List FactorBlock).map factorBlockValue).prod) = 17242779322502959 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_7
      · exact prime_oneHundredEighteenDL_563
      · exact prime_oneHundredEighteenDL_393209
      · exact prime_oneHundredEighteenDL_1854497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 17242779322502959) ^ 8621389661251479 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (6 : ZMod 17242779322502959) ^ 5747593107500986 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (6 : ZMod 17242779322502959) ^ 2463254188928994 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (6 : ZMod 17242779322502959) ^ 30626606256666 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (6 : ZMod 17242779322502959) ^ 43851436062 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (6 : ZMod 17242779322502959) ^ 9297820014 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_18316854115477111 : Nat.Prime 18316854115477111 := by
  apply lucas_primality 18316854115477111 (15 : ZMod 18316854115477111)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (67840200427693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (67840200427693, 1)] : List FactorBlock).map factorBlockValue).prod) = 18316854115477111 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_5
      · exact prime_oneHundredEighteenDL_67840200427693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (15 : ZMod 18316854115477111) ^ 9158427057738555 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (15 : ZMod 18316854115477111) ^ 6105618038492370 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (15 : ZMod 18316854115477111) ^ 3663370823095422 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (15 : ZMod 18316854115477111) ^ 270 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_18825236664309919 : Nat.Prime 18825236664309919 := by
  apply lucas_primality 18825236664309919 (12 : ZMod 18825236664309919)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (19, 2), (270619, 1), (3568463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (19, 2), (270619, 1), (3568463, 1)] : List FactorBlock).map factorBlockValue).prod) = 18825236664309919 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_19
      · exact prime_oneHundredEighteenDL_270619
      · exact prime_oneHundredEighteenDL_3568463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (12 : ZMod 18825236664309919) ^ 9412618332154959 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (12 : ZMod 18825236664309919) ^ 6275078888103306 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (12 : ZMod 18825236664309919) ^ 990801929700522 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (12 : ZMod 18825236664309919) ^ 69563617722 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (12 : ZMod 18825236664309919) ^ 5275446786 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_20634355892009401 : Nat.Prime 20634355892009401 := by
  apply lucas_primality 20634355892009401 (7 : ZMod 20634355892009401)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 2), (34390593153349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 2), (34390593153349, 1)] : List FactorBlock).map factorBlockValue).prod) = 20634355892009401 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_5
      · exact prime_oneHundredEighteenDL_34390593153349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 20634355892009401) ^ 10317177946004700 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (7 : ZMod 20634355892009401) ^ 6878118630669800 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (7 : ZMod 20634355892009401) ^ 4126871178401880 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (7 : ZMod 20634355892009401) ^ 600 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_24395326390228303 : Nat.Prime 24395326390228303 := by
  apply lucas_primality 24395326390228303 (3 : ZMod 24395326390228303)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (37, 2), (127, 1), (7795194553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (37, 2), (127, 1), (7795194553, 1)] : List FactorBlock).map factorBlockValue).prod) = 24395326390228303 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_37
      · exact prime_oneHundredEighteenDL_127
      · exact prime_oneHundredEighteenDL_7795194553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 24395326390228303) ^ 12197663195114151 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 24395326390228303) ^ 8131775463409434 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 24395326390228303) ^ 659333145681846 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 24395326390228303) ^ 192089184175026 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 24395326390228303) ^ 3129534 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_24564376851674137 : Nat.Prime 24564376851674137 := by
  apply lucas_primality 24564376851674137 (5 : ZMod 24564376851674137)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (73, 1), (5279, 1), (2655950567, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (73, 1), (5279, 1), (2655950567, 1)] : List FactorBlock).map factorBlockValue).prod) = 24564376851674137 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_73
      · exact prime_oneHundredEighteenDL_5279
      · exact prime_oneHundredEighteenDL_2655950567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 24564376851674137) ^ 12282188425837068 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 24564376851674137) ^ 8188125617224712 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 24564376851674137) ^ 336498313036632 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 24564376851674137) ^ 4653225393384 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 24564376851674137) ^ 9248808 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_36847107955599349 : Nat.Prime 36847107955599349 := by
  apply lucas_primality 36847107955599349 (13 : ZMod 36847107955599349)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (947, 1), (294767431087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (947, 1), (294767431087, 1)] : List FactorBlock).map factorBlockValue).prod) = 36847107955599349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_11
      · exact prime_oneHundredEighteenDL_947
      · exact prime_oneHundredEighteenDL_294767431087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 36847107955599349) ^ 18423553977799674 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (13 : ZMod 36847107955599349) ^ 12282369318533116 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (13 : ZMod 36847107955599349) ^ 3349737086872668 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (13 : ZMod 36847107955599349) ^ 38909300903484 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (13 : ZMod 36847107955599349) ^ 125004 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_39251231201603557 : Nat.Prime 39251231201603557 := by
  apply lucas_primality 39251231201603557 (2 : ZMod 39251231201603557)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (1019, 1), (3631, 1), (5741, 1), (51329, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (1019, 1), (3631, 1), (5741, 1), (51329, 1)] : List FactorBlock).map factorBlockValue).prod) = 39251231201603557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_1019
      · exact prime_oneHundredEighteenDL_3631
      · exact prime_oneHundredEighteenDL_5741
      · exact prime_oneHundredEighteenDL_51329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 39251231201603557) ^ 19625615600801778 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 39251231201603557) ^ 13083743733867852 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 39251231201603557) ^ 38519363298924 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 39251231201603557) ^ 10810033379676 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 39251231201603557) ^ 6837002473716 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 39251231201603557) ^ 764698926564 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_46868033232650351 : Nat.Prime 46868033232650351 := by
  apply lucas_primality 46868033232650351 (13 : ZMod 46868033232650351)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (7, 1), (3243341, 1), (41287261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (7, 1), (3243341, 1), (41287261, 1)] : List FactorBlock).map factorBlockValue).prod) = 46868033232650351 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_5
      · exact prime_oneHundredEighteenDL_7
      · exact prime_oneHundredEighteenDL_3243341
      · exact prime_oneHundredEighteenDL_41287261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 46868033232650351) ^ 23434016616325175 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (13 : ZMod 46868033232650351) ^ 9373606646530070 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (13 : ZMod 46868033232650351) ^ 6695433318950050 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (13 : ZMod 46868033232650351) ^ 14450541350 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (13 : ZMod 46868033232650351) ^ 1135169350 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_52968828295884041 : Nat.Prime 52968828295884041 := by
  apply lucas_primality 52968828295884041 (3 : ZMod 52968828295884041)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (353, 1), (4241, 1), (884539837, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (353, 1), (4241, 1), (884539837, 1)] : List FactorBlock).map factorBlockValue).prod) = 52968828295884041 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_5
      · exact prime_oneHundredEighteenDL_353
      · exact prime_oneHundredEighteenDL_4241
      · exact prime_oneHundredEighteenDL_884539837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 52968828295884041) ^ 26484414147942020 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 52968828295884041) ^ 10593765659176808 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 52968828295884041) ^ 150053337948680 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 52968828295884041) ^ 12489702498440 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 52968828295884041) ^ 59882920 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_62002648740676543 : Nat.Prime 62002648740676543 := by
  apply lucas_primality 62002648740676543 (5 : ZMod 62002648740676543)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (103, 1), (197, 1), (22142553649, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (103, 1), (197, 1), (22142553649, 1)] : List FactorBlock).map factorBlockValue).prod) = 62002648740676543 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_23
      · exact prime_oneHundredEighteenDL_103
      · exact prime_oneHundredEighteenDL_197
      · exact prime_oneHundredEighteenDL_22142553649
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 62002648740676543) ^ 31001324370338271 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 62002648740676543) ^ 20667549580225514 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 62002648740676543) ^ 2695767336551154 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 62002648740676543) ^ 601967463501714 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 62002648740676543) ^ 314734257566886 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 62002648740676543) ^ 2800158 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_70528576446348539 : Nat.Prime 70528576446348539 := by
  apply lucas_primality 70528576446348539 (2 : ZMod 70528576446348539)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (19, 1), (265145024234393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (19, 1), (265145024234393, 1)] : List FactorBlock).map factorBlockValue).prod) = 70528576446348539 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_7
      · exact prime_oneHundredEighteenDL_19
      · exact prime_oneHundredEighteenDL_265145024234393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 70528576446348539) ^ 35264288223174269 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 70528576446348539) ^ 10075510920906934 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 70528576446348539) ^ 3712030339281502 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 70528576446348539) ^ 266 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_131349433898481583 : Nat.Prime 131349433898481583 := by
  apply lucas_primality 131349433898481583 (3 : ZMod 131349433898481583)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (127, 1), (771389, 1), (31922857, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (127, 1), (771389, 1), (31922857, 1)] : List FactorBlock).map factorBlockValue).prod) = 131349433898481583 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_7
      · exact prime_oneHundredEighteenDL_127
      · exact prime_oneHundredEighteenDL_771389
      · exact prime_oneHundredEighteenDL_31922857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 131349433898481583) ^ 65674716949240791 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 131349433898481583) ^ 43783144632827194 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 131349433898481583) ^ 18764204842640226 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 131349433898481583) ^ 1034247511011666 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 131349433898481583) ^ 170276519238 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 131349433898481583) ^ 4114588926 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_153708284343135733 : Nat.Prime 153708284343135733 := by
  apply lucas_primality 153708284343135733 (2 : ZMod 153708284343135733)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (47, 1), (6113, 1), (52837, 1), (120539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (47, 1), (6113, 1), (52837, 1), (120539, 1)] : List FactorBlock).map factorBlockValue).prod) = 153708284343135733 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_7
      · exact prime_oneHundredEighteenDL_47
      · exact prime_oneHundredEighteenDL_6113
      · exact prime_oneHundredEighteenDL_52837
      · exact prime_oneHundredEighteenDL_120539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 153708284343135733) ^ 76854142171567866 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 153708284343135733) ^ 51236094781045244 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 153708284343135733) ^ 21958326334733676 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 153708284343135733) ^ 3270389028577356 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 153708284343135733) ^ 25144492776564 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 153708284343135733) ^ 2909103172836 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 153708284343135733) ^ 1275174709788 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_221419407632785289 : Nat.Prime 221419407632785289 := by
  apply lucas_primality 221419407632785289 (3 : ZMod 221419407632785289)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17, 1), (1628083879652833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17, 1), (1628083879652833, 1)] : List FactorBlock).map factorBlockValue).prod) = 221419407632785289 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_17
      · exact prime_oneHundredEighteenDL_1628083879652833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 221419407632785289) ^ 110709703816392644 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 221419407632785289) ^ 13024671037222664 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 221419407632785289) ^ 136 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_371089853800687997 : Nat.Prime 371089853800687997 := by
  apply lucas_primality 371089853800687997 (2 : ZMod 371089853800687997)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (958319, 1), (7446730517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (958319, 1), (7446730517, 1)] : List FactorBlock).map factorBlockValue).prod) = 371089853800687997 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_13
      · exact prime_oneHundredEighteenDL_958319
      · exact prime_oneHundredEighteenDL_7446730517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 371089853800687997) ^ 185544926900343998 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 371089853800687997) ^ 28545373369283692 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 371089853800687997) ^ 387229986884 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 371089853800687997) ^ 49832588 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_374944265861202809 : Nat.Prime 374944265861202809 := by
  apply lucas_primality 374944265861202809 (3 : ZMod 374944265861202809)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (46868033232650351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (46868033232650351, 1)] : List FactorBlock).map factorBlockValue).prod) = 374944265861202809 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_46868033232650351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 374944265861202809) ^ 187472132930601404 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 374944265861202809) ^ 8 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_642269936486227267 : Nat.Prime 642269936486227267 := by
  apply lucas_primality 642269936486227267 (2 : ZMod 642269936486227267)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (210709, 1), (24191564899, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (210709, 1), (24191564899, 1)] : List FactorBlock).map factorBlockValue).prod) = 642269936486227267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_7
      · exact prime_oneHundredEighteenDL_210709
      · exact prime_oneHundredEighteenDL_24191564899
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 642269936486227267) ^ 321134968243113633 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 642269936486227267) ^ 214089978828742422 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 642269936486227267) ^ 91752848069461038 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 642269936486227267) ^ 3048137177274 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 642269936486227267) ^ 26549334 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_848918644397372183 : Nat.Prime 848918644397372183 := by
  apply lucas_primality 848918644397372183 (5 : ZMod 848918644397372183)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (307, 1), (81329626786489, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (307, 1), (81329626786489, 1)] : List FactorBlock).map factorBlockValue).prod) = 848918644397372183 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_17
      · exact prime_oneHundredEighteenDL_307
      · exact prime_oneHundredEighteenDL_81329626786489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 848918644397372183) ^ 424459322198686091 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 848918644397372183) ^ 49936390846904246 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 848918644397372183) ^ 2765207310740626 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 848918644397372183) ^ 10438 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_922540188552849049 : Nat.Prime 922540188552849049 := by
  apply lucas_primality 922540188552849049 (11 : ZMod 922540188552849049)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (13, 1), (107, 1), (47317, 1), (83431813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (13, 1), (107, 1), (47317, 1), (83431813, 1)] : List FactorBlock).map factorBlockValue).prod) = 922540188552849049 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_7
      · exact prime_oneHundredEighteenDL_13
      · exact prime_oneHundredEighteenDL_107
      · exact prime_oneHundredEighteenDL_47317
      · exact prime_oneHundredEighteenDL_83431813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 922540188552849049) ^ 461270094276424524 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (11 : ZMod 922540188552849049) ^ 307513396184283016 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (11 : ZMod 922540188552849049) ^ 131791455507549864 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (11 : ZMod 922540188552849049) ^ 70964629888680696 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (11 : ZMod 922540188552849049) ^ 8621870921054664 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (11 : ZMod 922540188552849049) ^ 19497013516344 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (11 : ZMod 922540188552849049) ^ 11057415096 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_948767309370762493 : Nat.Prime 948767309370762493 := by
  apply lucas_primality 948767309370762493 (2 : ZMod 948767309370762493)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (6247, 1), (384599, 1), (2531369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (6247, 1), (384599, 1), (2531369, 1)] : List FactorBlock).map factorBlockValue).prod) = 948767309370762493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_13
      · exact prime_oneHundredEighteenDL_6247
      · exact prime_oneHundredEighteenDL_384599
      · exact prime_oneHundredEighteenDL_2531369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 948767309370762493) ^ 474383654685381246 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 948767309370762493) ^ 316255769790254164 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 948767309370762493) ^ 72982100720827884 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 948767309370762493) ^ 151875669820836 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 948767309370762493) ^ 2466900094308 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 948767309370762493) ^ 374804032668 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_981461373057808751 : Nat.Prime 981461373057808751 := by
  apply lucas_primality 981461373057808751 (11 : ZMod 981461373057808751)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 4), (139, 1), (4349, 1), (1298849977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 4), (139, 1), (4349, 1), (1298849977, 1)] : List FactorBlock).map factorBlockValue).prod) = 981461373057808751 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_5
      · exact prime_oneHundredEighteenDL_139
      · exact prime_oneHundredEighteenDL_4349
      · exact prime_oneHundredEighteenDL_1298849977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 981461373057808751) ^ 490730686528904375 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (11 : ZMod 981461373057808751) ^ 196292274611561750 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (11 : ZMod 981461373057808751) ^ 7060873187466250 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (11 : ZMod 981461373057808751) ^ 225675183503750 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (11 : ZMod 981461373057808751) ^ 755638750 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_982575074066965481 : Nat.Prime 982575074066965481 := by
  apply lucas_primality 982575074066965481 (3 : ZMod 982575074066965481)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (24564376851674137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (24564376851674137, 1)] : List FactorBlock).map factorBlockValue).prod) = 982575074066965481 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_5
      · exact prime_oneHundredEighteenDL_24564376851674137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 982575074066965481) ^ 491287537033482740 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 982575074066965481) ^ 196515014813393096 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 982575074066965481) ^ 40 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_1248370449738323557 : Nat.Prime 1248370449738323557 := by
  apply lucas_primality 1248370449738323557 (5 : ZMod 1248370449738323557)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (59, 1), (1763235098500457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (59, 1), (1763235098500457, 1)] : List FactorBlock).map factorBlockValue).prod) = 1248370449738323557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_59
      · exact prime_oneHundredEighteenDL_1763235098500457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1248370449738323557) ^ 624185224869161778 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 1248370449738323557) ^ 416123483246107852 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 1248370449738323557) ^ 21158821182005484 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 1248370449738323557) ^ 708 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_1795031159361207151 : Nat.Prime 1795031159361207151 := by
  apply lucas_primality 1795031159361207151 (3 : ZMod 1795031159361207151)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (11966874395741381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (11966874395741381, 1)] : List FactorBlock).map factorBlockValue).prod) = 1795031159361207151 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_5
      · exact prime_oneHundredEighteenDL_11966874395741381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1795031159361207151) ^ 897515579680603575 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 1795031159361207151) ^ 598343719787069050 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 1795031159361207151) ^ 359006231872241430 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 1795031159361207151) ^ 150 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_2127713160960753727 : Nat.Prime 2127713160960753727 := by
  apply lucas_primality 2127713160960753727 (6 : ZMod 2127713160960753727)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (37, 1), (41, 1), (2447, 1), (95530550279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (37, 1), (41, 1), (2447, 1), (95530550279, 1)] : List FactorBlock).map factorBlockValue).prod) = 2127713160960753727 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_37
      · exact prime_oneHundredEighteenDL_41
      · exact prime_oneHundredEighteenDL_2447
      · exact prime_oneHundredEighteenDL_95530550279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 2127713160960753727) ^ 1063856580480376863 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (6 : ZMod 2127713160960753727) ^ 709237720320251242 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (6 : ZMod 2127713160960753727) ^ 57505761107047398 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (6 : ZMod 2127713160960753727) ^ 51895442950262286 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (6 : ZMod 2127713160960753727) ^ 869519068639458 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (6 : ZMod 2127713160960753727) ^ 22272594 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_2220502305087140441 : Nat.Prime 2220502305087140441 := by
  apply lucas_primality 2220502305087140441 (3 : ZMod 2220502305087140441)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (101, 1), (191, 1), (48017, 1), (59929613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (101, 1), (191, 1), (48017, 1), (59929613, 1)] : List FactorBlock).map factorBlockValue).prod) = 2220502305087140441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_5
      · exact prime_oneHundredEighteenDL_101
      · exact prime_oneHundredEighteenDL_191
      · exact prime_oneHundredEighteenDL_48017
      · exact prime_oneHundredEighteenDL_59929613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2220502305087140441) ^ 1110251152543570220 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 444100461017428088 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 21985171337496440 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 11625666518780840 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 46244086575320 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 37051837880 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_2238348915709888151 : Nat.Prime 2238348915709888151 := by
  apply lucas_primality 2238348915709888151 (7 : ZMod 2238348915709888151)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (13, 1), (101, 1), (263, 1), (11027, 1), (11756551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (13, 1), (101, 1), (263, 1), (11027, 1), (11756551, 1)] : List FactorBlock).map factorBlockValue).prod) = 2238348915709888151 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_5
      · exact prime_oneHundredEighteenDL_13
      · exact prime_oneHundredEighteenDL_101
      · exact prime_oneHundredEighteenDL_263
      · exact prime_oneHundredEighteenDL_11027
      · exact prime_oneHundredEighteenDL_11756551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 2238348915709888151) ^ 1119174457854944075 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (7 : ZMod 2238348915709888151) ^ 447669783141977630 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (7 : ZMod 2238348915709888151) ^ 172180685823837550 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (7 : ZMod 2238348915709888151) ^ 22161870452573150 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (7 : ZMod 2238348915709888151) ^ 8510832379125050 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (7 : ZMod 2238348915709888151) ^ 202988021738450 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (7 : ZMod 2238348915709888151) ^ 190391630650 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_5480761894697962861 : Nat.Prime 5480761894697962861 := by
  apply lucas_primality 5480761894697962861 (6 : ZMod 5480761894697962861)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (13, 1), (479, 1), (4657, 1), (3149956679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (13, 1), (479, 1), (4657, 1), (3149956679, 1)] : List FactorBlock).map factorBlockValue).prod) = 5480761894697962861 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_5
      · exact prime_oneHundredEighteenDL_13
      · exact prime_oneHundredEighteenDL_479
      · exact prime_oneHundredEighteenDL_4657
      · exact prime_oneHundredEighteenDL_3149956679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 5480761894697962861) ^ 2740380947348981430 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (6 : ZMod 5480761894697962861) ^ 1826920631565987620 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (6 : ZMod 5480761894697962861) ^ 1096152378939592572 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (6 : ZMod 5480761894697962861) ^ 421597068822920220 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (6 : ZMod 5480761894697962861) ^ 11442091638200340 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (6 : ZMod 5480761894697962861) ^ 1176886814407980 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (6 : ZMod 5480761894697962861) ^ 1739948340 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_13029096451298904283 : Nat.Prime 13029096451298904283 := by
  apply lucas_primality 13029096451298904283 (2 : ZMod 13029096451298904283)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (311, 1), (2031691, 1), (3436726747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (311, 1), (2031691, 1), (3436726747, 1)] : List FactorBlock).map factorBlockValue).prod) = 13029096451298904283 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_311
      · exact prime_oneHundredEighteenDL_2031691
      · exact prime_oneHundredEighteenDL_3436726747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 13029096451298904283) ^ 6514548225649452141 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 13029096451298904283) ^ 4343032150432968094 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 13029096451298904283) ^ 41894200808035062 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 13029096451298904283) ^ 6412932109902 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 13029096451298904283) ^ 3791135406 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_20091703527913509113 : Nat.Prime 20091703527913509113 := by
  apply lucas_primality 20091703527913509113 (3 : ZMod 20091703527913509113)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (461, 1), (811, 1), (89137, 1), (75361057, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (461, 1), (811, 1), (89137, 1), (75361057, 1)] : List FactorBlock).map factorBlockValue).prod) = 20091703527913509113 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_461
      · exact prime_oneHundredEighteenDL_811
      · exact prime_oneHundredEighteenDL_89137
      · exact prime_oneHundredEighteenDL_75361057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 20091703527913509113) ^ 10045851763956754556 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 20091703527913509113) ^ 43582870993304792 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 20091703527913509113) ^ 24773987087439592 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 20091703527913509113) ^ 225402509933176 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 20091703527913509113) ^ 266605914616 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_22391302942731690263 : Nat.Prime 22391302942731690263 := by
  apply lucas_primality 22391302942731690263 (5 : ZMod 22391302942731690263)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2089, 1), (24121, 1), (222185453099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2089, 1), (24121, 1), (222185453099, 1)] : List FactorBlock).map factorBlockValue).prod) = 22391302942731690263 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_2089
      · exact prime_oneHundredEighteenDL_24121
      · exact prime_oneHundredEighteenDL_222185453099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 22391302942731690263) ^ 11195651471365845131 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 22391302942731690263) ^ 10718670628401958 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 22391302942731690263) ^ 928290823047622 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 22391302942731690263) ^ 100777538 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_49934817989532942281 : Nat.Prime 49934817989532942281 := by
  apply lucas_primality 49934817989532942281 (3 : ZMod 49934817989532942281)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (1248370449738323557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (1248370449738323557, 1)] : List FactorBlock).map factorBlockValue).prod) = 49934817989532942281 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_5
      · exact prime_oneHundredEighteenDL_1248370449738323557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 49934817989532942281) ^ 24967408994766471140 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 49934817989532942281) ^ 9986963597906588456 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 49934817989532942281) ^ 40 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_53950674664843090429 : Nat.Prime 53950674664843090429 := by
  apply lucas_primality 53950674664843090429 (2 : ZMod 53950674664843090429)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (642269936486227267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (642269936486227267, 1)] : List FactorBlock).map factorBlockValue).prod) = 53950674664843090429 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_7
      · exact prime_oneHundredEighteenDL_642269936486227267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 53950674664843090429) ^ 26975337332421545214 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 53950674664843090429) ^ 17983558221614363476 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 53950674664843090429) ^ 7707239237834727204 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 53950674664843090429) ^ 84 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_55290560849083829083 : Nat.Prime 55290560849083829083 := by
  apply lucas_primality 55290560849083829083 (2 : ZMod 55290560849083829083)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (9203, 1), (91028552693759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (9203, 1), (91028552693759, 1)] : List FactorBlock).map factorBlockValue).prod) = 55290560849083829083 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_11
      · exact prime_oneHundredEighteenDL_9203
      · exact prime_oneHundredEighteenDL_91028552693759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 55290560849083829083) ^ 27645280424541914541 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 55290560849083829083) ^ 18430186949694609694 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 55290560849083829083) ^ 5026414622643984462 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 55290560849083829083) ^ 6007884477788094 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 55290560849083829083) ^ 607398 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_80575765695478656139 : Nat.Prime 80575765695478656139 := by
  apply lucas_primality 80575765695478656139 (2 : ZMod 80575765695478656139)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (73, 1), (48767, 1), (3772283211553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (73, 1), (48767, 1), (3772283211553, 1)] : List FactorBlock).map factorBlockValue).prod) = 80575765695478656139 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_73
      · exact prime_oneHundredEighteenDL_48767
      · exact prime_oneHundredEighteenDL_3772283211553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 80575765695478656139) ^ 40287882847739328069 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 80575765695478656139) ^ 26858588565159552046 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 80575765695478656139) ^ 1103777612266830906 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 80575765695478656139) ^ 1652260046660214 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 80575765695478656139) ^ 21359946 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_186297808204524070801 : Nat.Prime 186297808204524070801 := by
  apply lucas_primality 186297808204524070801 (7 : ZMod 186297808204524070801)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (5, 2), (233, 1), (619, 1), (2113, 1), (6269, 1), (9029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (5, 2), (233, 1), (619, 1), (2113, 1), (6269, 1), (9029, 1)] : List FactorBlock).map factorBlockValue).prod) = 186297808204524070801 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_5
      · exact prime_oneHundredEighteenDL_233
      · exact prime_oneHundredEighteenDL_619
      · exact prime_oneHundredEighteenDL_2113
      · exact prime_oneHundredEighteenDL_6269
      · exact prime_oneHundredEighteenDL_9029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 186297808204524070801) ^ 93148904102262035400 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (7 : ZMod 186297808204524070801) ^ 62099269401508023600 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (7 : ZMod 186297808204524070801) ^ 37259561640904814160 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (7 : ZMod 186297808204524070801) ^ 799561408603107600 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (7 : ZMod 186297808204524070801) ^ 300965764466113200 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (7 : ZMod 186297808204524070801) ^ 88167443542131600 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (7 : ZMod 186297808204524070801) ^ 29717308694293200 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (7 : ZMod 186297808204524070801) ^ 20633271481285200 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_343964318895525651503 : Nat.Prime 343964318895525651503 := by
  apply lucas_primality 343964318895525651503 (5 : ZMod 343964318895525651503)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (5189, 1), (9133, 1), (88512052703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (5189, 1), (9133, 1), (88512052703, 1)] : List FactorBlock).map factorBlockValue).prod) = 343964318895525651503 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_41
      · exact prime_oneHundredEighteenDL_5189
      · exact prime_oneHundredEighteenDL_9133
      · exact prime_oneHundredEighteenDL_88512052703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 343964318895525651503) ^ 171982159447762825751 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 343964318895525651503) ^ 8389373631598186622 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 343964318895525651503) ^ 66287207341592918 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 343964318895525651503) ^ 37661701401021094 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 343964318895525651503) ^ 3886073234 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_361117783570042550867 : Nat.Prime 361117783570042550867 := by
  apply lucas_primality 361117783570042550867 (2 : ZMod 361117783570042550867)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (603610541, 1), (15743760127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (603610541, 1), (15743760127, 1)] : List FactorBlock).map factorBlockValue).prod) = 361117783570042550867 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_19
      · exact prime_oneHundredEighteenDL_603610541
      · exact prime_oneHundredEighteenDL_15743760127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 361117783570042550867) ^ 180558891785021275433 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 361117783570042550867) ^ 19006199135265397414 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 361117783570042550867) ^ 598262884826 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 361117783570042550867) ^ 22937200558 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_741977877887111147467 : Nat.Prime 741977877887111147467 := by
  apply lucas_primality 741977877887111147467 (2 : ZMod 741977877887111147467)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (6569, 1), (18825236664309919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (6569, 1), (18825236664309919, 1)] : List FactorBlock).map factorBlockValue).prod) = 741977877887111147467 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_6569
      · exact prime_oneHundredEighteenDL_18825236664309919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 741977877887111147467) ^ 370988938943555573733 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 741977877887111147467) ^ 247325959295703715822 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 741977877887111147467) ^ 112951419985859514 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 741977877887111147467) ^ 39414 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_785732324217339970699 : Nat.Prime 785732324217339970699 := by
  apply lucas_primality 785732324217339970699 (3 : ZMod 785732324217339970699)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (61, 1), (163, 1), (5077, 1), (48091, 1), (53942983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (61, 1), (163, 1), (5077, 1), (48091, 1), (53942983, 1)] : List FactorBlock).map factorBlockValue).prod) = 785732324217339970699 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_61
      · exact prime_oneHundredEighteenDL_163
      · exact prime_oneHundredEighteenDL_5077
      · exact prime_oneHundredEighteenDL_48091
      · exact prime_oneHundredEighteenDL_53942983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 785732324217339970699) ^ 392866162108669985349 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 785732324217339970699) ^ 261910774739113323566 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 785732324217339970699) ^ 12880857774054753618 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 785732324217339970699) ^ 4820443706854846446 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 785732324217339970699) ^ 154763112904735074 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 785732324217339970699) ^ 16338448446015678 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 785732324217339970699) ^ 14565978381606 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_832249527175714647823 : Nat.Prime 832249527175714647823 := by
  apply lucas_primality 832249527175714647823 (3 : ZMod 832249527175714647823)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 1), (67, 1), (226618069, 1), (315017711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 1), (67, 1), (226618069, 1), (315017711, 1)] : List FactorBlock).map factorBlockValue).prod) = 832249527175714647823 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_29
      · exact prime_oneHundredEighteenDL_67
      · exact prime_oneHundredEighteenDL_226618069
      · exact prime_oneHundredEighteenDL_315017711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 832249527175714647823) ^ 416124763587857323911 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 832249527175714647823) ^ 277416509058571549274 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 832249527175714647823) ^ 28698259557783263718 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 832249527175714647823) ^ 12421634733965890266 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 832249527175714647823) ^ 3672476474838 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 832249527175714647823) ^ 2641913448402 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_886148666952292168463 : Nat.Prime 886148666952292168463 := by
  apply lucas_primality 886148666952292168463 (5 : ZMod 886148666952292168463)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (467, 1), (948767309370762493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (467, 1), (948767309370762493, 1)] : List FactorBlock).map factorBlockValue).prod) = 886148666952292168463 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_467
      · exact prime_oneHundredEighteenDL_948767309370762493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 886148666952292168463) ^ 443074333476146084231 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 886148666952292168463) ^ 1897534618741524986 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 886148666952292168463) ^ 934 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_1211741626297785245891 : Nat.Prime 1211741626297785245891 := by
  apply lucas_primality 1211741626297785245891 (2 : ZMod 1211741626297785245891)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (59, 1), (61, 1), (1997, 1), (16859710603663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (59, 1), (61, 1), (1997, 1), (16859710603663, 1)] : List FactorBlock).map factorBlockValue).prod) = 1211741626297785245891 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_5
      · exact prime_oneHundredEighteenDL_59
      · exact prime_oneHundredEighteenDL_61
      · exact prime_oneHundredEighteenDL_1997
      · exact prime_oneHundredEighteenDL_16859710603663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1211741626297785245891) ^ 605870813148892622945 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1211741626297785245891) ^ 242348325259557049178 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1211741626297785245891) ^ 20537993666064156710 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1211741626297785245891) ^ 19864616824553856490 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1211741626297785245891) ^ 606780984625831370 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1211741626297785245891) ^ 71872030 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_1302909940455385496303 : Nat.Prime 1302909940455385496303 := by
  apply lucas_primality 1302909940455385496303 (5 : ZMod 1302909940455385496303)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (79, 1), (17491, 1), (643493, 1), (732653863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (79, 1), (17491, 1), (643493, 1), (732653863, 1)] : List FactorBlock).map factorBlockValue).prod) = 1302909940455385496303 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_79
      · exact prime_oneHundredEighteenDL_17491
      · exact prime_oneHundredEighteenDL_643493
      · exact prime_oneHundredEighteenDL_732653863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1302909940455385496303) ^ 651454970227692748151 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 1302909940455385496303) ^ 16492530891840322738 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 1302909940455385496303) ^ 74490305897626522 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 1302909940455385496303) ^ 2024746097401814 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 1302909940455385496303) ^ 1778343097954 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_1601414747245158361843 : Nat.Prime 1601414747245158361843 := by
  apply lucas_primality 1601414747245158361843 (2 : ZMod 1601414747245158361843)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (137, 1), (333497, 1), (5841711089363, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (137, 1), (333497, 1), (5841711089363, 1)] : List FactorBlock).map factorBlockValue).prod) = 1601414747245158361843 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_137
      · exact prime_oneHundredEighteenDL_333497
      · exact prime_oneHundredEighteenDL_5841711089363
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1601414747245158361843) ^ 800707373622579180921 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1601414747245158361843) ^ 533804915748386120614 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1601414747245158361843) ^ 11689158739015754466 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1601414747245158361843) ^ 4801886515456386 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1601414747245158361843) ^ 274134534 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_7860976507599834474551 : Nat.Prime 7860976507599834474551 := by
  apply lucas_primality 7860976507599834474551 (11 : ZMod 7860976507599834474551)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (11892496163, 1), (13220061457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (11892496163, 1), (13220061457, 1)] : List FactorBlock).map factorBlockValue).prod) = 7860976507599834474551 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_5
      · exact prime_oneHundredEighteenDL_11892496163
      · exact prime_oneHundredEighteenDL_13220061457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 7860976507599834474551) ^ 3930488253799917237275 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (11 : ZMod 7860976507599834474551) ^ 1572195301519966894910 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (11 : ZMod 7860976507599834474551) ^ 661003072850 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (11 : ZMod 7860976507599834474551) ^ 594624808150 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_12265197154357440736901 : Nat.Prime 12265197154357440736901 := by
  apply lucas_primality 12265197154357440736901 (2 : ZMod 12265197154357440736901)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (31, 1), (131, 1), (257, 1), (8796187, 1), (13360231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (31, 1), (131, 1), (257, 1), (8796187, 1), (13360231, 1)] : List FactorBlock).map factorBlockValue).prod) = 12265197154357440736901 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_5
      · exact prime_oneHundredEighteenDL_31
      · exact prime_oneHundredEighteenDL_131
      · exact prime_oneHundredEighteenDL_257
      · exact prime_oneHundredEighteenDL_8796187
      · exact prime_oneHundredEighteenDL_13360231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 12265197154357440736901) ^ 6132598577178720368450 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 12265197154357440736901) ^ 2453039430871488147380 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 12265197154357440736901) ^ 395651521108304539900 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 12265197154357440736901) ^ 93627459193568249900 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 12265197154357440736901) ^ 47724502546137901700 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 12265197154357440736901) ^ 1394376580938700 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 12265197154357440736901) ^ 918037805959900 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_13724676363356102917379 : Nat.Prime 13724676363356102917379 := by
  apply lucas_primality 13724676363356102917379 (2 : ZMod 13724676363356102917379)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (82370699, 1), (83310427919011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (82370699, 1), (83310427919011, 1)] : List FactorBlock).map factorBlockValue).prod) = 13724676363356102917379 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_82370699
      · exact prime_oneHundredEighteenDL_83310427919011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 13724676363356102917379) ^ 6862338181678051458689 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 13724676363356102917379) ^ 166620855838022 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 13724676363356102917379) ^ 164741398 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_14618785327397941098821 : Nat.Prime 14618785327397941098821 := by
  apply lucas_primality 14618785327397941098821 (2 : ZMod 14618785327397941098821)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (17, 1), (263, 1), (479, 1), (341303789052949, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (17, 1), (263, 1), (479, 1), (341303789052949, 1)] : List FactorBlock).map factorBlockValue).prod) = 14618785327397941098821 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_5
      · exact prime_oneHundredEighteenDL_17
      · exact prime_oneHundredEighteenDL_263
      · exact prime_oneHundredEighteenDL_479
      · exact prime_oneHundredEighteenDL_341303789052949
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 14618785327397941098821) ^ 7309392663698970549410 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 14618785327397941098821) ^ 2923757065479588219764 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 14618785327397941098821) ^ 859928548670467123460 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 14618785327397941098821) ^ 55584735085163274140 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 14618785327397941098821) ^ 30519384817114699580 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 14618785327397941098821) ^ 42832180 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_22849763148985729155967 : Nat.Prime 22849763148985729155967 := by
  apply lucas_primality 22849763148985729155967 (3 : ZMod 22849763148985729155967)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (13, 1), (29, 1), (89971993, 1), (4158320863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (13, 1), (29, 1), (89971993, 1), (4158320863, 1)] : List FactorBlock).map factorBlockValue).prod) = 22849763148985729155967 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_13
      · exact prime_oneHundredEighteenDL_29
      · exact prime_oneHundredEighteenDL_89971993
      · exact prime_oneHundredEighteenDL_4158320863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 22849763148985729155967) ^ 11424881574492864577983 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 22849763148985729155967) ^ 7616587716328576385322 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 22849763148985729155967) ^ 1757674088383517627382 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 22849763148985729155967) ^ 787922867206404453654 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 22849763148985729155967) ^ 253965288386862 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 22849763148985729155967) ^ 5494949500482 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_26129260470037911885317 : Nat.Prime 26129260470037911885317 := by
  apply lucas_primality 26129260470037911885317 (2 : ZMod 26129260470037911885317)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (37, 1), (5939, 1), (160813, 1), (184854881531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (37, 1), (5939, 1), (160813, 1), (184854881531, 1)] : List FactorBlock).map factorBlockValue).prod) = 26129260470037911885317 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_37
      · exact prime_oneHundredEighteenDL_5939
      · exact prime_oneHundredEighteenDL_160813
      · exact prime_oneHundredEighteenDL_184854881531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 26129260470037911885317) ^ 13064630235018955942658 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 26129260470037911885317) ^ 706196228919943564468 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 26129260470037911885317) ^ 4399606073419416044 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 26129260470037911885317) ^ 162482264929066132 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 26129260470037911885317) ^ 141350124236 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_29957171560152927216001 : Nat.Prime 29957171560152927216001 := by
  apply lucas_primality 29957171560152927216001 (26 : ZMod 29957171560152927216001)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (5, 3), (7, 1), (67, 1), (419, 1), (571, 1), (16421, 1), (338717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (5, 3), (7, 1), (67, 1), (419, 1), (571, 1), (16421, 1), (338717, 1)] : List FactorBlock).map factorBlockValue).prod) = 29957171560152927216001 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_5
      · exact prime_oneHundredEighteenDL_7
      · exact prime_oneHundredEighteenDL_67
      · exact prime_oneHundredEighteenDL_419
      · exact prime_oneHundredEighteenDL_571
      · exact prime_oneHundredEighteenDL_16421
      · exact prime_oneHundredEighteenDL_338717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (26 : ZMod 29957171560152927216001) ^ 14978585780076463608000 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (26 : ZMod 29957171560152927216001) ^ 9985723853384309072000 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (26 : ZMod 29957171560152927216001) ^ 5991434312030585443200 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (26 : ZMod 29957171560152927216001) ^ 4279595937164703888000 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (26 : ZMod 29957171560152927216001) ^ 447121963584372048000 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (26 : ZMod 29957171560152927216001) ^ 71496829499171664000 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (26 : ZMod 29957171560152927216001) ^ 52464398529164496000 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (26 : ZMod 29957171560152927216001) ^ 1824320781934896000 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (26 : ZMod 29957171560152927216001) ^ 88443070646448000 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_40430555721944598462487 : Nat.Prime 40430555721944598462487 := by
  apply lucas_primality 40430555721944598462487 (5 : ZMod 40430555721944598462487)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (17, 1), (202621, 1), (150481022080241, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (17, 1), (202621, 1), (150481022080241, 1)] : List FactorBlock).map factorBlockValue).prod) = 40430555721944598462487 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_13
      · exact prime_oneHundredEighteenDL_17
      · exact prime_oneHundredEighteenDL_202621
      · exact prime_oneHundredEighteenDL_150481022080241
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 40430555721944598462487) ^ 20215277860972299231243 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 40430555721944598462487) ^ 13476851907314866154162 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 40430555721944598462487) ^ 3110042747841892189422 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 40430555721944598462487) ^ 2378267983643799909558 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 40430555721944598462487) ^ 199537835278399566 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 40430555721944598462487) ^ 268675446 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_50277862106991688000757 : Nat.Prime 50277862106991688000757 := by
  apply lucas_primality 50277862106991688000757 (2 : ZMod 50277862106991688000757)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 2), (401, 1), (17623, 1), (3362303597867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 2), (401, 1), (17623, 1), (3362303597867, 1)] : List FactorBlock).map factorBlockValue).prod) = 50277862106991688000757 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_23
      · exact prime_oneHundredEighteenDL_401
      · exact prime_oneHundredEighteenDL_17623
      · exact prime_oneHundredEighteenDL_3362303597867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 50277862106991688000757) ^ 25138931053495844000378 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 50277862106991688000757) ^ 2185994004651812521772 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 50277862106991688000757) ^ 125381202261824658356 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 50277862106991688000757) ^ 2852968399647715372 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 50277862106991688000757) ^ 14953397468 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_57328037380036961837333 : Nat.Prime 57328037380036961837333 := by
  apply lucas_primality 57328037380036961837333 (2 : ZMod 57328037380036961837333)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (1302909940455385496303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (1302909940455385496303, 1)] : List FactorBlock).map factorBlockValue).prod) = 57328037380036961837333 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_11
      · exact prime_oneHundredEighteenDL_1302909940455385496303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 57328037380036961837333) ^ 28664018690018480918666 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 57328037380036961837333) ^ 5211639761821541985212 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 57328037380036961837333) ^ 44 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_67574011280201077079807 : Nat.Prime 67574011280201077079807 := by
  apply lucas_primality 67574011280201077079807 (5 : ZMod 67574011280201077079807)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 3), (17, 1), (71, 1), (109, 1), (257, 1), (863, 1), (1583, 1), (2132539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 3), (17, 1), (71, 1), (109, 1), (257, 1), (863, 1), (1583, 1), (2132539, 1)] : List FactorBlock).map factorBlockValue).prod) = 67574011280201077079807 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_7
      · exact prime_oneHundredEighteenDL_17
      · exact prime_oneHundredEighteenDL_71
      · exact prime_oneHundredEighteenDL_109
      · exact prime_oneHundredEighteenDL_257
      · exact prime_oneHundredEighteenDL_863
      · exact prime_oneHundredEighteenDL_1583
      · exact prime_oneHundredEighteenDL_2132539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 67574011280201077079807) ^ 33787005640100538539903 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 67574011280201077079807) ^ 9653430182885868154258 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 67574011280201077079807) ^ 3974941840011828063518 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 67574011280201077079807) ^ 951746637749310944786 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 67574011280201077079807) ^ 619945057616523642934 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 67574011280201077079807) ^ 262933896031910805758 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 67574011280201077079807) ^ 78301287694323380162 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 67574011280201077079807) ^ 42687309715856650082 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 67574011280201077079807) ^ 31687116287299354 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_85325579004877698281923 : Nat.Prime 85325579004877698281923 := by
  apply lucas_primality 85325579004877698281923 (2 : ZMod 85325579004877698281923)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (19, 1), (107, 1), (113, 1), (20634355892009401, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (19, 1), (107, 1), (113, 1), (20634355892009401, 1)] : List FactorBlock).map factorBlockValue).prod) = 85325579004877698281923 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_19
      · exact prime_oneHundredEighteenDL_107
      · exact prime_oneHundredEighteenDL_113
      · exact prime_oneHundredEighteenDL_20634355892009401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 85325579004877698281923) ^ 42662789502438849140961 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 85325579004877698281923) ^ 28441859668292566093974 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 85325579004877698281923) ^ 4490819947625142014838 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 85325579004877698281923) ^ 797435317802595311046 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 85325579004877698281923) ^ 755093619512192020194 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 85325579004877698281923) ^ 4135122 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_130644687377154277420417 : Nat.Prime 130644687377154277420417 := by
  apply lucas_primality 130644687377154277420417 (5 : ZMod 130644687377154277420417)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 6), (223, 1), (372149, 1), (16870678009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 6), (223, 1), (372149, 1), (16870678009, 1)] : List FactorBlock).map factorBlockValue).prod) = 130644687377154277420417 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_223
      · exact prime_oneHundredEighteenDL_372149
      · exact prime_oneHundredEighteenDL_16870678009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 130644687377154277420417) ^ 65322343688577138710208 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 130644687377154277420417) ^ 43548229125718092473472 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 130644687377154277420417) ^ 585850616041050571392 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 130644687377154277420417) ^ 351054785521805184 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 130644687377154277420417) ^ 7743890749824 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_264433086524935073215297 : Nat.Prime 264433086524935073215297 := by
  apply lucas_primality 264433086524935073215297 (15 : ZMod 264433086524935073215297)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (123923963, 1), (3704571807967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (123923963, 1), (3704571807967, 1)] : List FactorBlock).map factorBlockValue).prod) = 264433086524935073215297 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_123923963
      · exact prime_oneHundredEighteenDL_3704571807967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (15 : ZMod 264433086524935073215297) ^ 132216543262467536607648 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (15 : ZMod 264433086524935073215297) ^ 88144362174978357738432 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (15 : ZMod 264433086524935073215297) ^ 2133833361388992 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (15 : ZMod 264433086524935073215297) ^ 71380202688 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_703890069497883632010599 : Nat.Prime 703890069497883632010599 := by
  apply lucas_primality 703890069497883632010599 (7 : ZMod 703890069497883632010599)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (50277862106991688000757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (50277862106991688000757, 1)] : List FactorBlock).map factorBlockValue).prod) = 703890069497883632010599 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_7
      · exact prime_oneHundredEighteenDL_50277862106991688000757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 703890069497883632010599) ^ 351945034748941816005299 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (7 : ZMod 703890069497883632010599) ^ 100555724213983376001514 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (7 : ZMod 703890069497883632010599) ^ 14 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_1474148234542172602881997 : Nat.Prime 1474148234542172602881997 := by
  apply lucas_primality 1474148234542172602881997 (2 : ZMod 1474148234542172602881997)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (11, 1), (23, 1), (53950674664843090429, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (11, 1), (23, 1), (53950674664843090429, 1)] : List FactorBlock).map factorBlockValue).prod) = 1474148234542172602881997 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_11
      · exact prime_oneHundredEighteenDL_23
      · exact prime_oneHundredEighteenDL_53950674664843090429
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1474148234542172602881997) ^ 737074117271086301440998 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1474148234542172602881997) ^ 491382744847390867627332 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1474148234542172602881997) ^ 134013475867470236625636 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1474148234542172602881997) ^ 64093401501833591429652 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 1474148234542172602881997) ^ 27324 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_1517837630822232640420627 : Nat.Prime 1517837630822232640420627 := by
  apply lucas_primality 1517837630822232640420627 (3 : ZMod 1517837630822232640420627)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 5), (7, 1), (2647, 1), (1054853, 1), (159788353943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 5), (7, 1), (2647, 1), (1054853, 1), (159788353943, 1)] : List FactorBlock).map factorBlockValue).prod) = 1517837630822232640420627 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_7
      · exact prime_oneHundredEighteenDL_2647
      · exact prime_oneHundredEighteenDL_1054853
      · exact prime_oneHundredEighteenDL_159788353943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1517837630822232640420627) ^ 758918815411116320210313 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 1517837630822232640420627) ^ 505945876940744213473542 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 1517837630822232640420627) ^ 216833947260318948631518 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 1517837630822232640420627) ^ 573418069823283959358 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 1517837630822232640420627) ^ 1438909147361985642 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 1517837630822232640420627) ^ 9499050421182 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_2894586528428356013908637 : Nat.Prime 2894586528428356013908637 := by
  apply lucas_primality 2894586528428356013908637 (2 : ZMod 2894586528428356013908637)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (59, 1), (12265197154357440736901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (59, 1), (12265197154357440736901, 1)] : List FactorBlock).map factorBlockValue).prod) = 2894586528428356013908637 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_59
      · exact prime_oneHundredEighteenDL_12265197154357440736901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2894586528428356013908637) ^ 1447293264214178006954318 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 2894586528428356013908637) ^ 49060788617429762947604 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 2894586528428356013908637) ^ 236 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_3084810992484809978028053 : Nat.Prime 3084810992484809978028053 := by
  apply lucas_primality 3084810992484809978028053 (2 : ZMod 3084810992484809978028053)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (31, 1), (21355949, 1), (1164898268108327, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (31, 1), (21355949, 1), (1164898268108327, 1)] : List FactorBlock).map factorBlockValue).prod) = 3084810992484809978028053 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_31
      · exact prime_oneHundredEighteenDL_21355949
      · exact prime_oneHundredEighteenDL_1164898268108327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3084810992484809978028053) ^ 1542405496242404989014026 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 3084810992484809978028053) ^ 99510032015639031549292 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 3084810992484809978028053) ^ 144447385245432548 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 3084810992484809978028053) ^ 2648137676 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_3175460185376210284896107 : Nat.Prime 3175460185376210284896107 := by
  apply lucas_primality 3175460185376210284896107 (2 : ZMod 3175460185376210284896107)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (53, 1), (29957171560152927216001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (53, 1), (29957171560152927216001, 1)] : List FactorBlock).map factorBlockValue).prod) = 3175460185376210284896107 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_53
      · exact prime_oneHundredEighteenDL_29957171560152927216001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3175460185376210284896107) ^ 1587730092688105142448053 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 3175460185376210284896107) ^ 59914343120305854432002 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 3175460185376210284896107) ^ 106 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_5985904587837168387811751 : Nat.Prime 5985904587837168387811751 := by
  apply lucas_primality 5985904587837168387811751 (7 : ZMod 5985904587837168387811751)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 3), (19, 1), (563, 1), (2238348915709888151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 3), (19, 1), (563, 1), (2238348915709888151, 1)] : List FactorBlock).map factorBlockValue).prod) = 5985904587837168387811751 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_5
      · exact prime_oneHundredEighteenDL_19
      · exact prime_oneHundredEighteenDL_563
      · exact prime_oneHundredEighteenDL_2238348915709888151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 5985904587837168387811751) ^ 2992952293918584193905875 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (7 : ZMod 5985904587837168387811751) ^ 1197180917567433677562350 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (7 : ZMod 5985904587837168387811751) ^ 315047609886166757253250 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (7 : ZMod 5985904587837168387811751) ^ 10632157349621968717250 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (7 : ZMod 5985904587837168387811751) ^ 2674250 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_36011226722801509149803993 : Nat.Prime 36011226722801509149803993 := by
  apply lucas_primality 36011226722801509149803993 (3 : ZMod 36011226722801509149803993)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (197, 1), (22849763148985729155967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (197, 1), (22849763148985729155967, 1)] : List FactorBlock).map factorBlockValue).prod) = 36011226722801509149803993 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_197
      · exact prime_oneHundredEighteenDL_22849763148985729155967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 36011226722801509149803993) ^ 18005613361400754574901996 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 36011226722801509149803993) ^ 182798105191885833247736 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 36011226722801509149803993) ^ 1576 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_136504395620482432922055449 : Nat.Prime 136504395620482432922055449 := by
  apply lucas_primality 136504395620482432922055449 (3 : ZMod 136504395620482432922055449)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (59, 1), (223, 1), (53161, 1), (24395326390228303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (59, 1), (223, 1), (53161, 1), (24395326390228303, 1)] : List FactorBlock).map factorBlockValue).prod) = 136504395620482432922055449 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_59
      · exact prime_oneHundredEighteenDL_223
      · exact prime_oneHundredEighteenDL_53161
      · exact prime_oneHundredEighteenDL_24395326390228303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 136504395620482432922055449) ^ 68252197810241216461027724 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 136504395620482432922055449) ^ 2313633824075973439356872 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 136504395620482432922055449) ^ 612127334620997457049576 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 136504395620482432922055449) ^ 2567754474529870260568 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 136504395620482432922055449) ^ 5595514216 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_139647139463596643089430099 : Nat.Prime 139647139463596643089430099 := by
  apply lucas_primality 139647139463596643089430099 (2 : ZMod 139647139463596643089430099)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (157, 1), (40430555721944598462487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (157, 1), (40430555721944598462487, 1)] : List FactorBlock).map factorBlockValue).prod) = 139647139463596643089430099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_11
      · exact prime_oneHundredEighteenDL_157
      · exact prime_oneHundredEighteenDL_40430555721944598462487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 139647139463596643089430099) ^ 69823569731798321544715049 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 139647139463596643089430099) ^ 12695194496690603917220918 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 139647139463596643089430099) ^ 889472225882781166174714 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 139647139463596643089430099) ^ 3454 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_173949491675976367140075647 : Nat.Prime 173949491675976367140075647 := by
  apply lucas_primality 173949491675976367140075647 (5 : ZMod 173949491675976367140075647)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (59, 1), (1474148234542172602881997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (59, 1), (1474148234542172602881997, 1)] : List FactorBlock).map factorBlockValue).prod) = 173949491675976367140075647 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_59
      · exact prime_oneHundredEighteenDL_1474148234542172602881997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 173949491675976367140075647) ^ 86974745837988183570037823 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 173949491675976367140075647) ^ 2948296469084345205763994 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 173949491675976367140075647) ^ 118 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_792656206387119582081481073 : Nat.Prime 792656206387119582081481073 := by
  apply lucas_primality 792656206387119582081481073 (3 : ZMod 792656206387119582081481073)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (11, 1), (293, 1), (234078697, 1), (65666320948057, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (11, 1), (293, 1), (234078697, 1), (65666320948057, 1)] : List FactorBlock).map factorBlockValue).prod) = 792656206387119582081481073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_11
      · exact prime_oneHundredEighteenDL_293
      · exact prime_oneHundredEighteenDL_234078697
      · exact prime_oneHundredEighteenDL_65666320948057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 792656206387119582081481073) ^ 396328103193559791040740536 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 792656206387119582081481073) ^ 72059655126101780189225552 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 792656206387119582081481073) ^ 2705311284597677754544304 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 792656206387119582081481073) ^ 3386280838649403376 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 792656206387119582081481073) ^ 12070970246896 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_1116059938593064371570725351 : Nat.Prime 1116059938593064371570725351 := by
  apply lucas_primality 1116059938593064371570725351 (11 : ZMod 1116059938593064371570725351)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (25189, 1), (886148666952292168463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (25189, 1), (886148666952292168463, 1)] : List FactorBlock).map factorBlockValue).prod) = 1116059938593064371570725351 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_5
      · exact prime_oneHundredEighteenDL_25189
      · exact prime_oneHundredEighteenDL_886148666952292168463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 1116059938593064371570725351) ^ 558029969296532185785362675 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (11 : ZMod 1116059938593064371570725351) ^ 223211987718612874314145070 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (11 : ZMod 1116059938593064371570725351) ^ 44307433347614608423150 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (11 : ZMod 1116059938593064371570725351) ^ 1259450 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_2447499865335667481514748577 : Nat.Prime 2447499865335667481514748577 := by
  apply lucas_primality 2447499865335667481514748577 (3 : ZMod 2447499865335667481514748577)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (17, 1), (79, 1), (12575621651, 1), (4528634000201, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (17, 1), (79, 1), (12575621651, 1), (4528634000201, 1)] : List FactorBlock).map factorBlockValue).prod) = 2447499865335667481514748577 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_17
      · exact prime_oneHundredEighteenDL_79
      · exact prime_oneHundredEighteenDL_12575621651
      · exact prime_oneHundredEighteenDL_4528634000201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2447499865335667481514748577) ^ 1223749932667833740757374288 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 2447499865335667481514748577) ^ 143970580313862793030279328 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 2447499865335667481514748577) ^ 30981010953616044069806944 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 2447499865335667481514748577) ^ 194622574792638176 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 2447499865335667481514748577) ^ 540449916073376 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_2583472080076537897154456831 : Nat.Prime 2583472080076537897154456831 := by
  apply lucas_primality 2583472080076537897154456831 (14 : ZMod 2583472080076537897154456831)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (47, 1), (367174909, 1), (14970383247363521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (47, 1), (367174909, 1), (14970383247363521, 1)] : List FactorBlock).map factorBlockValue).prod) = 2583472080076537897154456831 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_5
      · exact prime_oneHundredEighteenDL_47
      · exact prime_oneHundredEighteenDL_367174909
      · exact prime_oneHundredEighteenDL_14970383247363521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 2583472080076537897154456831) ^ 1291736040038268948577228415 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (14 : ZMod 2583472080076537897154456831) ^ 516694416015307579430891366 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (14 : ZMod 2583472080076537897154456831) ^ 54967491065458253130945890 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (14 : ZMod 2583472080076537897154456831) ^ 7036080126260854870 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (14 : ZMod 2583472080076537897154456831) ^ 172572207230 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_3402621764003245035276601679 : Nat.Prime 3402621764003245035276601679 := by
  apply lucas_primality 3402621764003245035276601679 (7 : ZMod 3402621764003245035276601679)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (1481, 1), (67574011280201077079807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (1481, 1), (67574011280201077079807, 1)] : List FactorBlock).map factorBlockValue).prod) = 3402621764003245035276601679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_17
      · exact prime_oneHundredEighteenDL_1481
      · exact prime_oneHundredEighteenDL_67574011280201077079807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 3402621764003245035276601679) ^ 1701310882001622517638300839 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (7 : ZMod 3402621764003245035276601679) ^ 200154221411955590310388334 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (7 : ZMod 3402621764003245035276601679) ^ 2297516383526836620713438 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (7 : ZMod 3402621764003245035276601679) ^ 50354 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_5580299692965321857853626753 : Nat.Prime 5580299692965321857853626753 := by
  apply lucas_primality 5580299692965321857853626753 (3 : ZMod 5580299692965321857853626753)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (59, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (59, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 5580299692965321857853626753 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_59
      · exact prime_oneHundredEighteenDL_171401
      · exact prime_oneHundredEighteenDL_714027719
      · exact prime_oneHundredEighteenDL_6037638679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 5580299692965321857853626753) ^ 2790149846482660928926813376 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 5580299692965321857853626753) ^ 94581350728225794200908928 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 5580299692965321857853626753) ^ 32556984457297926253952 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 5580299692965321857853626753) ^ 7815242384119995008 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 5580299692965321857853626753) ^ 924252011365737088 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_8719218270258315402896291801 : Nat.Prime 8719218270258315402896291801 := by
  apply lucas_primality 8719218270258315402896291801 (3 : ZMod 8719218270258315402896291801)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (59, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (59, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 8719218270258315402896291801 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_5
      · exact prime_oneHundredEighteenDL_59
      · exact prime_oneHundredEighteenDL_171401
      · exact prime_oneHundredEighteenDL_714027719
      · exact prime_oneHundredEighteenDL_6037638679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 8719218270258315402896291801) ^ 4359609135129157701448145900 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 8719218270258315402896291801) ^ 1743843654051663080579258360 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 8719218270258315402896291801) ^ 147783360512852803438920200 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 8719218270258315402896291801) ^ 50870288214528009771800 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 8719218270258315402896291801) ^ 12211316225187492200 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (3 : ZMod 8719218270258315402896291801) ^ 1444143767758964200 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_11625624360344420537195055739 : Nat.Prime 11625624360344420537195055739 := by
  apply lucas_primality 11625624360344420537195055739 (2 : ZMod 11625624360344420537195055739)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (97, 1), (41701007, 1), (36847107955599349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (97, 1), (41701007, 1), (36847107955599349, 1)] : List FactorBlock).map factorBlockValue).prod) = 11625624360344420537195055739 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_13
      · exact prime_oneHundredEighteenDL_97
      · exact prime_oneHundredEighteenDL_41701007
      · exact prime_oneHundredEighteenDL_36847107955599349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 11625624360344420537195055739) ^ 5812812180172210268597527869 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 11625624360344420537195055739) ^ 3875208120114806845731685246 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 11625624360344420537195055739) ^ 894278796949570810553465826 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 11625624360344420537195055739) ^ 119851797529323923063866554 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 11625624360344420537195055739) ^ 278785218792064674534 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 11625624360344420537195055739) ^ 315509818962 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_23251248720688841074390111477 : Nat.Prime 23251248720688841074390111477 := by
  apply lucas_primality 23251248720688841074390111477 (2 : ZMod 23251248720688841074390111477)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (97, 1), (41701007, 1), (36847107955599349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (97, 1), (41701007, 1), (36847107955599349, 1)] : List FactorBlock).map factorBlockValue).prod) = 23251248720688841074390111477 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_13
      · exact prime_oneHundredEighteenDL_97
      · exact prime_oneHundredEighteenDL_41701007
      · exact prime_oneHundredEighteenDL_36847107955599349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 23251248720688841074390111477) ^ 11625624360344420537195055738 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 23251248720688841074390111477) ^ 7750416240229613691463370492 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 23251248720688841074390111477) ^ 1788557593899141621106931652 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 23251248720688841074390111477) ^ 239703595058647846127733108 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 23251248720688841074390111477) ^ 557570437584129349068 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 23251248720688841074390111477) ^ 631019637924 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_34876873081033261611585167207 : Nat.Prime 34876873081033261611585167207 := by
  apply lucas_primality 34876873081033261611585167207 (5 : ZMod 34876873081033261611585167207)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11489, 1), (1517837630822232640420627, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11489, 1), (1517837630822232640420627, 1)] : List FactorBlock).map factorBlockValue).prod) = 34876873081033261611585167207 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_11489
      · exact prime_oneHundredEighteenDL_1517837630822232640420627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 34876873081033261611585167207) ^ 17438436540516630805792583603 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 34876873081033261611585167207) ^ 3035675261644465280841254 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (5 : ZMod 34876873081033261611585167207) ^ 22978 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_34876873081033261611585167219 : Nat.Prime 34876873081033261611585167219 := by
  apply lucas_primality 34876873081033261611585167219 (2 : ZMod 34876873081033261611585167219)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5653, 1), (3084810992484809978028053, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5653, 1), (3084810992484809978028053, 1)] : List FactorBlock).map factorBlockValue).prod) = 34876873081033261611585167219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_5653
      · exact prime_oneHundredEighteenDL_3084810992484809978028053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 34876873081033261611585167219) ^ 17438436540516630805792583609 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 34876873081033261611585167219) ^ 6169621984969619956056106 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 34876873081033261611585167219) ^ 11306 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_139507492324133046446340668821 : Nat.Prime 139507492324133046446340668821 := by
  apply lucas_primality 139507492324133046446340668821 (2 : ZMod 139507492324133046446340668821)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 1), (47, 1), (367174909, 1), (14970383247363521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 1), (47, 1), (367174909, 1), (14970383247363521, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668821 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_3
      · exact prime_oneHundredEighteenDL_5
      · exact prime_oneHundredEighteenDL_47
      · exact prime_oneHundredEighteenDL_367174909
      · exact prime_oneHundredEighteenDL_14970383247363521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 139507492324133046446340668821) ^ 69753746162066523223170334410 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 139507492324133046446340668821) ^ 46502497441377682148780222940 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 139507492324133046446340668821) ^ 27901498464826609289268133764 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 139507492324133046446340668821) ^ 2968244517534745669071078060 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 139507492324133046446340668821) ^ 379948326818086162980 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 139507492324133046446340668821) ^ 9318899190420 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_139507492324133046446340668861 : Nat.Prime 139507492324133046446340668861 := by
  apply lucas_primality 139507492324133046446340668861 (2 : ZMod 139507492324133046446340668861)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (23, 2), (173, 1), (659, 1), (5983283, 1), (19330398271207, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (23, 2), (173, 1), (659, 1), (5983283, 1), (19330398271207, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668861 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_5
      · exact prime_oneHundredEighteenDL_23
      · exact prime_oneHundredEighteenDL_173
      · exact prime_oneHundredEighteenDL_659
      · exact prime_oneHundredEighteenDL_5983283
      · exact prime_oneHundredEighteenDL_19330398271207
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 139507492324133046446340668861) ^ 69753746162066523223170334430 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 139507492324133046446340668861) ^ 27901498464826609289268133772 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 139507492324133046446340668861) ^ 6065543144527523758536550820 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 139507492324133046446340668861) ^ 806401689734873100845899820 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 139507492324133046446340668861) ^ 211695739490338461982307540 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 139507492324133046446340668861) ^ 23316211572164152430420 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (2 : ZMod 139507492324133046446340668861) ^ 7217000413898980 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem prime_oneHundredEighteenDL_139507492324133046446340668879 : Nat.Prime 139507492324133046446340668879 := by
  apply lucas_primality 139507492324133046446340668879 (7 : ZMod 139507492324133046446340668879)
  · rw [← oneHundredEighteenDLFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (73, 1), (136504395620482432922055449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (73, 1), (136504395620482432922055449, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668879 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredEighteenDL_2
      · exact prime_oneHundredEighteenDL_7
      · exact prime_oneHundredEighteenDL_73
      · exact prime_oneHundredEighteenDL_136504395620482432922055449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 139507492324133046446340668879) ^ 69753746162066523223170334439 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (7 : ZMod 139507492324133046446340668879) ^ 19929641760590435206620095554 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (7 : ZMod 139507492324133046446340668879) ^ 1911061538686754060908776286 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide
    · change (7 : ZMod 139507492324133046446340668879) ^ 1022 ≠ 1
      rw [← oneHundredEighteenDLFastPow_eq_pow]
      decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668800 : Nat.totient 139507492324133046446340668800 = 54856863284746174059423744000 := by
  rw [← show ((([(2, 7), (5, 2), (59, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668800 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_2, prime_oneHundredEighteenDL_5, prime_oneHundredEighteenDL_59, prime_oneHundredEighteenDL_171401, prime_oneHundredEighteenDL_714027719, prime_oneHundredEighteenDL_6037638679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668801 : Nat.totient 139507492324133046446340668801 = 119577429736840112034383705088 := by
  rw [← show ((([(7, 3), (291007, 1), (12058873, 1), (115902620448737, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668801 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_7, prime_oneHundredEighteenDL_291007, prime_oneHundredEighteenDL_12058873, prime_oneHundredEighteenDL_115902620448737]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668802 : Nat.totient 139507492324133046446340668802 = 46279136109214772109037486080 := by
  rw [← show ((([(2, 1), (3, 2), (241, 1), (2237, 1), (4909, 1), (241663, 1), (577097, 1), (20998583, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668802 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_2, prime_oneHundredEighteenDL_3, prime_oneHundredEighteenDL_241, prime_oneHundredEighteenDL_2237, prime_oneHundredEighteenDL_4909, prime_oneHundredEighteenDL_241663, prime_oneHundredEighteenDL_577097, prime_oneHundredEighteenDL_20998583]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668803 : Nat.totient 139507492324133046446340668803 = 139507492324120214196787247880 := by
  rw [← show ((([(10880858014333, 1), (12821368695406591, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668803 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_10880858014333, prime_oneHundredEighteenDL_12821368695406591]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668804 : Nat.totient 139507492324133046446340668804 = 57862654306547464956170649600 := by
  rw [← show ((([(2, 2), (11, 1), (13, 1), (107, 1), (467, 1), (78721, 1), (62002648740676543, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668804 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_2, prime_oneHundredEighteenDL_11, prime_oneHundredEighteenDL_13, prime_oneHundredEighteenDL_107, prime_oneHundredEighteenDL_467, prime_oneHundredEighteenDL_78721, prime_oneHundredEighteenDL_62002648740676543]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668805 : Nat.totient 139507492324133046446340668805 = 72979322405540574966858800640 := by
  rw [← show ((([(3, 1), (5, 1), (73, 1), (181, 1), (703890069497883632010599, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668805 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_3, prime_oneHundredEighteenDL_5, prime_oneHundredEighteenDL_73, prime_oneHundredEighteenDL_181, prime_oneHundredEighteenDL_703890069497883632010599]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668806 : Nat.totient 139507492324133046446340668806 = 67880158026073489517785245000 := by
  rw [← show ((([(2, 1), (43, 1), (271, 1), (5985904587837168387811751, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668806 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_2, prime_oneHundredEighteenDL_43, prime_oneHundredEighteenDL_271, prime_oneHundredEighteenDL_5985904587837168387811751]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668807 : Nat.totient 139507492324133046446340668807 = 139444182160853215969019473920 := by
  rw [← show ((([(2393, 1), (47777, 1), (66617, 1), (18316854115477111, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668807 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_2393, prime_oneHundredEighteenDL_47777, prime_oneHundredEighteenDL_66617, prime_oneHundredEighteenDL_18316854115477111]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668808 : Nat.totient 139507492324133046446340668808 = 39859283520959363942101479936 := by
  rw [← show ((([(2, 3), (3, 1), (7, 1), (179953378837, 1), (4614538195344313, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668808 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_2, prime_oneHundredEighteenDL_3, prime_oneHundredEighteenDL_7, prime_oneHundredEighteenDL_179953378837, prime_oneHundredEighteenDL_4614538195344313]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668809 : Nat.totient 139507492324133046446340668809 = 139507477705347719048390026960 := by
  rw [← show ((([(9543029, 1), (14618785327397941098821, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668809 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_9543029, prime_oneHundredEighteenDL_14618785327397941098821]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668810 : Nat.totient 139507492324133046446340668810 = 55793377381275222007355164800 := by
  rw [← show ((([(2, 1), (5, 1), (5801, 1), (101222580439, 1), (23758403961679, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668810 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_2, prime_oneHundredEighteenDL_5, prime_oneHundredEighteenDL_5801, prime_oneHundredEighteenDL_101222580439, prime_oneHundredEighteenDL_23758403961679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668811 : Nat.totient 139507492324133046446340668811 = 89797917786793905772650732480 := by
  rw [← show ((([(3, 2), (29, 1), (10934939, 1), (964425391, 1), (50684133299, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668811 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_3, prime_oneHundredEighteenDL_29, prime_oneHundredEighteenDL_10934939, prime_oneHundredEighteenDL_964425391, prime_oneHundredEighteenDL_50684133299]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668812 : Nat.totient 139507492324133046446340668812 = 69752789908786240825918614720 := by
  rw [← show ((([(2, 2), (77621, 1), (1210819, 1), (371089853800687997, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668812 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_2, prime_oneHundredEighteenDL_77621, prime_oneHundredEighteenDL_1210819, prime_oneHundredEighteenDL_371089853800687997]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668813 : Nat.totient 139507492324133046446340668813 = 131377708357797817896559488000 := by
  rw [← show ((([(19, 1), (251, 1), (509, 1), (62297, 1), (922540188552849049, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668813 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_19, prime_oneHundredEighteenDL_251, prime_oneHundredEighteenDL_509, prime_oneHundredEighteenDL_62297, prime_oneHundredEighteenDL_922540188552849049]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668814 : Nat.totient 139507492324133046446340668814 = 43749796146588009439618800000 := by
  rw [← show ((([(2, 1), (3, 1), (23, 1), (131, 1), (151, 1), (443, 1), (4107295811, 1), (28087332431, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668814 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_2, prime_oneHundredEighteenDL_3, prime_oneHundredEighteenDL_23, prime_oneHundredEighteenDL_131, prime_oneHundredEighteenDL_151, prime_oneHundredEighteenDL_443, prime_oneHundredEighteenDL_4107295811, prime_oneHundredEighteenDL_28087332431]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668815 : Nat.totient 139507492324133046446340668815 = 79170129694455580995954739200 := by
  rw [← show ((([(5, 1), (7, 1), (11, 1), (17, 1), (31, 1), (1999, 1), (343964318895525651503, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668815 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_5, prime_oneHundredEighteenDL_7, prime_oneHundredEighteenDL_11, prime_oneHundredEighteenDL_17, prime_oneHundredEighteenDL_31, prime_oneHundredEighteenDL_1999, prime_oneHundredEighteenDL_343964318895525651503]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668816 : Nat.totient 139507492324133046446340668816 = 69753746162066523223170334400 := by
  rw [← show ((([(2, 4), (8719218270258315402896291801, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668816 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_2, prime_oneHundredEighteenDL_8719218270258315402896291801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668817 : Nat.totient 139507492324133046446340668817 = 85169040667678104841455427584 := by
  rw [← show ((([(3, 1), (13, 1), (137, 1), (1553, 1), (428339, 1), (39251231201603557, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668817 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_3, prime_oneHundredEighteenDL_13, prime_oneHundredEighteenDL_137, prime_oneHundredEighteenDL_1553, prime_oneHundredEighteenDL_428339, prime_oneHundredEighteenDL_39251231201603557]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668818 : Nat.totient 139507492324133046446340668818 = 69392327788162178796502920960 := by
  rw [← show ((([(2, 1), (193, 1), (14112454044391, 1), (25609888454543, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668818 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_2, prime_oneHundredEighteenDL_193, prime_oneHundredEighteenDL_14112454044391, prime_oneHundredEighteenDL_25609888454543]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668819 : Nat.totient 139507492324133046446340668819 = 138651511474214375331612329280 := by
  rw [← show ((([(163, 1), (1300031, 1), (18805667849, 1), (35008012727, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668819 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_163, prime_oneHundredEighteenDL_1300031, prime_oneHundredEighteenDL_18805667849, prime_oneHundredEighteenDL_35008012727]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668820 : Nat.totient 139507492324133046446340668820 = 36410465982595725811236003840 := by
  rw [← show ((([(2, 2), (3, 3), (5, 1), (47, 1), (367174909, 1), (14970383247363521, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668820 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_2, prime_oneHundredEighteenDL_3, prime_oneHundredEighteenDL_5, prime_oneHundredEighteenDL_47, prime_oneHundredEighteenDL_367174909, prime_oneHundredEighteenDL_14970383247363521]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668821 : Nat.totient 139507492324133046446340668821 = 139507492324133046446340668820 := by
  rw [← show ((([(139507492324133046446340668821, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668821 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_139507492324133046446340668821]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668822 : Nat.totient 139507492324133046446340668822 = 58946155148397585109369809600 := by
  rw [← show ((([(2, 1), (7, 1), (71, 1), (87641, 1), (1601414747245158361843, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668822 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_2, prime_oneHundredEighteenDL_7, prime_oneHundredEighteenDL_71, prime_oneHundredEighteenDL_87641, prime_oneHundredEighteenDL_1601414747245158361843]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668823 : Nat.totient 139507492324133046446340668823 = 93004993218256309946019398904 := by
  rw [← show ((([(3, 1), (55875667, 1), (832249527175714647823, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668823 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_3, prime_oneHundredEighteenDL_55875667, prime_oneHundredEighteenDL_832249527175714647823]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668824 : Nat.totient 139507492324133046446340668824 = 69747674811543234292608605952 := by
  rw [← show ((([(2, 3), (11489, 1), (1517837630822232640420627, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668824 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_2, prime_oneHundredEighteenDL_11489, prime_oneHundredEighteenDL_1517837630822232640420627]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668825 : Nat.totient 139507492324133046446340668825 = 111605993859306437157072535040 := by
  rw [← show ((([(5, 2), (5580299692965321857853626753, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668825 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_5, prime_oneHundredEighteenDL_5580299692965321857853626753]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668826 : Nat.totient 139507492324133046446340668826 = 42274996675283351252840208000 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (42330181, 1), (49934817989532942281, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668826 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_2, prime_oneHundredEighteenDL_3, prime_oneHundredEighteenDL_11, prime_oneHundredEighteenDL_42330181, prime_oneHundredEighteenDL_49934817989532942281]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668827 : Nat.totient 139507492324133046446340668827 = 135217824155100065996491530240 := by
  rw [← show ((([(37, 1), (277, 1), (4729, 1), (238213, 1), (59649929, 1), (202568231, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668827 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_37, prime_oneHundredEighteenDL_277, prime_oneHundredEighteenDL_4729, prime_oneHundredEighteenDL_238213, prime_oneHundredEighteenDL_59649929, prime_oneHundredEighteenDL_202568231]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668828 : Nat.totient 139507492324133046446340668828 = 69753746162066523223170334412 := by
  rw [← show ((([(2, 2), (34876873081033261611585167207, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668828 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_2, prime_oneHundredEighteenDL_34876873081033261611585167207]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668829 : Nat.totient 139507492324133046446340668829 = 79718304037120291330643560320 := by
  rw [← show ((([(3, 2), (7, 1), (326141, 1), (4291589, 1), (1582098289002067, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668829 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_3, prime_oneHundredEighteenDL_7, prime_oneHundredEighteenDL_326141, prime_oneHundredEighteenDL_4291589, prime_oneHundredEighteenDL_1582098289002067]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668830 : Nat.totient 139507492324133046446340668830 = 51104864535999796093501085184 := by
  rw [← show ((([(2, 1), (5, 1), (13, 1), (127, 1), (9698280469, 1), (871275936325357, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668830 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_2, prime_oneHundredEighteenDL_5, prime_oneHundredEighteenDL_13, prime_oneHundredEighteenDL_127, prime_oneHundredEighteenDL_9698280469, prime_oneHundredEighteenDL_871275936325357]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668831 : Nat.totient 139507492324133046446340668831 = 139504316863947670236055728792 := by
  rw [← show ((([(43933, 1), (3175460185376210284896107, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668831 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_43933, prime_oneHundredEighteenDL_3175460185376210284896107]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668832 : Nat.totient 139507492324133046446340668832 = 40938672353325608427171840000 := by
  rw [← show ((([(2, 5), (3, 1), (17, 1), (19, 1), (79, 1), (12575621651, 1), (4528634000201, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668832 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_2, prime_oneHundredEighteenDL_3, prime_oneHundredEighteenDL_17, prime_oneHundredEighteenDL_19, prime_oneHundredEighteenDL_79, prime_oneHundredEighteenDL_12575621651, prime_oneHundredEighteenDL_4528634000201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668833 : Nat.totient 139507492324133046446340668833 = 139507487552548151245348250880 := by
  rw [← show ((([(29281061, 1), (21357468337, 1), (223080162269, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668833 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_29281061, prime_oneHundredEighteenDL_21357468337, prime_oneHundredEighteenDL_223080162269]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668834 : Nat.totient 139507492324133046446340668834 = 69739537260636392758728249264 := by
  rw [← show ((([(2, 1), (5749, 1), (33599, 1), (361117783570042550867, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668834 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_2, prime_oneHundredEighteenDL_5749, prime_oneHundredEighteenDL_33599, prime_oneHundredEighteenDL_361117783570042550867]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668835 : Nat.totient 139507492324133046446340668835 = 72976298463291850940450142720 := by
  rw [← show ((([(3, 1), (5, 1), (53, 1), (3061, 1), (57328037380036961837333, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668835 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_3, prime_oneHundredEighteenDL_5, prime_oneHundredEighteenDL_53, prime_oneHundredEighteenDL_3061, prime_oneHundredEighteenDL_57328037380036961837333]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668836 : Nat.totient 139507492324133046446340668836 = 59788754675071845856507878048 := by
  rw [← show ((([(2, 2), (7, 1), (359407, 1), (14060239, 1), (985962202947919, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668836 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_2, prime_oneHundredEighteenDL_7, prime_oneHundredEighteenDL_359407, prime_oneHundredEighteenDL_14060239, prime_oneHundredEighteenDL_985962202947919]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668837 : Nat.totient 139507492324133046446340668837 = 118617612631066152635138173440 := by
  rw [← show ((([(11, 1), (23, 1), (89, 1), (103, 1), (727, 1), (52103, 1), (1588007828000327, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668837 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_11, prime_oneHundredEighteenDL_23, prime_oneHundredEighteenDL_89, prime_oneHundredEighteenDL_103, prime_oneHundredEighteenDL_727, prime_oneHundredEighteenDL_52103, prime_oneHundredEighteenDL_1588007828000327]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668838 : Nat.totient 139507492324133046446340668838 = 45864167404124224381263206400 := by
  rw [← show ((([(2, 1), (3, 2), (101, 1), (353, 1), (967, 1), (1925936203, 1), (116724111547, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668838 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_2, prime_oneHundredEighteenDL_3, prime_oneHundredEighteenDL_101, prime_oneHundredEighteenDL_353, prime_oneHundredEighteenDL_967, prime_oneHundredEighteenDL_1925936203, prime_oneHundredEighteenDL_116724111547]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668839 : Nat.totient 139507492324133046446340668839 = 136104870560129801411064067120 := by
  rw [← show ((([(41, 1), (3402621764003245035276601679, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668839 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_41, prime_oneHundredEighteenDL_3402621764003245035276601679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668840 : Nat.totient 139507492324133046446340668840 = 53875233938741495970666323200 := by
  rw [← show ((([(2, 3), (5, 1), (29, 1), (15299, 1), (7860976507599834474551, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668840 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_2, prime_oneHundredEighteenDL_5, prime_oneHundredEighteenDL_29, prime_oneHundredEighteenDL_15299, prime_oneHundredEighteenDL_7860976507599834474551]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668841 : Nat.totient 139507492324133046446340668841 = 92181938912177977214596640256 := by
  rw [← show ((([(3, 1), (113, 1), (31585193, 1), (13029096451298904283, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668841 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_3, prime_oneHundredEighteenDL_113, prime_oneHundredEighteenDL_31585193, prime_oneHundredEighteenDL_13029096451298904283]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668842 : Nat.totient 139507492324133046446340668842 = 68610242126612308605118654320 := by
  rw [← show ((([(2, 1), (61, 1), (6797626137803, 1), (168221083693387, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668842 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_2, prime_oneHundredEighteenDL_61, prime_oneHundredEighteenDL_6797626137803, prime_oneHundredEighteenDL_168221083693387]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668843 : Nat.totient 139507492324133046446340668843 = 110375378225501849909686298880 := by
  rw [← show ((([(7, 1), (13, 1), (26431, 1), (221403932777, 1), (261973410679, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668843 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_7, prime_oneHundredEighteenDL_13, prime_oneHundredEighteenDL_26431, prime_oneHundredEighteenDL_221403932777, prime_oneHundredEighteenDL_261973410679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668844 : Nat.totient 139507492324133046446340668844 = 46206303157106166291482304000 := by
  rw [← show ((([(2, 2), (3, 1), (157, 1), (1397964901, 1), (52968828295884041, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668844 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_2, prime_oneHundredEighteenDL_3, prime_oneHundredEighteenDL_157, prime_oneHundredEighteenDL_1397964901, prime_oneHundredEighteenDL_52968828295884041]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668845 : Nat.totient 139507492324133046446340668845 = 111605811183025916414722344000 := by
  rw [← show ((([(5, 1), (956051, 1), (1692541, 1), (17242779322502959, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668845 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_5, prime_oneHundredEighteenDL_956051, prime_oneHundredEighteenDL_1692541, prime_oneHundredEighteenDL_17242779322502959]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668846 : Nat.totient 139507492324133046446340668846 = 67501065550758747110828494200 := by
  rw [← show ((([(2, 1), (31, 1), (26371, 1), (85325579004877698281923, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668846 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_2, prime_oneHundredEighteenDL_31, prime_oneHundredEighteenDL_26371, prime_oneHundredEighteenDL_85325579004877698281923]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668847 : Nat.totient 139507492324133046446340668847 = 93000505420065503805142647168 := by
  rw [← show ((([(3, 4), (21577, 1), (519307, 1), (153708284343135733, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668847 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_3, prime_oneHundredEighteenDL_21577, prime_oneHundredEighteenDL_519307, prime_oneHundredEighteenDL_153708284343135733]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668848 : Nat.totient 139507492324133046446340668848 = 63412496510969566566518485760 := by
  rw [← show ((([(2, 4), (11, 1), (792656206387119582081481073, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668848 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_2, prime_oneHundredEighteenDL_11, prime_oneHundredEighteenDL_792656206387119582081481073]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668849 : Nat.totient 139507492324133046446340668849 = 128158070402022775524171804672 := by
  rw [← show ((([(17, 1), (43, 1), (2089, 1), (4547, 1), (20091703527913509113, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668849 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_17, prime_oneHundredEighteenDL_43, prime_oneHundredEighteenDL_2089, prime_oneHundredEighteenDL_4547, prime_oneHundredEighteenDL_20091703527913509113]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668850 : Nat.totient 139507492324133046446340668850 = 31257433040884113465003571200 := by
  rw [← show ((([(2, 1), (3, 1), (5, 2), (7, 2), (83, 1), (229, 1), (311, 1), (4243, 1), (1920227, 1), (394103803, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668850 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_2, prime_oneHundredEighteenDL_3, prime_oneHundredEighteenDL_5, prime_oneHundredEighteenDL_7, prime_oneHundredEighteenDL_83, prime_oneHundredEighteenDL_229, prime_oneHundredEighteenDL_311, prime_oneHundredEighteenDL_4243, prime_oneHundredEighteenDL_1920227, prime_oneHundredEighteenDL_394103803]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668851 : Nat.totient 139507492324133046446340668851 = 132024537342253634331066451200 := by
  rw [← show ((([(19, 1), (941, 1), (35240221, 1), (221419407632785289, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668851 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_19, prime_oneHundredEighteenDL_941, prime_oneHundredEighteenDL_35240221, prime_oneHundredEighteenDL_221419407632785289]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668852 : Nat.totient 139507492324133046446340668852 = 69747956989009666511142493056 := by
  rw [← show ((([(2, 2), (12049, 1), (2894586528428356013908637, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668852 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_2, prime_oneHundredEighteenDL_12049, prime_oneHundredEighteenDL_2894586528428356013908637]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668853 : Nat.totient 139507492324133046446340668853 = 92151737836732401743864442240 := by
  rw [← show ((([(3, 1), (109, 1), (434194219, 1), (982575074066965481, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668853 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_3, prime_oneHundredEighteenDL_109, prime_oneHundredEighteenDL_434194219, prime_oneHundredEighteenDL_982575074066965481]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668854 : Nat.totient 139507492324133046446340668854 = 68712645408304005020550825000 := by
  rw [← show ((([(2, 1), (67, 1), (1060765831, 1), (981461373057808751, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668854 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_2, prime_oneHundredEighteenDL_67, prime_oneHundredEighteenDL_1060765831, prime_oneHundredEighteenDL_981461373057808751]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668855 : Nat.totient 139507492324133046446340668855 = 111583897898783486032789094400 := by
  rw [← show ((([(5, 1), (5051, 1), (802015873, 1), (6887588555758577, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668855 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_5, prime_oneHundredEighteenDL_5051, prime_oneHundredEighteenDL_802015873, prime_oneHundredEighteenDL_6887588555758577]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668856 : Nat.totient 139507492324133046446340668856 = 42482851520876130204354945024 := by
  rw [← show ((([(2, 3), (3, 2), (13, 1), (97, 1), (41701007, 1), (36847107955599349, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668856 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_2, prime_oneHundredEighteenDL_3, prime_oneHundredEighteenDL_13, prime_oneHundredEighteenDL_97, prime_oneHundredEighteenDL_41701007, prime_oneHundredEighteenDL_36847107955599349]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668857 : Nat.totient 139507492324133046446340668857 = 119577850563488172028316480112 := by
  rw [← show ((([(7, 1), (2197071011957, 1), (9071004829670243, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668857 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_7, prime_oneHundredEighteenDL_2197071011957, prime_oneHundredEighteenDL_9071004829670243]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668858 : Nat.totient 139507492324133046446340668858 = 69753746161935173258217061884 := by
  rw [← show ((([(2, 1), (531054790963, 1), (131349433898481583, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668858 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_2, prime_oneHundredEighteenDL_531054790963, prime_oneHundredEighteenDL_131349433898481583]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668859 : Nat.totient 139507492324133046446340668859 = 82935462659494891722324864000 := by
  rw [← show ((([(3, 1), (11, 1), (59, 1), (461, 1), (69997, 1), (2220502305087140441, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668859 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_3, prime_oneHundredEighteenDL_11, prime_oneHundredEighteenDL_59, prime_oneHundredEighteenDL_461, prime_oneHundredEighteenDL_69997, prime_oneHundredEighteenDL_2220502305087140441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668860 : Nat.totient 139507492324133046446340668860 = 52987706075053894495370697216 := by
  rw [← show ((([(2, 2), (5, 1), (23, 2), (173, 1), (659, 1), (5983283, 1), (19330398271207, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668860 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_2, prime_oneHundredEighteenDL_5, prime_oneHundredEighteenDL_23, prime_oneHundredEighteenDL_173, prime_oneHundredEighteenDL_659, prime_oneHundredEighteenDL_5983283, prime_oneHundredEighteenDL_19330398271207]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668861 : Nat.totient 139507492324133046446340668861 = 139507492324133046446340668860 := by
  rw [← show ((([(139507492324133046446340668861, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668861 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_139507492324133046446340668861]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668862 : Nat.totient 139507492324133046446340668862 = 46502497441377682148780222952 := by
  rw [← show ((([(2, 1), (3, 1), (23251248720688841074390111477, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668862 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_2, prime_oneHundredEighteenDL_3, prime_oneHundredEighteenDL_23251248720688841074390111477]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668863 : Nat.totient 139507492324133046446340668863 = 138878438154412048600560297984 := by
  rw [← show ((([(233, 1), (4583, 1), (130644687377154277420417, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668863 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_233, prime_oneHundredEighteenDL_4583, prime_oneHundredEighteenDL_130644687377154277420417]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668864 : Nat.totient 139507492324133046446340668864 = 58173008382206154133238412288 := by
  rw [← show ((([(2, 6), (7, 1), (37, 1), (1169681357543, 1), (7195321868923, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668864 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_2, prime_oneHundredEighteenDL_7, prime_oneHundredEighteenDL_37, prime_oneHundredEighteenDL_1169681357543, prime_oneHundredEighteenDL_7195321868923]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668865 : Nat.totient 139507492324133046446340668865 = 74403995897205628858939340544 := by
  rw [← show ((([(3, 2), (5, 1), (8268339533, 1), (374944265861202809, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668865 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_3, prime_oneHundredEighteenDL_5, prime_oneHundredEighteenDL_8268339533, prime_oneHundredEighteenDL_374944265861202809]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668866 : Nat.totient 139507492324133046446340668866 = 65606043729080107850470871040 := by
  rw [← show ((([(2, 1), (17, 1), (1493, 1), (117709, 1), (5820797, 1), (4011129502741, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668866 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_2, prime_oneHundredEighteenDL_17, prime_oneHundredEighteenDL_1493, prime_oneHundredEighteenDL_117709, prime_oneHundredEighteenDL_5820797, prime_oneHundredEighteenDL_4011129502741]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668867 : Nat.totient 139507492324133046446340668867 = 135600684499073559789320839200 := by
  rw [← show ((([(47, 1), (167, 1), (1319, 1), (7507, 1), (1795031159361207151, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668867 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_47, prime_oneHundredEighteenDL_167, prime_oneHundredEighteenDL_1319, prime_oneHundredEighteenDL_7507, prime_oneHundredEighteenDL_1795031159361207151]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668868 : Nat.totient 139507492324133046446340668868 = 46502497441377682148780222952 := by
  rw [← show ((([(2, 2), (3, 1), (11625624360344420537195055739, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668868 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_2, prime_oneHundredEighteenDL_3, prime_oneHundredEighteenDL_11625624360344420537195055739]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668869 : Nat.totient 139507492324133046446340668869 = 124335571398256710159087220416 := by
  rw [← show ((([(13, 1), (29, 1), (6692759, 1), (55290560849083829083, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668869 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_13, prime_oneHundredEighteenDL_29, prime_oneHundredEighteenDL_6692759, prime_oneHundredEighteenDL_55290560849083829083]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668870 : Nat.totient 139507492324133046446340668870 = 47979673501658262345575193600 := by
  rw [← show ((([(2, 1), (5, 1), (11, 1), (19, 1), (617, 1), (19739, 1), (5480761894697962861, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668870 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_2, prime_oneHundredEighteenDL_5, prime_oneHundredEighteenDL_11, prime_oneHundredEighteenDL_19, prime_oneHundredEighteenDL_617, prime_oneHundredEighteenDL_19739, prime_oneHundredEighteenDL_5480761894697962861]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668871 : Nat.totient 139507492324133046446340668871 = 79636970958355247095852548096 := by
  rw [← show ((([(3, 1), (7, 1), (977, 1), (96409217, 1), (70528576446348539, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668871 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_3, prime_oneHundredEighteenDL_7, prime_oneHundredEighteenDL_977, prime_oneHundredEighteenDL_96409217, prime_oneHundredEighteenDL_70528576446348539]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668872 : Nat.totient 139507492324133046446340668872 = 69741406918096583983258199616 := by
  rw [← show ((([(2, 3), (5653, 1), (3084810992484809978028053, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668872 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_2, prime_oneHundredEighteenDL_5653, prime_oneHundredEighteenDL_3084810992484809978028053]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668873 : Nat.totient 139507492324133046446340668873 = 139330226736521958690013675824 := by
  rw [← show ((([(787, 1), (208812613, 1), (848918644397372183, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668873 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_787, prime_oneHundredEighteenDL_208812613, prime_oneHundredEighteenDL_848918644397372183]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668874 : Nat.totient 139507492324133046446340668874 = 46502497441377682148780222940 := by
  rw [← show ((([(2, 1), (3, 3), (2583472080076537897154456831, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668874 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_2, prime_oneHundredEighteenDL_3, prime_oneHundredEighteenDL_2583472080076537897154456831]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668875 : Nat.totient 139507492324133046446340668875 = 111605993859306437157072535000 := by
  rw [← show ((([(5, 3), (1116059938593064371570725351, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668875 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_5, prime_oneHundredEighteenDL_1116059938593064371570725351]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668876 : Nat.totient 139507492324133046446340668876 = 69753746162066523223170334436 := by
  rw [← show ((([(2, 2), (34876873081033261611585167219, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668876 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_2, prime_oneHundredEighteenDL_34876873081033261611585167219]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668877 : Nat.totient 139507492324133046446340668877 = 90004658285900415323481730560 := by
  rw [← show ((([(3, 1), (31, 1), (514313, 1), (190896269, 1), (15278813913037, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668877 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_3, prime_oneHundredEighteenDL_31, prime_oneHundredEighteenDL_514313, prime_oneHundredEighteenDL_190896269, prime_oneHundredEighteenDL_15278813913037]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668878 : Nat.totient 139507492324133046446340668878 = 58969898908048411022327953536 := by
  rw [← show ((([(2, 1), (7, 1), (73, 1), (136504395620482432922055449, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668878 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_2, prime_oneHundredEighteenDL_7, prime_oneHundredEighteenDL_73, prime_oneHundredEighteenDL_136504395620482432922055449]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668879 : Nat.totient 139507492324133046446340668879 = 139507492324133046446340668878 := by
  rw [← show ((([(139507492324133046446340668879, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668879 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_139507492324133046446340668879]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668880 : Nat.totient 139507492324133046446340668880 = 36259496977877755419479285760 := by
  rw [← show ((([(2, 4), (3, 1), (5, 1), (41, 1), (1033, 1), (13724676363356102917379, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668880 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_2, prime_oneHundredEighteenDL_3, prime_oneHundredEighteenDL_5, prime_oneHundredEighteenDL_41, prime_oneHundredEighteenDL_1033, prime_oneHundredEighteenDL_13724676363356102917379]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668881 : Nat.totient 139507492324133046446340668881 = 126813592042219782432642240000 := by
  rw [← show ((([(11, 1), (16417, 1), (34501, 1), (22391302942731690263, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668881 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_11, prime_oneHundredEighteenDL_16417, prime_oneHundredEighteenDL_34501, prime_oneHundredEighteenDL_22391302942731690263]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668882 : Nat.totient 139507492324133046446340668882 = 63955938659695480250051889792 := by
  rw [← show ((([(2, 1), (13, 1), (149, 1), (36011226722801509149803993, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668882 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_2, prime_oneHundredEighteenDL_13, prime_oneHundredEighteenDL_149, prime_oneHundredEighteenDL_36011226722801509149803993]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668883 : Nat.totient 139507492324133046446340668883 = 83630847225544284345986211840 := by
  rw [← show ((([(3, 2), (17, 1), (23, 1), (887, 1), (27529, 1), (49919581, 1), (32523200639, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668883 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_3, prime_oneHundredEighteenDL_17, prime_oneHundredEighteenDL_23, prime_oneHundredEighteenDL_887, prime_oneHundredEighteenDL_27529, prime_oneHundredEighteenDL_49919581, prime_oneHundredEighteenDL_32523200639]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668884 : Nat.totient 139507492324133046446340668884 = 69753217295893473353023640064 := by
  rw [← show ((([(2, 2), (131893, 1), (264433086524935073215297, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668884 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_2, prime_oneHundredEighteenDL_131893, prime_oneHundredEighteenDL_264433086524935073215297]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668885 : Nat.totient 139507492324133046446340668885 = 95390976347672520066283725120 := by
  rw [← show ((([(5, 1), (7, 1), (367, 1), (8963, 1), (1211741626297785245891, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668885 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_5, prime_oneHundredEighteenDL_7, prime_oneHundredEighteenDL_367, prime_oneHundredEighteenDL_8963, prime_oneHundredEighteenDL_1211741626297785245891]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668886 : Nat.totient 139507492324133046446340668886 = 46502495869913033714041097928 := by
  rw [← show ((([(2, 1), (3, 1), (29591819, 1), (785732324217339970699, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668886 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_2, prime_oneHundredEighteenDL_3, prime_oneHundredEighteenDL_29591819, prime_oneHundredEighteenDL_785732324217339970699]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668887 : Nat.totient 139507492324133046446340668887 = 139507491262518050934711351168 := by
  rw [← show ((([(146137543, 1), (1306339753, 1), (730768111753, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668887 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_146137543, prime_oneHundredEighteenDL_1306339753, prime_oneHundredEighteenDL_730768111753]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668888 : Nat.totient 139507492324133046446340668888 = 68437637743870845876603810048 := by
  rw [← show ((([(2, 3), (53, 1), (1586081060903, 1), (207446588102329, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668888 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_2, prime_oneHundredEighteenDL_53, prime_oneHundredEighteenDL_1586081060903, prime_oneHundredEighteenDL_207446588102329]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668889 : Nat.totient 139507492324133046446340668889 = 88109995152084029334530948736 := by
  rw [← show ((([(3, 1), (19, 1), (2447499865335667481514748577, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668889 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_3, prime_oneHundredEighteenDL_19, prime_oneHundredEighteenDL_2447499865335667481514748577]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668890 : Nat.totient 139507492324133046446340668890 = 55791719324594018961220730880 := by
  rw [← show ((([(2, 1), (5, 1), (5417, 1), (74411, 1), (379033, 1), (708667, 1), (128849377, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668890 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_2, prime_oneHundredEighteenDL_5, prime_oneHundredEighteenDL_5417, prime_oneHundredEighteenDL_74411, prime_oneHundredEighteenDL_379033, prime_oneHundredEighteenDL_708667, prime_oneHundredEighteenDL_128849377]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668891 : Nat.totient 139507492324133046446340668891 = 139495198637833590179606343048 := by
  rw [← show ((([(12347, 1), (140227, 1), (80575765695478656139, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668891 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_12347, prime_oneHundredEighteenDL_140227, prime_oneHundredEighteenDL_80575765695478656139]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668892 : Nat.totient 139507492324133046446340668892 = 35281720285135954417751040000 := by
  rw [← show ((([(2, 2), (3, 2), (7, 1), (11, 1), (43, 1), (331, 1), (9349, 1), (70373, 1), (369991, 1), (14525981, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668892 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_2, prime_oneHundredEighteenDL_3, prime_oneHundredEighteenDL_7, prime_oneHundredEighteenDL_11, prime_oneHundredEighteenDL_43, prime_oneHundredEighteenDL_331, prime_oneHundredEighteenDL_9349, prime_oneHundredEighteenDL_70373, prime_oneHundredEighteenDL_369991, prime_oneHundredEighteenDL_14525981]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668893 : Nat.totient 139507492324133046446340668893 = 136300674315905763558562382400 := by
  rw [← show ((([(71, 1), (139, 1), (541, 1), (26129260470037911885317, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668893 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_71, prime_oneHundredEighteenDL_139, prime_oneHundredEighteenDL_541, prime_oneHundredEighteenDL_26129260470037911885317]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668894 : Nat.totient 139507492324133046446340668894 = 69579796670390546856030258400 := by
  rw [← show ((([(2, 1), (401, 1), (173949491675976367140075647, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668894 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_2, prime_oneHundredEighteenDL_401, prime_oneHundredEighteenDL_173949491675976367140075647]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668895 : Nat.totient 139507492324133046446340668895 = 68672750683274666868512821248 := by
  rw [← show ((([(3, 1), (5, 1), (13, 1), (8737, 1), (2240084947, 1), (36554100161399, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668895 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_3, prime_oneHundredEighteenDL_5, prime_oneHundredEighteenDL_13, prime_oneHundredEighteenDL_8737, prime_oneHundredEighteenDL_2240084947, prime_oneHundredEighteenDL_36554100161399]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668896 : Nat.totient 139507492324133046446340668896 = 69670578484508405577837667200 := by
  rw [← show ((([(2, 5), (839, 1), (2442151, 1), (2127713160960753727, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668896 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_2, prime_oneHundredEighteenDL_839, prime_oneHundredEighteenDL_2442151, prime_oneHundredEighteenDL_2127713160960753727]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668897 : Nat.totient 139507492324133046446340668897 = 138773219446960392704609203200 := by
  rw [← show ((([(337, 1), (479, 1), (4639, 1), (186297808204524070801, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668897 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_337, prime_oneHundredEighteenDL_479, prime_oneHundredEighteenDL_4639, prime_oneHundredEighteenDL_186297808204524070801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668898 : Nat.totient 139507492324133046446340668898 = 44763133608609891131937917952 := by
  rw [← show ((([(2, 1), (3, 1), (29, 1), (373, 1), (2897, 1), (741977877887111147467, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668898 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_2, prime_oneHundredEighteenDL_3, prime_oneHundredEighteenDL_29, prime_oneHundredEighteenDL_373, prime_oneHundredEighteenDL_2897, prime_oneHundredEighteenDL_741977877887111147467]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668899 : Nat.totient 139507492324133046446340668899 = 119301632466687309979808778240 := by
  rw [← show ((([(7, 2), (433, 1), (2126303, 1), (179491561, 1), (17228377109, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668899 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_7, prime_oneHundredEighteenDL_433, prime_oneHundredEighteenDL_2126303, prime_oneHundredEighteenDL_179491561, prime_oneHundredEighteenDL_17228377109]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668900 : Nat.totient 139507492324133046446340668900 = 52480098381755671429540608000 := by
  rw [← show ((([(2, 2), (5, 2), (17, 2), (1301, 1), (5138366503, 1), (722099950267, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668900 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_2, prime_oneHundredEighteenDL_5, prime_oneHundredEighteenDL_17, prime_oneHundredEighteenDL_1301, prime_oneHundredEighteenDL_5138366503, prime_oneHundredEighteenDL_722099950267]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredEighteenDL_139507492324133046446340668901 : Nat.totient 139507492324133046446340668901 = 90491346372410624721950703504 := by
  rw [← show ((([(3, 3), (37, 1), (139647139463596643089430099, 1)] : List FactorBlock).map factorBlockValue).prod) = 139507492324133046446340668901 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredEighteenDL_3, prime_oneHundredEighteenDL_37, prime_oneHundredEighteenDL_139647139463596643089430099]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64OneHundredEighteenDL : certifiedKill 1 139507492324133046446340668799 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_oneHundredEighteenDL_139507492324133046446340668800, phi_oneHundredEighteenDL_139507492324133046446340668801, phi_oneHundredEighteenDL_139507492324133046446340668802,
    phi_oneHundredEighteenDL_139507492324133046446340668803, phi_oneHundredEighteenDL_139507492324133046446340668804, phi_oneHundredEighteenDL_139507492324133046446340668805,
    phi_oneHundredEighteenDL_139507492324133046446340668806, phi_oneHundredEighteenDL_139507492324133046446340668807, phi_oneHundredEighteenDL_139507492324133046446340668808,
    phi_oneHundredEighteenDL_139507492324133046446340668809, phi_oneHundredEighteenDL_139507492324133046446340668810, phi_oneHundredEighteenDL_139507492324133046446340668811,
    phi_oneHundredEighteenDL_139507492324133046446340668812, phi_oneHundredEighteenDL_139507492324133046446340668813, phi_oneHundredEighteenDL_139507492324133046446340668814,
    phi_oneHundredEighteenDL_139507492324133046446340668815, phi_oneHundredEighteenDL_139507492324133046446340668816, phi_oneHundredEighteenDL_139507492324133046446340668817,
    phi_oneHundredEighteenDL_139507492324133046446340668818, phi_oneHundredEighteenDL_139507492324133046446340668819, phi_oneHundredEighteenDL_139507492324133046446340668820,
    phi_oneHundredEighteenDL_139507492324133046446340668821, phi_oneHundredEighteenDL_139507492324133046446340668822, phi_oneHundredEighteenDL_139507492324133046446340668823,
    phi_oneHundredEighteenDL_139507492324133046446340668824, phi_oneHundredEighteenDL_139507492324133046446340668825, phi_oneHundredEighteenDL_139507492324133046446340668826,
    phi_oneHundredEighteenDL_139507492324133046446340668827, phi_oneHundredEighteenDL_139507492324133046446340668828, phi_oneHundredEighteenDL_139507492324133046446340668829,
    phi_oneHundredEighteenDL_139507492324133046446340668830, phi_oneHundredEighteenDL_139507492324133046446340668831, phi_oneHundredEighteenDL_139507492324133046446340668832,
    phi_oneHundredEighteenDL_139507492324133046446340668833, phi_oneHundredEighteenDL_139507492324133046446340668834, phi_oneHundredEighteenDL_139507492324133046446340668835,
    phi_oneHundredEighteenDL_139507492324133046446340668836, phi_oneHundredEighteenDL_139507492324133046446340668837, phi_oneHundredEighteenDL_139507492324133046446340668838,
    phi_oneHundredEighteenDL_139507492324133046446340668839, phi_oneHundredEighteenDL_139507492324133046446340668840, phi_oneHundredEighteenDL_139507492324133046446340668841,
    phi_oneHundredEighteenDL_139507492324133046446340668842, phi_oneHundredEighteenDL_139507492324133046446340668843, phi_oneHundredEighteenDL_139507492324133046446340668844,
    phi_oneHundredEighteenDL_139507492324133046446340668845, phi_oneHundredEighteenDL_139507492324133046446340668846, phi_oneHundredEighteenDL_139507492324133046446340668847,
    phi_oneHundredEighteenDL_139507492324133046446340668848, phi_oneHundredEighteenDL_139507492324133046446340668849, phi_oneHundredEighteenDL_139507492324133046446340668850,
    phi_oneHundredEighteenDL_139507492324133046446340668851, phi_oneHundredEighteenDL_139507492324133046446340668852, phi_oneHundredEighteenDL_139507492324133046446340668853,
    phi_oneHundredEighteenDL_139507492324133046446340668854, phi_oneHundredEighteenDL_139507492324133046446340668855, phi_oneHundredEighteenDL_139507492324133046446340668856,
    phi_oneHundredEighteenDL_139507492324133046446340668857, phi_oneHundredEighteenDL_139507492324133046446340668858, phi_oneHundredEighteenDL_139507492324133046446340668859,
    phi_oneHundredEighteenDL_139507492324133046446340668860, phi_oneHundredEighteenDL_139507492324133046446340668861, phi_oneHundredEighteenDL_139507492324133046446340668862,
    phi_oneHundredEighteenDL_139507492324133046446340668863, phi_oneHundredEighteenDL_139507492324133046446340668864, phi_oneHundredEighteenDL_139507492324133046446340668865,
    phi_oneHundredEighteenDL_139507492324133046446340668866, phi_oneHundredEighteenDL_139507492324133046446340668867, phi_oneHundredEighteenDL_139507492324133046446340668868,
    phi_oneHundredEighteenDL_139507492324133046446340668869, phi_oneHundredEighteenDL_139507492324133046446340668870, phi_oneHundredEighteenDL_139507492324133046446340668871,
    phi_oneHundredEighteenDL_139507492324133046446340668872, phi_oneHundredEighteenDL_139507492324133046446340668873, phi_oneHundredEighteenDL_139507492324133046446340668874,
    phi_oneHundredEighteenDL_139507492324133046446340668875, phi_oneHundredEighteenDL_139507492324133046446340668876, phi_oneHundredEighteenDL_139507492324133046446340668877,
    phi_oneHundredEighteenDL_139507492324133046446340668878, phi_oneHundredEighteenDL_139507492324133046446340668879, phi_oneHundredEighteenDL_139507492324133046446340668880,
    phi_oneHundredEighteenDL_139507492324133046446340668881, phi_oneHundredEighteenDL_139507492324133046446340668882, phi_oneHundredEighteenDL_139507492324133046446340668883,
    phi_oneHundredEighteenDL_139507492324133046446340668884, phi_oneHundredEighteenDL_139507492324133046446340668885, phi_oneHundredEighteenDL_139507492324133046446340668886,
    phi_oneHundredEighteenDL_139507492324133046446340668887, phi_oneHundredEighteenDL_139507492324133046446340668888, phi_oneHundredEighteenDL_139507492324133046446340668889,
    phi_oneHundredEighteenDL_139507492324133046446340668890, phi_oneHundredEighteenDL_139507492324133046446340668891, phi_oneHundredEighteenDL_139507492324133046446340668892,
    phi_oneHundredEighteenDL_139507492324133046446340668893, phi_oneHundredEighteenDL_139507492324133046446340668894, phi_oneHundredEighteenDL_139507492324133046446340668895,
    phi_oneHundredEighteenDL_139507492324133046446340668896, phi_oneHundredEighteenDL_139507492324133046446340668897, phi_oneHundredEighteenDL_139507492324133046446340668898,
    phi_oneHundredEighteenDL_139507492324133046446340668899, phi_oneHundredEighteenDL_139507492324133046446340668900, phi_oneHundredEighteenDL_139507492324133046446340668901
    ]

end TotientTailPeriodKiller
end Erdos249257
