import Erdos249257.DiagonalPincerCertificatesT64

/- Kernel-checked off-diagonal certificate at a freely chosen position. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def oneHundredTwentyThreeDQFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem oneHundredTwentyThreeDQFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : oneHundredTwentyThreeDQFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [oneHundredTwentyThreeDQFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [oneHundredTwentyThreeDQFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then oneHundredTwentyThreeDQFastPow a n * oneHundredTwentyThreeDQFastPow a n * a else oneHundredTwentyThreeDQFastPow a n * oneHundredTwentyThreeDQFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_oneHundredTwentyThreeDQ_2 : Nat.Prime 2 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_3 : Nat.Prime 3 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_5 : Nat.Prime 5 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_7 : Nat.Prime 7 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_11 : Nat.Prime 11 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_13 : Nat.Prime 13 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_17 : Nat.Prime 17 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_19 : Nat.Prime 19 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_23 : Nat.Prime 23 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_29 : Nat.Prime 29 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_31 : Nat.Prime 31 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_37 : Nat.Prime 37 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_41 : Nat.Prime 41 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_43 : Nat.Prime 43 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_47 : Nat.Prime 47 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_53 : Nat.Prime 53 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_59 : Nat.Prime 59 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_61 : Nat.Prime 61 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_67 : Nat.Prime 67 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_71 : Nat.Prime 71 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_73 : Nat.Prime 73 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_79 : Nat.Prime 79 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_83 : Nat.Prime 83 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_89 : Nat.Prime 89 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_97 : Nat.Prime 97 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_101 : Nat.Prime 101 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_103 : Nat.Prime 103 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_107 : Nat.Prime 107 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_109 : Nat.Prime 109 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_113 : Nat.Prime 113 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_127 : Nat.Prime 127 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_131 : Nat.Prime 131 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_137 : Nat.Prime 137 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_139 : Nat.Prime 139 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_149 : Nat.Prime 149 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_151 : Nat.Prime 151 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_157 : Nat.Prime 157 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_163 : Nat.Prime 163 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_167 : Nat.Prime 167 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_173 : Nat.Prime 173 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_179 : Nat.Prime 179 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_181 : Nat.Prime 181 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_191 : Nat.Prime 191 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_193 : Nat.Prime 193 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_197 : Nat.Prime 197 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_199 : Nat.Prime 199 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_211 : Nat.Prime 211 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_223 : Nat.Prime 223 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_227 : Nat.Prime 227 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_229 : Nat.Prime 229 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_233 : Nat.Prime 233 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_239 : Nat.Prime 239 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_241 : Nat.Prime 241 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_251 : Nat.Prime 251 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_263 : Nat.Prime 263 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_269 : Nat.Prime 269 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_271 : Nat.Prime 271 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_281 : Nat.Prime 281 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_283 : Nat.Prime 283 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_293 : Nat.Prime 293 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_307 : Nat.Prime 307 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_311 : Nat.Prime 311 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_337 : Nat.Prime 337 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_349 : Nat.Prime 349 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_359 : Nat.Prime 359 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_373 : Nat.Prime 373 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_379 : Nat.Prime 379 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_389 : Nat.Prime 389 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_397 : Nat.Prime 397 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_401 : Nat.Prime 401 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_421 : Nat.Prime 421 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_431 : Nat.Prime 431 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_433 : Nat.Prime 433 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_439 : Nat.Prime 439 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_443 : Nat.Prime 443 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_449 : Nat.Prime 449 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_461 : Nat.Prime 461 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_467 : Nat.Prime 467 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_491 : Nat.Prime 491 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_503 : Nat.Prime 503 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_509 : Nat.Prime 509 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_521 : Nat.Prime 521 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_523 : Nat.Prime 523 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_541 : Nat.Prime 541 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_563 : Nat.Prime 563 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_569 : Nat.Prime 569 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_587 : Nat.Prime 587 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_601 : Nat.Prime 601 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_607 : Nat.Prime 607 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_619 : Nat.Prime 619 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_631 : Nat.Prime 631 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_653 : Nat.Prime 653 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_659 : Nat.Prime 659 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_661 : Nat.Prime 661 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_683 : Nat.Prime 683 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_709 : Nat.Prime 709 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_719 : Nat.Prime 719 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_773 : Nat.Prime 773 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_797 : Nat.Prime 797 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_811 : Nat.Prime 811 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_821 : Nat.Prime 821 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_857 : Nat.Prime 857 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_859 : Nat.Prime 859 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_877 : Nat.Prime 877 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_887 : Nat.Prime 887 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_907 : Nat.Prime 907 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_929 : Nat.Prime 929 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_947 : Nat.Prime 947 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_967 : Nat.Prime 967 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_971 : Nat.Prime 971 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_977 : Nat.Prime 977 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_991 : Nat.Prime 991 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_997 : Nat.Prime 997 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_1009 : Nat.Prime 1009 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_1049 : Nat.Prime 1049 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_1109 : Nat.Prime 1109 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_1117 : Nat.Prime 1117 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_1151 : Nat.Prime 1151 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_1201 : Nat.Prime 1201 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_1223 : Nat.Prime 1223 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_1229 : Nat.Prime 1229 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_1289 : Nat.Prime 1289 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_1321 : Nat.Prime 1321 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_1327 : Nat.Prime 1327 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_1381 : Nat.Prime 1381 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_1427 : Nat.Prime 1427 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_1433 : Nat.Prime 1433 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_1439 : Nat.Prime 1439 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_1451 : Nat.Prime 1451 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_1489 : Nat.Prime 1489 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_1499 : Nat.Prime 1499 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_1549 : Nat.Prime 1549 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_1559 : Nat.Prime 1559 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_1583 : Nat.Prime 1583 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_1619 : Nat.Prime 1619 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_1627 : Nat.Prime 1627 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_1637 : Nat.Prime 1637 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_1657 : Nat.Prime 1657 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_1693 : Nat.Prime 1693 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_1733 : Nat.Prime 1733 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_1753 : Nat.Prime 1753 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_1783 : Nat.Prime 1783 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_1847 : Nat.Prime 1847 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_1871 : Nat.Prime 1871 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_1877 : Nat.Prime 1877 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_1901 : Nat.Prime 1901 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_1907 : Nat.Prime 1907 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_1933 : Nat.Prime 1933 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_1979 : Nat.Prime 1979 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_1999 : Nat.Prime 1999 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_2003 : Nat.Prime 2003 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_2083 : Nat.Prime 2083 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_2161 : Nat.Prime 2161 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_2221 : Nat.Prime 2221 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_2237 : Nat.Prime 2237 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_2267 : Nat.Prime 2267 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_2269 : Nat.Prime 2269 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_2281 : Nat.Prime 2281 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_2287 : Nat.Prime 2287 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_2293 : Nat.Prime 2293 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_2339 : Nat.Prime 2339 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_2549 : Nat.Prime 2549 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_2621 : Nat.Prime 2621 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_2657 : Nat.Prime 2657 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_2693 : Nat.Prime 2693 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_2699 : Nat.Prime 2699 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_2909 : Nat.Prime 2909 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_2927 : Nat.Prime 2927 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_2999 : Nat.Prime 2999 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_3137 : Nat.Prime 3137 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_3323 : Nat.Prime 3323 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_3491 : Nat.Prime 3491 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_3623 : Nat.Prime 3623 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_4013 : Nat.Prime 4013 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_4057 : Nat.Prime 4057 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_4111 : Nat.Prime 4111 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_4241 : Nat.Prime 4241 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_4261 : Nat.Prime 4261 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_4283 : Nat.Prime 4283 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_4421 : Nat.Prime 4421 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_4463 : Nat.Prime 4463 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_4507 : Nat.Prime 4507 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_4519 : Nat.Prime 4519 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_4523 : Nat.Prime 4523 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_4957 : Nat.Prime 4957 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_4993 : Nat.Prime 4993 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_5081 : Nat.Prime 5081 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_5189 : Nat.Prime 5189 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_5417 : Nat.Prime 5417 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_5443 : Nat.Prime 5443 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_5779 : Nat.Prime 5779 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_5881 : Nat.Prime 5881 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_6089 : Nat.Prime 6089 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_6299 : Nat.Prime 6299 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_6317 : Nat.Prime 6317 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_6701 : Nat.Prime 6701 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_6863 : Nat.Prime 6863 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_6907 : Nat.Prime 6907 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_7369 : Nat.Prime 7369 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_7699 : Nat.Prime 7699 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_8009 : Nat.Prime 8009 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_8081 : Nat.Prime 8081 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_8191 : Nat.Prime 8191 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_8297 : Nat.Prime 8297 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_8581 : Nat.Prime 8581 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_8707 : Nat.Prime 8707 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_8867 : Nat.Prime 8867 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_8929 : Nat.Prime 8929 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_10139 : Nat.Prime 10139 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_10501 : Nat.Prime 10501 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_10597 : Nat.Prime 10597 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_11549 : Nat.Prime 11549 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_12433 : Nat.Prime 12433 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_12547 : Nat.Prime 12547 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_12613 : Nat.Prime 12613 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_12697 : Nat.Prime 12697 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_12959 : Nat.Prime 12959 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_13127 : Nat.Prime 13127 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_13229 : Nat.Prime 13229 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_13859 : Nat.Prime 13859 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_13883 : Nat.Prime 13883 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_13963 : Nat.Prime 13963 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_14461 : Nat.Prime 14461 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_15139 : Nat.Prime 15139 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_15319 : Nat.Prime 15319 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_16567 : Nat.Prime 16567 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_17203 : Nat.Prime 17203 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_17449 : Nat.Prime 17449 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_18191 : Nat.Prime 18191 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_19507 : Nat.Prime 19507 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_20071 : Nat.Prime 20071 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_20183 : Nat.Prime 20183 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_20411 : Nat.Prime 20411 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_20753 : Nat.Prime 20753 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_21817 : Nat.Prime 21817 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_22369 : Nat.Prime 22369 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_23027 : Nat.Prime 23027 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_23209 : Nat.Prime 23209 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_24337 : Nat.Prime 24337 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_24971 : Nat.Prime 24971 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_25013 : Nat.Prime 25013 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_25031 : Nat.Prime 25031 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_25117 : Nat.Prime 25117 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_25867 : Nat.Prime 25867 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_27061 : Nat.Prime 27061 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_28933 : Nat.Prime 28933 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_29021 : Nat.Prime 29021 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_29879 : Nat.Prime 29879 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_30113 : Nat.Prime 30113 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_31177 : Nat.Prime 31177 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_31327 : Nat.Prime 31327 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_31723 : Nat.Prime 31723 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_33521 : Nat.Prime 33521 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_34361 : Nat.Prime 34361 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_35509 : Nat.Prime 35509 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_37663 : Nat.Prime 37663 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_39293 : Nat.Prime 39293 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_40759 : Nat.Prime 40759 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_41969 : Nat.Prime 41969 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_42937 : Nat.Prime 42937 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_43067 : Nat.Prime 43067 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_44641 : Nat.Prime 44641 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_45119 : Nat.Prime 45119 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_46457 : Nat.Prime 46457 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_47713 : Nat.Prime 47713 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_49783 : Nat.Prime 49783 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_52981 : Nat.Prime 52981 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_55073 : Nat.Prime 55073 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_55343 : Nat.Prime 55343 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_56099 : Nat.Prime 56099 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_56263 : Nat.Prime 56263 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_56311 : Nat.Prime 56311 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_59779 : Nat.Prime 59779 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_61031 : Nat.Prime 61031 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_61261 : Nat.Prime 61261 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_61673 : Nat.Prime 61673 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_63689 : Nat.Prime 63689 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_65413 : Nat.Prime 65413 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_65867 : Nat.Prime 65867 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_66239 : Nat.Prime 66239 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_70061 : Nat.Prime 70061 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_71443 : Nat.Prime 71443 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_72173 : Nat.Prime 72173 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_77347 : Nat.Prime 77347 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_77527 : Nat.Prime 77527 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_78539 : Nat.Prime 78539 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_84313 : Nat.Prime 84313 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_104677 : Nat.Prime 104677 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_105601 : Nat.Prime 105601 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_108739 : Nat.Prime 108739 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_109211 : Nat.Prime 109211 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_115337 : Nat.Prime 115337 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_125711 : Nat.Prime 125711 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_134287 : Nat.Prime 134287 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_135829 : Nat.Prime 135829 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_139943 : Nat.Prime 139943 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_140797 : Nat.Prime 140797 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_143257 : Nat.Prime 143257 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_147557 : Nat.Prime 147557 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_150001 : Nat.Prime 150001 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_153281 : Nat.Prime 153281 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_160093 : Nat.Prime 160093 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_164627 : Nat.Prime 164627 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_166189 : Nat.Prime 166189 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_171401 : Nat.Prime 171401 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_174299 : Nat.Prime 174299 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_175519 : Nat.Prime 175519 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_179951 : Nat.Prime 179951 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_215389 : Nat.Prime 215389 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_216071 : Nat.Prime 216071 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_221713 : Nat.Prime 221713 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_232681 : Nat.Prime 232681 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_233759 : Nat.Prime 233759 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_247943 : Nat.Prime 247943 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_256187 : Nat.Prime 256187 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_257893 : Nat.Prime 257893 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_271211 : Nat.Prime 271211 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_275543 : Nat.Prime 275543 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_284341 : Nat.Prime 284341 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_284831 : Nat.Prime 284831 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_293179 : Nat.Prime 293179 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_300667 : Nat.Prime 300667 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_301759 : Nat.Prime 301759 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_302723 : Nat.Prime 302723 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_306517 : Nat.Prime 306517 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_307267 : Nat.Prime 307267 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_317353 : Nat.Prime 317353 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_341461 : Nat.Prime 341461 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_347969 : Nat.Prime 347969 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_348431 : Nat.Prime 348431 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_381019 : Nat.Prime 381019 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_387169 : Nat.Prime 387169 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_396619 : Nat.Prime 396619 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_408389 : Nat.Prime 408389 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_421433 : Nat.Prime 421433 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_489257 : Nat.Prime 489257 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_498521 : Nat.Prime 498521 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_519119 : Nat.Prime 519119 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_561019 : Nat.Prime 561019 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_566701 : Nat.Prime 566701 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_567467 : Nat.Prime 567467 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_569419 : Nat.Prime 569419 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_600641 : Nat.Prime 600641 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_636931 : Nat.Prime 636931 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_718807 : Nat.Prime 718807 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_752833 : Nat.Prime 752833 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_796373 : Nat.Prime 796373 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_825007 : Nat.Prime 825007 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_851293 : Nat.Prime 851293 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_856147 : Nat.Prime 856147 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_869419 : Nat.Prime 869419 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_908377 : Nat.Prime 908377 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_937477 : Nat.Prime 937477 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_1017847 : Nat.Prime 1017847 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_1019503 : Nat.Prime 1019503 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_1069727 : Nat.Prime 1069727 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_1182289 : Nat.Prime 1182289 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_1326653 : Nat.Prime 1326653 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_1450711 : Nat.Prime 1450711 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_1548739 : Nat.Prime 1548739 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_1700723 : Nat.Prime 1700723 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_1748963 : Nat.Prime 1748963 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_2002229 : Nat.Prime 2002229 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_2005151 : Nat.Prime 2005151 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_2009593 : Nat.Prime 2009593 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_2023121 : Nat.Prime 2023121 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_2070643 : Nat.Prime 2070643 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_2096209 : Nat.Prime 2096209 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_2167579 : Nat.Prime 2167579 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_2306053 : Nat.Prime 2306053 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_2384831 : Nat.Prime 2384831 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_2386591 : Nat.Prime 2386591 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_2439301 : Nat.Prime 2439301 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_2514931 : Nat.Prime 2514931 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_2604677 : Nat.Prime 2604677 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_2607469 : Nat.Prime 2607469 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_2908937 : Nat.Prime 2908937 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_3081119 : Nat.Prime 3081119 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_3117209 : Nat.Prime 3117209 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_3248689 : Nat.Prime 3248689 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_3392041 : Nat.Prime 3392041 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_3398309 : Nat.Prime 3398309 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_3618071 : Nat.Prime 3618071 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_3822383 : Nat.Prime 3822383 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_4119133 : Nat.Prime 4119133 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_4281047 : Nat.Prime 4281047 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_4719287 : Nat.Prime 4719287 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_4946003 : Nat.Prime 4946003 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_5265851 : Nat.Prime 5265851 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_5295791 : Nat.Prime 5295791 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_5332973 : Nat.Prime 5332973 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_5487451 : Nat.Prime 5487451 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_5733337 : Nat.Prime 5733337 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_6362311 : Nat.Prime 6362311 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_6498727 : Nat.Prime 6498727 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_6932339 : Nat.Prime 6932339 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_7795763 : Nat.Prime 7795763 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_7827331 : Nat.Prime 7827331 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_8493257 : Nat.Prime 8493257 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_8657771 : Nat.Prime 8657771 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_8772727 : Nat.Prime 8772727 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_9039061 : Nat.Prime 9039061 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_10820141 : Nat.Prime 10820141 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_11003347 : Nat.Prime 11003347 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_11231657 : Nat.Prime 11231657 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_11266873 : Nat.Prime 11266873 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_11547463 : Nat.Prime 11547463 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_11910809 : Nat.Prime 11910809 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_12126643 : Nat.Prime 12126643 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_13417171 : Nat.Prime 13417171 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_13439191 : Nat.Prime 13439191 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_13454101 : Nat.Prime 13454101 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_14123063 : Nat.Prime 14123063 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_14260049 : Nat.Prime 14260049 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_14279443 : Nat.Prime 14279443 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_14799739 : Nat.Prime 14799739 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_14996321 : Nat.Prime 14996321 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_15975769 : Nat.Prime 15975769 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_16538827 : Nat.Prime 16538827 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_18529163 : Nat.Prime 18529163 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_18583861 : Nat.Prime 18583861 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_20162537 : Nat.Prime 20162537 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_20697107 : Nat.Prime 20697107 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_20787667 : Nat.Prime 20787667 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_21723721 : Nat.Prime 21723721 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_23864609 : Nat.Prime 23864609 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_24469429 : Nat.Prime 24469429 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_24925801 : Nat.Prime 24925801 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_25003499 : Nat.Prime 25003499 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_25189729 : Nat.Prime 25189729 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_28453823 : Nat.Prime 28453823 := by norm_num

private theorem prime_oneHundredTwentyThreeDQ_30055901 : Nat.Prime 30055901 := by
  apply lucas_primality 30055901 (10 : ZMod 30055901)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (7, 1), (42937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (7, 1), (42937, 1)] : List FactorBlock).map factorBlockValue).prod) = 30055901 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_5
      · exact prime_oneHundredTwentyThreeDQ_7
      · exact prime_oneHundredTwentyThreeDQ_42937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 30055901) ^ 15027950 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (10 : ZMod 30055901) ^ 6011180 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (10 : ZMod 30055901) ^ 4293700 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (10 : ZMod 30055901) ^ 700 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_33374239 : Nat.Prime 33374239 := by
  apply lucas_primality 33374239 (3 : ZMod 33374239)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (101, 1), (55073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (101, 1), (55073, 1)] : List FactorBlock).map factorBlockValue).prod) = 33374239 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_101
      · exact prime_oneHundredTwentyThreeDQ_55073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 33374239) ^ 16687119 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 33374239) ^ 11124746 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 33374239) ^ 330438 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 33374239) ^ 606 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_33470887 : Nat.Prime 33470887 := by
  apply lucas_primality 33470887 (3 : ZMod 33470887)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (179951, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (179951, 1)] : List FactorBlock).map factorBlockValue).prod) = 33470887 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_31
      · exact prime_oneHundredTwentyThreeDQ_179951
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 33470887) ^ 16735443 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 33470887) ^ 11156962 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 33470887) ^ 1079706 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 33470887) ^ 186 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_33546529 : Nat.Prime 33546529 := by
  apply lucas_primality 33546529 (19 : ZMod 33546529)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 3), (41, 1), (947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 3), (41, 1), (947, 1)] : List FactorBlock).map factorBlockValue).prod) = 33546529 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_41
      · exact prime_oneHundredTwentyThreeDQ_947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 33546529) ^ 16773264 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (19 : ZMod 33546529) ^ 11182176 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (19 : ZMod 33546529) ^ 818208 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (19 : ZMod 33546529) ^ 35424 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_34954709 : Nat.Prime 34954709 := by
  apply lucas_primality 34954709 (2 : ZMod 34954709)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (61, 1), (143257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (61, 1), (143257, 1)] : List FactorBlock).map factorBlockValue).prod) = 34954709 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_61
      · exact prime_oneHundredTwentyThreeDQ_143257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 34954709) ^ 17477354 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 34954709) ^ 573028 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 34954709) ^ 244 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_37058327 : Nat.Prime 37058327 := by
  apply lucas_primality 37058327 (5 : ZMod 37058327)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (18529163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (18529163, 1)] : List FactorBlock).map factorBlockValue).prod) = 37058327 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_18529163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 37058327) ^ 18529163 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 37058327) ^ 2 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_38192599 : Nat.Prime 38192599 := by
  apply lucas_primality 38192599 (3 : ZMod 38192599)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (523, 1), (4057, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (523, 1), (4057, 1)] : List FactorBlock).map factorBlockValue).prod) = 38192599 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_523
      · exact prime_oneHundredTwentyThreeDQ_4057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 38192599) ^ 19096299 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 38192599) ^ 12730866 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 38192599) ^ 73026 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 38192599) ^ 9414 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_38710171 : Nat.Prime 38710171 := by
  apply lucas_primality 38710171 (2 : ZMod 38710171)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (311, 1), (461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (311, 1), (461, 1)] : List FactorBlock).map factorBlockValue).prod) = 38710171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_5
      · exact prime_oneHundredTwentyThreeDQ_311
      · exact prime_oneHundredTwentyThreeDQ_461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 38710171) ^ 19355085 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 38710171) ^ 12903390 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 38710171) ^ 7742034 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 38710171) ^ 124470 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 38710171) ^ 83970 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_39668467 : Nat.Prime 39668467 := by
  apply lucas_primality 39668467 (2 : ZMod 39668467)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (347969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (347969, 1)] : List FactorBlock).map factorBlockValue).prod) = 39668467 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_19
      · exact prime_oneHundredTwentyThreeDQ_347969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 39668467) ^ 19834233 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 39668467) ^ 13222822 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 39668467) ^ 2087814 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 39668467) ^ 114 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_43071731 : Nat.Prime 43071731 := by
  apply lucas_primality 43071731 (2 : ZMod 43071731)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (41, 1), (8081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (41, 1), (8081, 1)] : List FactorBlock).map factorBlockValue).prod) = 43071731 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_5
      · exact prime_oneHundredTwentyThreeDQ_13
      · exact prime_oneHundredTwentyThreeDQ_41
      · exact prime_oneHundredTwentyThreeDQ_8081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 43071731) ^ 21535865 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 43071731) ^ 8614346 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 43071731) ^ 3313210 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 43071731) ^ 1050530 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 43071731) ^ 5330 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_47729219 : Nat.Prime 47729219 := by
  apply lucas_primality 47729219 (2 : ZMod 47729219)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23864609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23864609, 1)] : List FactorBlock).map factorBlockValue).prod) = 47729219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_23864609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 47729219) ^ 23864609 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 47729219) ^ 2 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_50733167 : Nat.Prime 50733167 := by
  apply lucas_primality 50733167 (5 : ZMod 50733167)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (2306053, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (2306053, 1)] : List FactorBlock).map factorBlockValue).prod) = 50733167 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_11
      · exact prime_oneHundredTwentyThreeDQ_2306053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 50733167) ^ 25366583 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 50733167) ^ 4612106 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 50733167) ^ 22 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_60111803 : Nat.Prime 60111803 := by
  apply lucas_primality 60111803 (2 : ZMod 60111803)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (30055901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (30055901, 1)] : List FactorBlock).map factorBlockValue).prod) = 60111803 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_30055901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 60111803) ^ 30055901 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 60111803) ^ 2 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_61310069 : Nat.Prime 61310069 := by
  apply lucas_primality 61310069 (2 : ZMod 61310069)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (509, 1), (30113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (509, 1), (30113, 1)] : List FactorBlock).map factorBlockValue).prod) = 61310069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_509
      · exact prime_oneHundredTwentyThreeDQ_30113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 61310069) ^ 30655034 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 61310069) ^ 120452 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 61310069) ^ 2036 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_66146741 : Nat.Prime 66146741 := by
  apply lucas_primality 66146741 (7 : ZMod 66146741)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (11, 1), (300667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (11, 1), (300667, 1)] : List FactorBlock).map factorBlockValue).prod) = 66146741 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_5
      · exact prime_oneHundredTwentyThreeDQ_11
      · exact prime_oneHundredTwentyThreeDQ_300667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 66146741) ^ 33073370 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (7 : ZMod 66146741) ^ 13229348 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (7 : ZMod 66146741) ^ 6013340 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (7 : ZMod 66146741) ^ 220 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_67601239 : Nat.Prime 67601239 := by
  apply lucas_primality 67601239 (3 : ZMod 67601239)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11266873, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11266873, 1)] : List FactorBlock).map factorBlockValue).prod) = 67601239 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_11266873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 67601239) ^ 33800619 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 67601239) ^ 22533746 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 67601239) ^ 6 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_69831491 : Nat.Prime 69831491 := by
  apply lucas_primality 69831491 (6 : ZMod 69831491)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (503, 1), (13883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (503, 1), (13883, 1)] : List FactorBlock).map factorBlockValue).prod) = 69831491 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_5
      · exact prime_oneHundredTwentyThreeDQ_503
      · exact prime_oneHundredTwentyThreeDQ_13883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 69831491) ^ 34915745 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (6 : ZMod 69831491) ^ 13966298 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (6 : ZMod 69831491) ^ 138830 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (6 : ZMod 69831491) ^ 5030 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_69909419 : Nat.Prime 69909419 := by
  apply lucas_primality 69909419 (2 : ZMod 69909419)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (34954709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (34954709, 1)] : List FactorBlock).map factorBlockValue).prod) = 69909419 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_34954709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 69909419) ^ 34954709 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 69909419) ^ 2 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_72759859 : Nat.Prime 72759859 := by
  apply lucas_primality 72759859 (3 : ZMod 72759859)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (12126643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (12126643, 1)] : List FactorBlock).map factorBlockValue).prod) = 72759859 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_12126643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 72759859) ^ 36379929 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 72759859) ^ 24253286 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 72759859) ^ 6 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_82411187 : Nat.Prime 82411187 := by
  apply lucas_primality 82411187 (2 : ZMod 82411187)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (13, 1), (107, 1), (2693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (13, 1), (107, 1), (2693, 1)] : List FactorBlock).map factorBlockValue).prod) = 82411187 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_11
      · exact prime_oneHundredTwentyThreeDQ_13
      · exact prime_oneHundredTwentyThreeDQ_107
      · exact prime_oneHundredTwentyThreeDQ_2693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 82411187) ^ 41205593 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 82411187) ^ 7491926 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 82411187) ^ 6339322 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 82411187) ^ 770198 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 82411187) ^ 30602 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_82758073 : Nat.Prime 82758073 := by
  apply lucas_primality 82758073 (10 : ZMod 82758073)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (19, 1), (97, 1), (1871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (19, 1), (97, 1), (1871, 1)] : List FactorBlock).map factorBlockValue).prod) = 82758073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_19
      · exact prime_oneHundredTwentyThreeDQ_97
      · exact prime_oneHundredTwentyThreeDQ_1871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 82758073) ^ 41379036 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (10 : ZMod 82758073) ^ 27586024 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (10 : ZMod 82758073) ^ 4355688 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (10 : ZMod 82758073) ^ 853176 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (10 : ZMod 82758073) ^ 44232 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_83849483 : Nat.Prime 83849483 := by
  apply lucas_primality 83849483 (2 : ZMod 83849483)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (163, 1), (8297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (163, 1), (8297, 1)] : List FactorBlock).map factorBlockValue).prod) = 83849483 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_31
      · exact prime_oneHundredTwentyThreeDQ_163
      · exact prime_oneHundredTwentyThreeDQ_8297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 83849483) ^ 41924741 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 83849483) ^ 2704822 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 83849483) ^ 514414 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 83849483) ^ 10106 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_84059999 : Nat.Prime 84059999 := by
  apply lucas_primality 84059999 (7 : ZMod 84059999)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (157, 1), (24337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (157, 1), (24337, 1)] : List FactorBlock).map factorBlockValue).prod) = 84059999 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_11
      · exact prime_oneHundredTwentyThreeDQ_157
      · exact prime_oneHundredTwentyThreeDQ_24337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 84059999) ^ 42029999 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (7 : ZMod 84059999) ^ 7641818 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (7 : ZMod 84059999) ^ 535414 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (7 : ZMod 84059999) ^ 3454 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_91761259 : Nat.Prime 91761259 := by
  apply lucas_primality 91761259 (2 : ZMod 91761259)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (37, 1), (103, 1), (4013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (37, 1), (103, 1), (4013, 1)] : List FactorBlock).map factorBlockValue).prod) = 91761259 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_37
      · exact prime_oneHundredTwentyThreeDQ_103
      · exact prime_oneHundredTwentyThreeDQ_4013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 91761259) ^ 45880629 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 91761259) ^ 30587086 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 91761259) ^ 2480034 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 91761259) ^ 890886 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 91761259) ^ 22866 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_95458439 : Nat.Prime 95458439 := by
  apply lucas_primality 95458439 (13 : ZMod 95458439)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47729219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47729219, 1)] : List FactorBlock).map factorBlockValue).prod) = 95458439 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_47729219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (13 : ZMod 95458439) ^ 47729219 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (13 : ZMod 95458439) ^ 2 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_102808553 : Nat.Prime 102808553 := by
  apply lucas_primality 102808553 (3 : ZMod 102808553)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (11, 1), (47, 1), (53, 1), (67, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (11, 1), (47, 1), (53, 1), (67, 1)] : List FactorBlock).map factorBlockValue).prod) = 102808553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_7
      · exact prime_oneHundredTwentyThreeDQ_11
      · exact prime_oneHundredTwentyThreeDQ_47
      · exact prime_oneHundredTwentyThreeDQ_53
      · exact prime_oneHundredTwentyThreeDQ_67
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 102808553) ^ 51404276 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 102808553) ^ 14686936 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 102808553) ^ 9346232 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 102808553) ^ 2187416 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 102808553) ^ 1939784 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 102808553) ^ 1534456 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_107966143 : Nat.Prime 107966143 := by
  apply lucas_primality 107966143 (5 : ZMod 107966143)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (233, 1), (8581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (233, 1), (8581, 1)] : List FactorBlock).map factorBlockValue).prod) = 107966143 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_233
      · exact prime_oneHundredTwentyThreeDQ_8581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 107966143) ^ 53983071 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 107966143) ^ 35988714 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 107966143) ^ 463374 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 107966143) ^ 12582 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_110858731 : Nat.Prime 110858731 := by
  apply lucas_primality 110858731 (3 : ZMod 110858731)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (19, 1), (43, 1), (4523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (19, 1), (43, 1), (4523, 1)] : List FactorBlock).map factorBlockValue).prod) = 110858731 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_5
      · exact prime_oneHundredTwentyThreeDQ_19
      · exact prime_oneHundredTwentyThreeDQ_43
      · exact prime_oneHundredTwentyThreeDQ_4523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 110858731) ^ 55429365 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 110858731) ^ 36952910 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 110858731) ^ 22171746 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 110858731) ^ 5834670 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 110858731) ^ 2578110 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 110858731) ^ 24510 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_115474631 : Nat.Prime 115474631 := by
  apply lucas_primality 115474631 (17 : ZMod 115474631)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11547463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11547463, 1)] : List FactorBlock).map factorBlockValue).prod) = 115474631 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_5
      · exact prime_oneHundredTwentyThreeDQ_11547463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (17 : ZMod 115474631) ^ 57737315 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (17 : ZMod 115474631) ^ 23094926 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (17 : ZMod 115474631) ^ 10 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_130500871 : Nat.Prime 130500871 := by
  apply lucas_primality 130500871 (3 : ZMod 130500871)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (29, 1), (150001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (29, 1), (150001, 1)] : List FactorBlock).map factorBlockValue).prod) = 130500871 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_5
      · exact prime_oneHundredTwentyThreeDQ_29
      · exact prime_oneHundredTwentyThreeDQ_150001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 130500871) ^ 65250435 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 130500871) ^ 43500290 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 130500871) ^ 26100174 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 130500871) ^ 4500030 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 130500871) ^ 870 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_132339967 : Nat.Prime 132339967 := by
  apply lucas_primality 132339967 (3 : ZMod 132339967)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (2005151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (2005151, 1)] : List FactorBlock).map factorBlockValue).prod) = 132339967 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_11
      · exact prime_oneHundredTwentyThreeDQ_2005151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 132339967) ^ 66169983 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 132339967) ^ 44113322 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 132339967) ^ 12030906 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 132339967) ^ 66 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_140866157 : Nat.Prime 140866157 := by
  apply lucas_primality 140866157 (2 : ZMod 140866157)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (53, 1), (503, 1), (1321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (53, 1), (503, 1), (1321, 1)] : List FactorBlock).map factorBlockValue).prod) = 140866157 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_53
      · exact prime_oneHundredTwentyThreeDQ_503
      · exact prime_oneHundredTwentyThreeDQ_1321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 140866157) ^ 70433078 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 140866157) ^ 2657852 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 140866157) ^ 280052 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 140866157) ^ 106636 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_143590061 : Nat.Prime 143590061 := by
  apply lucas_primality 143590061 (2 : ZMod 143590061)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (109, 1), (65867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (109, 1), (65867, 1)] : List FactorBlock).map factorBlockValue).prod) = 143590061 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_5
      · exact prime_oneHundredTwentyThreeDQ_109
      · exact prime_oneHundredTwentyThreeDQ_65867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 143590061) ^ 71795030 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 143590061) ^ 28718012 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 143590061) ^ 1317340 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 143590061) ^ 2180 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_146441219 : Nat.Prime 146441219 := by
  apply lucas_primality 146441219 (6 : ZMod 146441219)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 2), (137, 1), (631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 2), (137, 1), (631, 1)] : List FactorBlock).map factorBlockValue).prod) = 146441219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_7
      · exact prime_oneHundredTwentyThreeDQ_11
      · exact prime_oneHundredTwentyThreeDQ_137
      · exact prime_oneHundredTwentyThreeDQ_631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 146441219) ^ 73220609 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (6 : ZMod 146441219) ^ 20920174 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (6 : ZMod 146441219) ^ 13312838 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (6 : ZMod 146441219) ^ 1068914 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (6 : ZMod 146441219) ^ 232078 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_164188469 : Nat.Prime 164188469 := by
  apply lucas_primality 164188469 (2 : ZMod 164188469)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (139, 1), (197, 1), (1499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (139, 1), (197, 1), (1499, 1)] : List FactorBlock).map factorBlockValue).prod) = 164188469 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_139
      · exact prime_oneHundredTwentyThreeDQ_197
      · exact prime_oneHundredTwentyThreeDQ_1499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 164188469) ^ 82094234 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 164188469) ^ 1181212 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 164188469) ^ 833444 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 164188469) ^ 109532 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_202041799 : Nat.Prime 202041799 := by
  apply lucas_primality 202041799 (3 : ZMod 202041799)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (23, 1), (29879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (23, 1), (29879, 1)] : List FactorBlock).map factorBlockValue).prod) = 202041799 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_7
      · exact prime_oneHundredTwentyThreeDQ_23
      · exact prime_oneHundredTwentyThreeDQ_29879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 202041799) ^ 101020899 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 202041799) ^ 67347266 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 202041799) ^ 28863114 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 202041799) ^ 8784426 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 202041799) ^ 6762 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_229043197 : Nat.Prime 229043197 := by
  apply lucas_primality 229043197 (2 : ZMod 229043197)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (6362311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (6362311, 1)] : List FactorBlock).map factorBlockValue).prod) = 229043197 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_6362311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 229043197) ^ 114521598 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 229043197) ^ 76347732 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 229043197) ^ 36 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_230949263 : Nat.Prime 230949263 := by
  apply lucas_primality 230949263 (5 : ZMod 230949263)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (115474631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (115474631, 1)] : List FactorBlock).map factorBlockValue).prod) = 230949263 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_115474631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 230949263) ^ 115474631 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 230949263) ^ 2 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_237754967 : Nat.Prime 237754967 := by
  apply lucas_primality 237754967 (5 : ZMod 237754967)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (197, 1), (491, 1), (1229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (197, 1), (491, 1), (1229, 1)] : List FactorBlock).map factorBlockValue).prod) = 237754967 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_197
      · exact prime_oneHundredTwentyThreeDQ_491
      · exact prime_oneHundredTwentyThreeDQ_1229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 237754967) ^ 118877483 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 237754967) ^ 1206878 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 237754967) ^ 484226 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 237754967) ^ 193454 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_247777217 : Nat.Prime 247777217 := by
  apply lucas_primality 247777217 (3 : ZMod 247777217)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (1109, 1), (3491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (1109, 1), (3491, 1)] : List FactorBlock).map factorBlockValue).prod) = 247777217 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_1109
      · exact prime_oneHundredTwentyThreeDQ_3491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 247777217) ^ 123888608 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 247777217) ^ 223424 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 247777217) ^ 70976 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_269549981 : Nat.Prime 269549981 := by
  apply lucas_primality 269549981 (2 : ZMod 269549981)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 3), (39293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 3), (39293, 1)] : List FactorBlock).map factorBlockValue).prod) = 269549981 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_5
      · exact prime_oneHundredTwentyThreeDQ_7
      · exact prime_oneHundredTwentyThreeDQ_39293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 269549981) ^ 134774990 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 269549981) ^ 53909996 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 269549981) ^ 38507140 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 269549981) ^ 6860 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_282275519 : Nat.Prime 282275519 := by
  apply lucas_primality 282275519 (11 : ZMod 282275519)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (20162537, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (20162537, 1)] : List FactorBlock).map factorBlockValue).prod) = 282275519 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_7
      · exact prime_oneHundredTwentyThreeDQ_20162537
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 282275519) ^ 141137759 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (11 : ZMod 282275519) ^ 40325074 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (11 : ZMod 282275519) ^ 14 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_287180123 : Nat.Prime 287180123 := by
  apply lucas_primality 287180123 (2 : ZMod 287180123)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (143590061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (143590061, 1)] : List FactorBlock).map factorBlockValue).prod) = 287180123 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_143590061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 287180123) ^ 143590061 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 287180123) ^ 2 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_287948027 : Nat.Prime 287948027 := by
  apply lucas_primality 287948027 (2 : ZMod 287948027)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (71, 1), (65413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (71, 1), (65413, 1)] : List FactorBlock).map factorBlockValue).prod) = 287948027 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_31
      · exact prime_oneHundredTwentyThreeDQ_71
      · exact prime_oneHundredTwentyThreeDQ_65413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 287948027) ^ 143974013 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 287948027) ^ 9288646 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 287948027) ^ 4055606 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 287948027) ^ 4402 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_292882439 : Nat.Prime 292882439 := by
  apply lucas_primality 292882439 (11 : ZMod 292882439)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (146441219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (146441219, 1)] : List FactorBlock).map factorBlockValue).prod) = 292882439 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_146441219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (11 : ZMod 292882439) ^ 146441219 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (11 : ZMod 292882439) ^ 2 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_314147747 : Nat.Prime 314147747 := by
  apply lucas_primality 314147747 (2 : ZMod 314147747)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (14279443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (14279443, 1)] : List FactorBlock).map factorBlockValue).prod) = 314147747 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_11
      · exact prime_oneHundredTwentyThreeDQ_14279443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 314147747) ^ 157073873 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 314147747) ^ 28558886 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 314147747) ^ 22 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_325921333 : Nat.Prime 325921333 := by
  apply lucas_primality 325921333 (5 : ZMod 325921333)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (233, 1), (10597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (233, 1), (10597, 1)] : List FactorBlock).map factorBlockValue).prod) = 325921333 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_11
      · exact prime_oneHundredTwentyThreeDQ_233
      · exact prime_oneHundredTwentyThreeDQ_10597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 325921333) ^ 162960666 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 325921333) ^ 108640444 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 325921333) ^ 29629212 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 325921333) ^ 1398804 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 325921333) ^ 30756 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_349340203 : Nat.Prime 349340203 := by
  apply lucas_primality 349340203 (7 : ZMod 349340203)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 5), (718807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 5), (718807, 1)] : List FactorBlock).map factorBlockValue).prod) = 349340203 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_718807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 349340203) ^ 174670101 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (7 : ZMod 349340203) ^ 116446734 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (7 : ZMod 349340203) ^ 486 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_353112493 : Nat.Prime 353112493 := by
  apply lucas_primality 353112493 (2 : ZMod 353112493)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (1548739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (1548739, 1)] : List FactorBlock).map factorBlockValue).prod) = 353112493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_19
      · exact prime_oneHundredTwentyThreeDQ_1548739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 353112493) ^ 176556246 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 353112493) ^ 117704164 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 353112493) ^ 18584868 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 353112493) ^ 228 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_506900707 : Nat.Prime 506900707 := by
  apply lucas_primality 506900707 (3 : ZMod 506900707)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (6498727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (6498727, 1)] : List FactorBlock).map factorBlockValue).prod) = 506900707 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_13
      · exact prime_oneHundredTwentyThreeDQ_6498727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 506900707) ^ 253450353 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 506900707) ^ 168966902 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 506900707) ^ 38992362 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 506900707) ^ 78 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_559185673 : Nat.Prime 559185673 := by
  apply lucas_primality 559185673 (5 : ZMod 559185673)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (421, 1), (55343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (421, 1), (55343, 1)] : List FactorBlock).map factorBlockValue).prod) = 559185673 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_421
      · exact prime_oneHundredTwentyThreeDQ_55343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 559185673) ^ 279592836 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 559185673) ^ 186395224 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 559185673) ^ 1328232 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 559185673) ^ 10104 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_587628869 : Nat.Prime 587628869 := by
  apply lucas_primality 587628869 (2 : ZMod 587628869)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (443, 1), (19507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (443, 1), (19507, 1)] : List FactorBlock).map factorBlockValue).prod) = 587628869 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_17
      · exact prime_oneHundredTwentyThreeDQ_443
      · exact prime_oneHundredTwentyThreeDQ_19507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 587628869) ^ 293814434 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 587628869) ^ 34566404 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 587628869) ^ 1326476 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 587628869) ^ 30124 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_598922059 : Nat.Prime 598922059 := by
  apply lucas_primality 598922059 (3 : ZMod 598922059)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (14260049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (14260049, 1)] : List FactorBlock).map factorBlockValue).prod) = 598922059 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_7
      · exact prime_oneHundredTwentyThreeDQ_14260049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 598922059) ^ 299461029 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 598922059) ^ 199640686 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 598922059) ^ 85560294 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 598922059) ^ 42 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_616050371 : Nat.Prime 616050371 := by
  apply lucas_primality 616050371 (2 : ZMod 616050371)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (37, 1), (211, 1), (607, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (37, 1), (211, 1), (607, 1)] : List FactorBlock).map factorBlockValue).prod) = 616050371 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_5
      · exact prime_oneHundredTwentyThreeDQ_13
      · exact prime_oneHundredTwentyThreeDQ_37
      · exact prime_oneHundredTwentyThreeDQ_211
      · exact prime_oneHundredTwentyThreeDQ_607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 616050371) ^ 308025185 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 616050371) ^ 123210074 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 616050371) ^ 47388490 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 616050371) ^ 16650010 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 616050371) ^ 2919670 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 616050371) ^ 1014910 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_636055141 : Nat.Prime 636055141 := by
  apply lucas_primality 636055141 (14 : ZMod 636055141)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (41, 1), (43, 1), (859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (41, 1), (43, 1), (859, 1)] : List FactorBlock).map factorBlockValue).prod) = 636055141 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_5
      · exact prime_oneHundredTwentyThreeDQ_7
      · exact prime_oneHundredTwentyThreeDQ_41
      · exact prime_oneHundredTwentyThreeDQ_43
      · exact prime_oneHundredTwentyThreeDQ_859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 636055141) ^ 318027570 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (14 : ZMod 636055141) ^ 212018380 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (14 : ZMod 636055141) ^ 127211028 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (14 : ZMod 636055141) ^ 90865020 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (14 : ZMod 636055141) ^ 15513540 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (14 : ZMod 636055141) ^ 14791980 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (14 : ZMod 636055141) ^ 740460 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_640433267 : Nat.Prime 640433267 := by
  apply lucas_primality 640433267 (2 : ZMod 640433267)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (19, 1), (61, 1), (25117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (19, 1), (61, 1), (25117, 1)] : List FactorBlock).map factorBlockValue).prod) = 640433267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_11
      · exact prime_oneHundredTwentyThreeDQ_19
      · exact prime_oneHundredTwentyThreeDQ_61
      · exact prime_oneHundredTwentyThreeDQ_25117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 640433267) ^ 320216633 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 58221206 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 33707014 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 10498906 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 25498 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_714027719 : Nat.Prime 714027719 := by
  apply lucas_primality 714027719 (11 : ZMod 714027719)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) = 714027719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_17203
      · exact prime_oneHundredTwentyThreeDQ_20753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 714027719) ^ 357013859 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 41506 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 34406 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_754354033 : Nat.Prime 754354033 := by
  apply lucas_primality 754354033 (5 : ZMod 754354033)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (29, 1), (89, 1), (6089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (29, 1), (89, 1), (6089, 1)] : List FactorBlock).map factorBlockValue).prod) = 754354033 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_29
      · exact prime_oneHundredTwentyThreeDQ_89
      · exact prime_oneHundredTwentyThreeDQ_6089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 754354033) ^ 377177016 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 754354033) ^ 251451344 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 754354033) ^ 26012208 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 754354033) ^ 8475888 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 754354033) ^ 123888 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_787110113 : Nat.Prime 787110113 := by
  apply lucas_primality 787110113 (3 : ZMod 787110113)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (19, 1), (29, 1), (44641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (19, 1), (29, 1), (44641, 1)] : List FactorBlock).map factorBlockValue).prod) = 787110113 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_19
      · exact prime_oneHundredTwentyThreeDQ_29
      · exact prime_oneHundredTwentyThreeDQ_44641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 787110113) ^ 393555056 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 787110113) ^ 41426848 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 787110113) ^ 27141728 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 787110113) ^ 17632 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_821234273 : Nat.Prime 821234273 := by
  apply lucas_primality 821234273 (3 : ZMod 821234273)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (887, 1), (28933, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (887, 1), (28933, 1)] : List FactorBlock).map factorBlockValue).prod) = 821234273 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_887
      · exact prime_oneHundredTwentyThreeDQ_28933
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 821234273) ^ 410617136 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 821234273) ^ 925856 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 821234273) ^ 28384 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_883092643 : Nat.Prime 883092643 := by
  apply lucas_primality 883092643 (2 : ZMod 883092643)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (8657771, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (8657771, 1)] : List FactorBlock).map factorBlockValue).prod) = 883092643 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_17
      · exact prime_oneHundredTwentyThreeDQ_8657771
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 883092643) ^ 441546321 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 883092643) ^ 294364214 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 883092643) ^ 51946626 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 883092643) ^ 102 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_1008719989 : Nat.Prime 1008719989 := by
  apply lucas_primality 1008719989 (2 : ZMod 1008719989)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (84059999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (84059999, 1)] : List FactorBlock).map factorBlockValue).prod) = 1008719989 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_84059999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1008719989) ^ 504359994 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1008719989) ^ 336239996 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1008719989) ^ 12 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_1123626241 : Nat.Prime 1123626241 := by
  apply lucas_primality 1123626241 (31 : ZMod 1123626241)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 2), (5, 1), (11, 1), (8867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 2), (5, 1), (11, 1), (8867, 1)] : List FactorBlock).map factorBlockValue).prod) = 1123626241 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_5
      · exact prime_oneHundredTwentyThreeDQ_11
      · exact prime_oneHundredTwentyThreeDQ_8867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (31 : ZMod 1123626241) ^ 561813120 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (31 : ZMod 1123626241) ^ 374542080 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (31 : ZMod 1123626241) ^ 224725248 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (31 : ZMod 1123626241) ^ 102147840 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (31 : ZMod 1123626241) ^ 126720 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_1173888763 : Nat.Prime 1173888763 := by
  apply lucas_primality 1173888763 (2 : ZMod 1173888763)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (97, 1), (1009, 1), (1999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (97, 1), (1009, 1), (1999, 1)] : List FactorBlock).map factorBlockValue).prod) = 1173888763 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_97
      · exact prime_oneHundredTwentyThreeDQ_1009
      · exact prime_oneHundredTwentyThreeDQ_1999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1173888763) ^ 586944381 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1173888763) ^ 391296254 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1173888763) ^ 12101946 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1173888763) ^ 1163418 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1173888763) ^ 587238 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_1176020819 : Nat.Prime 1176020819 := by
  apply lucas_primality 1176020819 (2 : ZMod 1176020819)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (29, 1), (683, 1), (4241, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (29, 1), (683, 1), (4241, 1)] : List FactorBlock).map factorBlockValue).prod) = 1176020819 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_7
      · exact prime_oneHundredTwentyThreeDQ_29
      · exact prime_oneHundredTwentyThreeDQ_683
      · exact prime_oneHundredTwentyThreeDQ_4241
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1176020819) ^ 588010409 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1176020819) ^ 168002974 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1176020819) ^ 40552442 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1176020819) ^ 1721846 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1176020819) ^ 277298 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_1309677463 : Nat.Prime 1309677463 := by
  apply lucas_primality 1309677463 (3 : ZMod 1309677463)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (72759859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (72759859, 1)] : List FactorBlock).map factorBlockValue).prod) = 1309677463 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_72759859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1309677463) ^ 654838731 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1309677463) ^ 436559154 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1309677463) ^ 18 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_1363823611 : Nat.Prime 1363823611 := by
  apply lucas_primality 1363823611 (10 : ZMod 1363823611)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (19, 1), (31, 1), (79, 1), (977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (19, 1), (31, 1), (79, 1), (977, 1)] : List FactorBlock).map factorBlockValue).prod) = 1363823611 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_5
      · exact prime_oneHundredTwentyThreeDQ_19
      · exact prime_oneHundredTwentyThreeDQ_31
      · exact prime_oneHundredTwentyThreeDQ_79
      · exact prime_oneHundredTwentyThreeDQ_977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 1363823611) ^ 681911805 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (10 : ZMod 1363823611) ^ 454607870 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (10 : ZMod 1363823611) ^ 272764722 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (10 : ZMod 1363823611) ^ 71780190 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (10 : ZMod 1363823611) ^ 43994310 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (10 : ZMod 1363823611) ^ 17263590 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (10 : ZMod 1363823611) ^ 1395930 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_1464341083 : Nat.Prime 1464341083 := by
  apply lucas_primality 1464341083 (3 : ZMod 1464341083)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (37, 1), (509, 1), (12959, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (37, 1), (509, 1), (12959, 1)] : List FactorBlock).map factorBlockValue).prod) = 1464341083 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_37
      · exact prime_oneHundredTwentyThreeDQ_509
      · exact prime_oneHundredTwentyThreeDQ_12959
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1464341083) ^ 732170541 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1464341083) ^ 488113694 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1464341083) ^ 39576786 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1464341083) ^ 2876898 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1464341083) ^ 112998 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_1505450053 : Nat.Prime 1505450053 := by
  apply lucas_primality 1505450053 (2 : ZMod 1505450053)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (971, 1), (43067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (971, 1), (43067, 1)] : List FactorBlock).map factorBlockValue).prod) = 1505450053 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_971
      · exact prime_oneHundredTwentyThreeDQ_43067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1505450053) ^ 752725026 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1505450053) ^ 501816684 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1505450053) ^ 1550412 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1505450053) ^ 34956 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_1597025669 : Nat.Prime 1597025669 := by
  apply lucas_primality 1597025669 (2 : ZMod 1597025669)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (67, 1), (851293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (67, 1), (851293, 1)] : List FactorBlock).map factorBlockValue).prod) = 1597025669 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_7
      · exact prime_oneHundredTwentyThreeDQ_67
      · exact prime_oneHundredTwentyThreeDQ_851293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1597025669) ^ 798512834 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1597025669) ^ 228146524 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1597025669) ^ 23836204 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1597025669) ^ 1876 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_1633056307 : Nat.Prime 1633056307 := by
  apply lucas_primality 1633056307 (11 : ZMod 1633056307)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (587, 1), (66239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (587, 1), (66239, 1)] : List FactorBlock).map factorBlockValue).prod) = 1633056307 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_7
      · exact prime_oneHundredTwentyThreeDQ_587
      · exact prime_oneHundredTwentyThreeDQ_66239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 1633056307) ^ 816528153 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (11 : ZMod 1633056307) ^ 544352102 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (11 : ZMod 1633056307) ^ 233293758 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (11 : ZMod 1633056307) ^ 2782038 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (11 : ZMod 1633056307) ^ 24654 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_1694450239 : Nat.Prime 1694450239 := by
  apply lucas_primality 1694450239 (6 : ZMod 1694450239)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (21723721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (21723721, 1)] : List FactorBlock).map factorBlockValue).prod) = 1694450239 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_13
      · exact prime_oneHundredTwentyThreeDQ_21723721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 1694450239) ^ 847225119 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (6 : ZMod 1694450239) ^ 564816746 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (6 : ZMod 1694450239) ^ 130342326 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (6 : ZMod 1694450239) ^ 78 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_1729267091 : Nat.Prime 1729267091 := by
  apply lucas_primality 1729267091 (2 : ZMod 1729267091)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (179, 1), (379, 1), (2549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (179, 1), (379, 1), (2549, 1)] : List FactorBlock).map factorBlockValue).prod) = 1729267091 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_5
      · exact prime_oneHundredTwentyThreeDQ_179
      · exact prime_oneHundredTwentyThreeDQ_379
      · exact prime_oneHundredTwentyThreeDQ_2549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1729267091) ^ 864633545 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1729267091) ^ 345853418 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1729267091) ^ 9660710 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1729267091) ^ 4562710 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1729267091) ^ 678410 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_1875866569 : Nat.Prime 1875866569 := by
  apply lucas_primality 1875866569 (13 : ZMod 1875866569)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (23, 1), (3398309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (23, 1), (3398309, 1)] : List FactorBlock).map factorBlockValue).prod) = 1875866569 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_23
      · exact prime_oneHundredTwentyThreeDQ_3398309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 1875866569) ^ 937933284 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (13 : ZMod 1875866569) ^ 625288856 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (13 : ZMod 1875866569) ^ 81559416 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (13 : ZMod 1875866569) ^ 552 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_2298442127 : Nat.Prime 2298442127 := by
  apply lucas_primality 2298442127 (5 : ZMod 2298442127)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (67601239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (67601239, 1)] : List FactorBlock).map factorBlockValue).prod) = 2298442127 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_17
      · exact prime_oneHundredTwentyThreeDQ_67601239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 2298442127) ^ 1149221063 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 2298442127) ^ 135202478 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 2298442127) ^ 34 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_2314470259 : Nat.Prime 2314470259 := by
  apply lucas_primality 2314470259 (14 : ZMod 2314470259)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7369, 1), (17449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7369, 1), (17449, 1)] : List FactorBlock).map factorBlockValue).prod) = 2314470259 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_7369
      · exact prime_oneHundredTwentyThreeDQ_17449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 2314470259) ^ 1157235129 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (14 : ZMod 2314470259) ^ 771490086 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (14 : ZMod 2314470259) ^ 314082 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (14 : ZMod 2314470259) ^ 132642 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_2352041639 : Nat.Prime 2352041639 := by
  apply lucas_primality 2352041639 (19 : ZMod 2352041639)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1176020819, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1176020819, 1)] : List FactorBlock).map factorBlockValue).prod) = 2352041639 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_1176020819
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (19 : ZMod 2352041639) ^ 1176020819 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (19 : ZMod 2352041639) ^ 2 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_2842734247 : Nat.Prime 2842734247 := by
  apply lucas_primality 2842734247 (3 : ZMod 2842734247)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (43071731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (43071731, 1)] : List FactorBlock).map factorBlockValue).prod) = 2842734247 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_11
      · exact prime_oneHundredTwentyThreeDQ_43071731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2842734247) ^ 1421367123 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 2842734247) ^ 947578082 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 2842734247) ^ 258430386 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 2842734247) ^ 66 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_2979022723 : Nat.Prime 2979022723 := by
  apply lucas_primality 2979022723 (2 : ZMod 2979022723)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (38192599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (38192599, 1)] : List FactorBlock).map factorBlockValue).prod) = 2979022723 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_13
      · exact prime_oneHundredTwentyThreeDQ_38192599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2979022723) ^ 1489511361 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2979022723) ^ 993007574 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2979022723) ^ 229155594 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2979022723) ^ 78 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_3017416133 : Nat.Prime 3017416133 := by
  apply lucas_primality 3017416133 (2 : ZMod 3017416133)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (754354033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (754354033, 1)] : List FactorBlock).map factorBlockValue).prod) = 3017416133 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_754354033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 3017416133) ^ 1508708066 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 3017416133) ^ 4 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_3194051339 : Nat.Prime 3194051339 := by
  apply lucas_primality 3194051339 (2 : ZMod 3194051339)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1597025669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1597025669, 1)] : List FactorBlock).map factorBlockValue).prod) = 3194051339 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_1597025669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 3194051339) ^ 1597025669 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 3194051339) ^ 2 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_3199253489 : Nat.Prime 3199253489 := by
  apply lucas_primality 3199253489 (3 : ZMod 3199253489)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (1489, 1), (134287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (1489, 1), (134287, 1)] : List FactorBlock).map factorBlockValue).prod) = 3199253489 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_1489
      · exact prime_oneHundredTwentyThreeDQ_134287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 3199253489) ^ 1599626744 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 3199253489) ^ 2148592 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 3199253489) ^ 23824 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_3351911569 : Nat.Prime 3351911569 := by
  apply lucas_primality 3351911569 (7 : ZMod 3351911569)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (69831491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (69831491, 1)] : List FactorBlock).map factorBlockValue).prod) = 3351911569 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_69831491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 3351911569) ^ 1675955784 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (7 : ZMod 3351911569) ^ 1117303856 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (7 : ZMod 3351911569) ^ 48 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_4032039997 : Nat.Prime 4032039997 := by
  apply lucas_primality 4032039997 (2 : ZMod 4032039997)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (43, 1), (2604677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (43, 1), (2604677, 1)] : List FactorBlock).map factorBlockValue).prod) = 4032039997 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_43
      · exact prime_oneHundredTwentyThreeDQ_2604677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4032039997) ^ 2016019998 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 4032039997) ^ 1344013332 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 4032039997) ^ 93768372 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 4032039997) ^ 1548 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_4165516939 : Nat.Prime 4165516939 := by
  apply lucas_primality 4165516939 (2 : ZMod 4165516939)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (59, 1), (1069727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (59, 1), (1069727, 1)] : List FactorBlock).map factorBlockValue).prod) = 4165516939 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_11
      · exact prime_oneHundredTwentyThreeDQ_59
      · exact prime_oneHundredTwentyThreeDQ_1069727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4165516939) ^ 2082758469 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 4165516939) ^ 1388505646 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 4165516939) ^ 378683358 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 4165516939) ^ 70601982 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 4165516939) ^ 3894 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_4839086167 : Nat.Prime 4839086167 := by
  apply lucas_primality 4839086167 (3 : ZMod 4839086167)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2927, 1), (275543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2927, 1), (275543, 1)] : List FactorBlock).map factorBlockValue).prod) = 4839086167 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_2927
      · exact prime_oneHundredTwentyThreeDQ_275543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4839086167) ^ 2419543083 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 4839086167) ^ 1613028722 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 4839086167) ^ 1653258 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 4839086167) ^ 17562 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_5187738011 : Nat.Prime 5187738011 := by
  apply lucas_primality 5187738011 (2 : ZMod 5187738011)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (13, 1), (43, 1), (233, 1), (569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (13, 1), (43, 1), (233, 1), (569, 1)] : List FactorBlock).map factorBlockValue).prod) = 5187738011 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_5
      · exact prime_oneHundredTwentyThreeDQ_7
      · exact prime_oneHundredTwentyThreeDQ_13
      · exact prime_oneHundredTwentyThreeDQ_43
      · exact prime_oneHundredTwentyThreeDQ_233
      · exact prime_oneHundredTwentyThreeDQ_569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5187738011) ^ 2593869005 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 5187738011) ^ 1037547602 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 5187738011) ^ 741105430 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 5187738011) ^ 399056770 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 5187738011) ^ 120645070 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 5187738011) ^ 22264970 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 5187738011) ^ 9117290 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_5517906211 : Nat.Prime 5517906211 := by
  apply lucas_primality 5517906211 (2 : ZMod 5517906211)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (61310069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (61310069, 1)] : List FactorBlock).map factorBlockValue).prod) = 5517906211 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_5
      · exact prime_oneHundredTwentyThreeDQ_61310069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5517906211) ^ 2758953105 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 5517906211) ^ 1839302070 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 5517906211) ^ 1103581242 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 5517906211) ^ 90 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_5858781301 : Nat.Prime 5858781301 := by
  apply lucas_primality 5858781301 (11 : ZMod 5858781301)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 2), (653, 1), (3323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 2), (653, 1), (3323, 1)] : List FactorBlock).map factorBlockValue).prod) = 5858781301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_5
      · exact prime_oneHundredTwentyThreeDQ_653
      · exact prime_oneHundredTwentyThreeDQ_3323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 5858781301) ^ 2929390650 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (11 : ZMod 5858781301) ^ 1952927100 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (11 : ZMod 5858781301) ^ 1171756260 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (11 : ZMod 5858781301) ^ 8972100 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (11 : ZMod 5858781301) ^ 1763100 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_5986848097 : Nat.Prime 5986848097 := by
  apply lucas_primality 5986848097 (5 : ZMod 5986848097)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (20787667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (20787667, 1)] : List FactorBlock).map factorBlockValue).prod) = 5986848097 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_20787667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 5986848097) ^ 2993424048 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 5986848097) ^ 1995616032 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 5986848097) ^ 288 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_6037638679 : Nat.Prime 6037638679 := by
  apply lucas_primality 6037638679 (3 : ZMod 6037638679)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) = 6037638679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_31
      · exact prime_oneHundredTwentyThreeDQ_10820141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6037638679) ^ 3018819339 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 2012546226 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 194762538 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 558 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_6042936539 : Nat.Prime 6042936539 := by
  apply lucas_primality 6042936539 (2 : ZMod 6042936539)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 2), (179, 1), (20071, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 2), (179, 1), (20071, 1)] : List FactorBlock).map factorBlockValue).prod) = 6042936539 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_29
      · exact prime_oneHundredTwentyThreeDQ_179
      · exact prime_oneHundredTwentyThreeDQ_20071
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 6042936539) ^ 3021468269 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 6042936539) ^ 208377122 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 6042936539) ^ 33759422 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 6042936539) ^ 301078 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_6707958641 : Nat.Prime 6707958641 := by
  apply lucas_primality 6707958641 (3 : ZMod 6707958641)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (83849483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (83849483, 1)] : List FactorBlock).map factorBlockValue).prod) = 6707958641 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_5
      · exact prime_oneHundredTwentyThreeDQ_83849483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 6707958641) ^ 3353979320 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 6707958641) ^ 1341591728 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 6707958641) ^ 80 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_6857736239 : Nat.Prime 6857736239 := by
  apply lucas_primality 6857736239 (7 : ZMod 6857736239)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (389, 1), (284341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (389, 1), (284341, 1)] : List FactorBlock).map factorBlockValue).prod) = 6857736239 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_31
      · exact prime_oneHundredTwentyThreeDQ_389
      · exact prime_oneHundredTwentyThreeDQ_284341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 6857736239) ^ 3428868119 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (7 : ZMod 6857736239) ^ 221217298 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (7 : ZMod 6857736239) ^ 17629142 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (7 : ZMod 6857736239) ^ 24118 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_7153087979 : Nat.Prime 7153087979 := by
  apply lucas_primality 7153087979 (2 : ZMod 7153087979)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (71, 1), (719, 1), (70061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (71, 1), (719, 1), (70061, 1)] : List FactorBlock).map factorBlockValue).prod) = 7153087979 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_71
      · exact prime_oneHundredTwentyThreeDQ_719
      · exact prime_oneHundredTwentyThreeDQ_70061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7153087979) ^ 3576543989 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 7153087979) ^ 100747718 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 7153087979) ^ 9948662 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 7153087979) ^ 102098 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_7224292637 : Nat.Prime 7224292637 := by
  apply lucas_primality 7224292637 (2 : ZMod 7224292637)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (164188469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (164188469, 1)] : List FactorBlock).map factorBlockValue).prod) = 7224292637 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_11
      · exact prime_oneHundredTwentyThreeDQ_164188469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 7224292637) ^ 3612146318 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 7224292637) ^ 656753876 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 7224292637) ^ 44 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_7466683199 : Nat.Prime 7466683199 := by
  apply lucas_primality 7466683199 (19 : ZMod 7466683199)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (287180123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (287180123, 1)] : List FactorBlock).map factorBlockValue).prod) = 7466683199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_13
      · exact prime_oneHundredTwentyThreeDQ_287180123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (19 : ZMod 7466683199) ^ 3733341599 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (19 : ZMod 7466683199) ^ 574360246 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (19 : ZMod 7466683199) ^ 26 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_10818185111 : Nat.Prime 10818185111 := by
  apply lucas_primality 10818185111 (23 : ZMod 10818185111)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (151, 1), (421433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (151, 1), (421433, 1)] : List FactorBlock).map factorBlockValue).prod) = 10818185111 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_5
      · exact prime_oneHundredTwentyThreeDQ_17
      · exact prime_oneHundredTwentyThreeDQ_151
      · exact prime_oneHundredTwentyThreeDQ_421433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 10818185111) ^ 5409092555 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (23 : ZMod 10818185111) ^ 2163637022 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (23 : ZMod 10818185111) ^ 636363830 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (23 : ZMod 10818185111) ^ 71643610 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (23 : ZMod 10818185111) ^ 25670 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_12122507941 : Nat.Prime 12122507941 := by
  apply lucas_primality 12122507941 (7 : ZMod 12122507941)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (202041799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (202041799, 1)] : List FactorBlock).map factorBlockValue).prod) = 12122507941 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_5
      · exact prime_oneHundredTwentyThreeDQ_202041799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 12122507941) ^ 6061253970 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (7 : ZMod 12122507941) ^ 4040835980 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (7 : ZMod 12122507941) ^ 2424501588 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (7 : ZMod 12122507941) ^ 60 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_12321007421 : Nat.Prime 12321007421 := by
  apply lucas_primality 12321007421 (2 : ZMod 12321007421)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (616050371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (616050371, 1)] : List FactorBlock).map factorBlockValue).prod) = 12321007421 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_5
      · exact prime_oneHundredTwentyThreeDQ_616050371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 12321007421) ^ 6160503710 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 12321007421) ^ 2464201484 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 12321007421) ^ 20 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_14399904703 : Nat.Prime 14399904703 := by
  apply lucas_primality 14399904703 (3 : ZMod 14399904703)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 1), (82758073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 1), (82758073, 1)] : List FactorBlock).map factorBlockValue).prod) = 14399904703 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_29
      · exact prime_oneHundredTwentyThreeDQ_82758073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 14399904703) ^ 7199952351 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 14399904703) ^ 4799968234 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 14399904703) ^ 496548438 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 14399904703) ^ 174 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_17867268467 : Nat.Prime 17867268467 := by
  apply lucas_primality 17867268467 (2 : ZMod 17867268467)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (137, 1), (263, 1), (247943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (137, 1), (263, 1), (247943, 1)] : List FactorBlock).map factorBlockValue).prod) = 17867268467 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_137
      · exact prime_oneHundredTwentyThreeDQ_263
      · exact prime_oneHundredTwentyThreeDQ_247943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 17867268467) ^ 8933634233 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 17867268467) ^ 130418018 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 17867268467) ^ 67936382 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 17867268467) ^ 72062 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_35511313909 : Nat.Prime 35511313909 := by
  apply lucas_primality 35511313909 (2 : ZMod 35511313909)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 2), (1439, 1), (41969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 2), (1439, 1), (41969, 1)] : List FactorBlock).map factorBlockValue).prod) = 35511313909 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_7
      · exact prime_oneHundredTwentyThreeDQ_1439
      · exact prime_oneHundredTwentyThreeDQ_41969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 35511313909) ^ 17755656954 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 35511313909) ^ 11837104636 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 35511313909) ^ 5073044844 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 35511313909) ^ 24677772 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 35511313909) ^ 846132 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_37982380157 : Nat.Prime 37982380157 := by
  apply lucas_primality 37982380157 (2 : ZMod 37982380157)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (41, 1), (47, 1), (307, 1), (2293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (41, 1), (47, 1), (307, 1), (2293, 1)] : List FactorBlock).map factorBlockValue).prod) = 37982380157 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_7
      · exact prime_oneHundredTwentyThreeDQ_41
      · exact prime_oneHundredTwentyThreeDQ_47
      · exact prime_oneHundredTwentyThreeDQ_307
      · exact prime_oneHundredTwentyThreeDQ_2293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 37982380157) ^ 18991190078 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 37982380157) ^ 5426054308 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 37982380157) ^ 926399516 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 37982380157) ^ 808135748 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 37982380157) ^ 123721108 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 37982380157) ^ 16564492 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_38627195153 : Nat.Prime 38627195153 := by
  apply lucas_primality 38627195153 (3 : ZMod 38627195153)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (13, 1), (43, 1), (47, 1), (13127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (13, 1), (43, 1), (47, 1), (13127, 1)] : List FactorBlock).map factorBlockValue).prod) = 38627195153 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_7
      · exact prime_oneHundredTwentyThreeDQ_13
      · exact prime_oneHundredTwentyThreeDQ_43
      · exact prime_oneHundredTwentyThreeDQ_47
      · exact prime_oneHundredTwentyThreeDQ_13127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 38627195153) ^ 19313597576 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 38627195153) ^ 5518170736 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 38627195153) ^ 2971322704 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 38627195153) ^ 898306864 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 38627195153) ^ 821855216 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 38627195153) ^ 2942576 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_39361763113 : Nat.Prime 39361763113 := by
  apply lucas_primality 39361763113 (5 : ZMod 39361763113)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 2), (33470887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 2), (33470887, 1)] : List FactorBlock).map factorBlockValue).prod) = 39361763113 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_7
      · exact prime_oneHundredTwentyThreeDQ_33470887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 39361763113) ^ 19680881556 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 39361763113) ^ 13120587704 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 39361763113) ^ 5623109016 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 39361763113) ^ 1176 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_46231962649 : Nat.Prime 46231962649 := by
  apply lucas_primality 46231962649 (7 : ZMod 46231962649)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (19, 1), (37, 1), (181, 1), (15139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (19, 1), (37, 1), (181, 1), (15139, 1)] : List FactorBlock).map factorBlockValue).prod) = 46231962649 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_19
      · exact prime_oneHundredTwentyThreeDQ_37
      · exact prime_oneHundredTwentyThreeDQ_181
      · exact prime_oneHundredTwentyThreeDQ_15139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 46231962649) ^ 23115981324 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (7 : ZMod 46231962649) ^ 15410654216 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (7 : ZMod 46231962649) ^ 2433261192 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (7 : ZMod 46231962649) ^ 1249512504 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (7 : ZMod 46231962649) ^ 255425208 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (7 : ZMod 46231962649) ^ 3053832 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_48311824511 : Nat.Prime 48311824511 := by
  apply lucas_primality 48311824511 (11 : ZMod 48311824511)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (113, 1), (2514931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (113, 1), (2514931, 1)] : List FactorBlock).map factorBlockValue).prod) = 48311824511 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_5
      · exact prime_oneHundredTwentyThreeDQ_17
      · exact prime_oneHundredTwentyThreeDQ_113
      · exact prime_oneHundredTwentyThreeDQ_2514931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 48311824511) ^ 24155912255 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (11 : ZMod 48311824511) ^ 9662364902 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (11 : ZMod 48311824511) ^ 2841872030 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (11 : ZMod 48311824511) ^ 427538270 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (11 : ZMod 48311824511) ^ 19210 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_48502013269 : Nat.Prime 48502013269 := by
  apply lucas_primality 48502013269 (2 : ZMod 48502013269)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (237754967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (237754967, 1)] : List FactorBlock).map factorBlockValue).prod) = 48502013269 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_17
      · exact prime_oneHundredTwentyThreeDQ_237754967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 48502013269) ^ 24251006634 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 48502013269) ^ 16167337756 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 48502013269) ^ 2853059604 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 48502013269) ^ 204 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_51054319639 : Nat.Prime 51054319639 := by
  apply lucas_primality 51054319639 (3 : ZMod 51054319639)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (431, 1), (509, 1), (1847, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (431, 1), (509, 1), (1847, 1)] : List FactorBlock).map factorBlockValue).prod) = 51054319639 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_7
      · exact prime_oneHundredTwentyThreeDQ_431
      · exact prime_oneHundredTwentyThreeDQ_509
      · exact prime_oneHundredTwentyThreeDQ_1847
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 51054319639) ^ 25527159819 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 51054319639) ^ 17018106546 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 51054319639) ^ 7293474234 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 51054319639) ^ 118455498 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 51054319639) ^ 100303182 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 51054319639) ^ 27641754 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_58886624501 : Nat.Prime 58886624501 := by
  apply lucas_primality 58886624501 (2 : ZMod 58886624501)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 3), (11, 1), (61, 1), (175519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 3), (11, 1), (61, 1), (175519, 1)] : List FactorBlock).map factorBlockValue).prod) = 58886624501 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_5
      · exact prime_oneHundredTwentyThreeDQ_11
      · exact prime_oneHundredTwentyThreeDQ_61
      · exact prime_oneHundredTwentyThreeDQ_175519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 58886624501) ^ 29443312250 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 58886624501) ^ 11777324900 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 58886624501) ^ 5353329500 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 58886624501) ^ 965354500 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 58886624501) ^ 335500 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_68237181317 : Nat.Prime 68237181317 := by
  apply lucas_primality 68237181317 (2 : ZMod 68237181317)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (4463, 1), (3822383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (4463, 1), (3822383, 1)] : List FactorBlock).map factorBlockValue).prod) = 68237181317 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_4463
      · exact prime_oneHundredTwentyThreeDQ_3822383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 68237181317) ^ 34118590658 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 68237181317) ^ 15289532 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 68237181317) ^ 17852 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_70379153699 : Nat.Prime 70379153699 := by
  apply lucas_primality 70379153699 (2 : ZMod 70379153699)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (61, 1), (82411187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (61, 1), (82411187, 1)] : List FactorBlock).map factorBlockValue).prod) = 70379153699 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_7
      · exact prime_oneHundredTwentyThreeDQ_61
      · exact prime_oneHundredTwentyThreeDQ_82411187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 70379153699) ^ 35189576849 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 70379153699) ^ 10054164814 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 70379153699) ^ 1153756618 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 70379153699) ^ 854 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_71644160257 : Nat.Prime 71644160257 := by
  apply lucas_primality 71644160257 (5 : ZMod 71644160257)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 1), (17, 1), (5487451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 1), (17, 1), (5487451, 1)] : List FactorBlock).map factorBlockValue).prod) = 71644160257 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_17
      · exact prime_oneHundredTwentyThreeDQ_5487451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 71644160257) ^ 35822080128 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 71644160257) ^ 23881386752 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 71644160257) ^ 4214362368 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 71644160257) ^ 13056 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_74309082979 : Nat.Prime 74309082979 := by
  apply lucas_primality 74309082979 (3 : ZMod 74309082979)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (37, 1), (41, 1), (379, 1), (1657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (37, 1), (41, 1), (379, 1), (1657, 1)] : List FactorBlock).map factorBlockValue).prod) = 74309082979 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_13
      · exact prime_oneHundredTwentyThreeDQ_37
      · exact prime_oneHundredTwentyThreeDQ_41
      · exact prime_oneHundredTwentyThreeDQ_379
      · exact prime_oneHundredTwentyThreeDQ_1657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 74309082979) ^ 37154541489 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 74309082979) ^ 24769694326 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 74309082979) ^ 5716083306 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 74309082979) ^ 2008353594 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 74309082979) ^ 1812416658 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 74309082979) ^ 196066182 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 74309082979) ^ 44845554 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_90457457939 : Nat.Prime 90457457939 := by
  apply lucas_primality 90457457939 (2 : ZMod 90457457939)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (147557, 1), (306517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (147557, 1), (306517, 1)] : List FactorBlock).map factorBlockValue).prod) = 90457457939 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_147557
      · exact prime_oneHundredTwentyThreeDQ_306517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 90457457939) ^ 45228728969 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 90457457939) ^ 613034 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 90457457939) ^ 295114 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_105432557977 : Nat.Prime 105432557977 := by
  apply lucas_primality 105432557977 (7 : ZMod 105432557977)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (1464341083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (1464341083, 1)] : List FactorBlock).map factorBlockValue).prod) = 105432557977 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_1464341083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 105432557977) ^ 52716278988 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (7 : ZMod 105432557977) ^ 35144185992 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (7 : ZMod 105432557977) ^ 72 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_107203610803 : Nat.Prime 107203610803 := by
  apply lucas_primality 107203610803 (2 : ZMod 107203610803)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17867268467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17867268467, 1)] : List FactorBlock).map factorBlockValue).prod) = 107203610803 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_17867268467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 107203610803) ^ 53601805401 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 107203610803) ^ 35734536934 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 107203610803) ^ 6 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_131895216811 : Nat.Prime 131895216811 := by
  apply lucas_primality 131895216811 (7 : ZMod 131895216811)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 5), (5, 1), (7, 1), (71, 1), (109211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 5), (5, 1), (7, 1), (71, 1), (109211, 1)] : List FactorBlock).map factorBlockValue).prod) = 131895216811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_5
      · exact prime_oneHundredTwentyThreeDQ_7
      · exact prime_oneHundredTwentyThreeDQ_71
      · exact prime_oneHundredTwentyThreeDQ_109211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 131895216811) ^ 65947608405 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (7 : ZMod 131895216811) ^ 43965072270 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (7 : ZMod 131895216811) ^ 26379043362 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (7 : ZMod 131895216811) ^ 18842173830 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (7 : ZMod 131895216811) ^ 1857679110 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (7 : ZMod 131895216811) ^ 1207710 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_134060634143 : Nat.Prime 134060634143 := by
  apply lucas_primality 134060634143 (5 : ZMod 134060634143)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (59, 1), (1327, 1), (856147, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (59, 1), (1327, 1), (856147, 1)] : List FactorBlock).map factorBlockValue).prod) = 134060634143 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_59
      · exact prime_oneHundredTwentyThreeDQ_1327
      · exact prime_oneHundredTwentyThreeDQ_856147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 134060634143) ^ 67030317071 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 134060634143) ^ 2272214138 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 134060634143) ^ 101025346 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 134060634143) ^ 156586 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_221064267763 : Nat.Prime 221064267763 := by
  apply lucas_primality 221064267763 (3 : ZMod 221064267763)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (4261, 1), (221713, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (4261, 1), (221713, 1)] : List FactorBlock).map factorBlockValue).prod) = 221064267763 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_13
      · exact prime_oneHundredTwentyThreeDQ_4261
      · exact prime_oneHundredTwentyThreeDQ_221713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 221064267763) ^ 110532133881 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 221064267763) ^ 73688089254 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 221064267763) ^ 17004943674 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 221064267763) ^ 51880842 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 221064267763) ^ 997074 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_221352255143 : Nat.Prime 221352255143 := by
  apply lucas_primality 221352255143 (5 : ZMod 221352255143)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (59, 1), (1875866569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (59, 1), (1875866569, 1)] : List FactorBlock).map factorBlockValue).prod) = 221352255143 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_59
      · exact prime_oneHundredTwentyThreeDQ_1875866569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 221352255143) ^ 110676127571 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 221352255143) ^ 3751733138 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 221352255143) ^ 118 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_243364641461 : Nat.Prime 243364641461 := by
  apply lucas_primality 243364641461 (2 : ZMod 243364641461)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (19, 1), (640433267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (19, 1), (640433267, 1)] : List FactorBlock).map factorBlockValue).prod) = 243364641461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_5
      · exact prime_oneHundredTwentyThreeDQ_19
      · exact prime_oneHundredTwentyThreeDQ_640433267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 243364641461) ^ 121682320730 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 243364641461) ^ 48672928292 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 243364641461) ^ 12808665340 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 243364641461) ^ 380 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_254092639391 : Nat.Prime 254092639391 := by
  apply lucas_primality 254092639391 (13 : ZMod 254092639391)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (19, 1), (47, 1), (28453823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (19, 1), (47, 1), (28453823, 1)] : List FactorBlock).map factorBlockValue).prod) = 254092639391 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_5
      · exact prime_oneHundredTwentyThreeDQ_19
      · exact prime_oneHundredTwentyThreeDQ_47
      · exact prime_oneHundredTwentyThreeDQ_28453823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 254092639391) ^ 127046319695 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (13 : ZMod 254092639391) ^ 50818527878 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (13 : ZMod 254092639391) ^ 13373296810 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (13 : ZMod 254092639391) ^ 5406226370 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (13 : ZMod 254092639391) ^ 8930 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_277740317081 : Nat.Prime 277740317081 := by
  apply lucas_primality 277740317081 (3 : ZMod 277740317081)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (23, 1), (89, 1), (3392041, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (23, 1), (89, 1), (3392041, 1)] : List FactorBlock).map factorBlockValue).prod) = 277740317081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_5
      · exact prime_oneHundredTwentyThreeDQ_23
      · exact prime_oneHundredTwentyThreeDQ_89
      · exact prime_oneHundredTwentyThreeDQ_3392041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 277740317081) ^ 138870158540 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 277740317081) ^ 55548063416 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 277740317081) ^ 12075665960 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 277740317081) ^ 3120677720 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 277740317081) ^ 81880 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_343811582143 : Nat.Prime 343811582143 := by
  apply lucas_primality 343811582143 (5 : ZMod 343811582143)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (29, 1), (282275519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (29, 1), (282275519, 1)] : List FactorBlock).map factorBlockValue).prod) = 343811582143 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_7
      · exact prime_oneHundredTwentyThreeDQ_29
      · exact prime_oneHundredTwentyThreeDQ_282275519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 343811582143) ^ 171905791071 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 343811582143) ^ 114603860714 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 343811582143) ^ 49115940306 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 343811582143) ^ 11855571798 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 343811582143) ^ 1218 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_345118424881 : Nat.Prime 345118424881 := by
  apply lucas_primality 345118424881 (7 : ZMod 345118424881)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (107, 1), (13439191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (107, 1), (13439191, 1)] : List FactorBlock).map factorBlockValue).prod) = 345118424881 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_5
      · exact prime_oneHundredTwentyThreeDQ_107
      · exact prime_oneHundredTwentyThreeDQ_13439191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 345118424881) ^ 172559212440 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (7 : ZMod 345118424881) ^ 115039474960 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (7 : ZMod 345118424881) ^ 69023684976 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (7 : ZMod 345118424881) ^ 3225405840 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (7 : ZMod 345118424881) ^ 25680 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_375436412387 : Nat.Prime 375436412387 := by
  apply lucas_primality 375436412387 (2 : ZMod 375436412387)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (104677, 1), (256187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (104677, 1), (256187, 1)] : List FactorBlock).map factorBlockValue).prod) = 375436412387 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_7
      · exact prime_oneHundredTwentyThreeDQ_104677
      · exact prime_oneHundredTwentyThreeDQ_256187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 375436412387) ^ 187718206193 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 375436412387) ^ 53633773198 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 375436412387) ^ 3586618 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 375436412387) ^ 1465478 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_498052330879 : Nat.Prime 498052330879 := by
  apply lucas_primality 498052330879 (3 : ZMod 498052330879)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (43, 1), (2281, 1), (49783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (43, 1), (2281, 1), (49783, 1)] : List FactorBlock).map factorBlockValue).prod) = 498052330879 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_17
      · exact prime_oneHundredTwentyThreeDQ_43
      · exact prime_oneHundredTwentyThreeDQ_2281
      · exact prime_oneHundredTwentyThreeDQ_49783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 498052330879) ^ 249026165439 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 498052330879) ^ 166017443626 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 498052330879) ^ 29297195934 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 498052330879) ^ 11582612346 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 498052330879) ^ 218348238 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 498052330879) ^ 10004466 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_698176681607 : Nat.Prime 698176681607 := by
  apply lucas_primality 698176681607 (5 : ZMod 698176681607)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (79, 1), (56263, 1), (78539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (79, 1), (56263, 1), (78539, 1)] : List FactorBlock).map factorBlockValue).prod) = 698176681607 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_79
      · exact prime_oneHundredTwentyThreeDQ_56263
      · exact prime_oneHundredTwentyThreeDQ_78539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 698176681607) ^ 349088340803 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 698176681607) ^ 8837679514 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 698176681607) ^ 12409162 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 698176681607) ^ 8889554 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_842955281741 : Nat.Prime 842955281741 := by
  apply lucas_primality 842955281741 (2 : ZMod 842955281741)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (11, 1), (13, 1), (19, 1), (89, 1), (174299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (11, 1), (13, 1), (19, 1), (89, 1), (174299, 1)] : List FactorBlock).map factorBlockValue).prod) = 842955281741 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_5
      · exact prime_oneHundredTwentyThreeDQ_11
      · exact prime_oneHundredTwentyThreeDQ_13
      · exact prime_oneHundredTwentyThreeDQ_19
      · exact prime_oneHundredTwentyThreeDQ_89
      · exact prime_oneHundredTwentyThreeDQ_174299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 842955281741) ^ 421477640870 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 842955281741) ^ 168591056348 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 842955281741) ^ 76632298340 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 842955281741) ^ 64842713980 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 842955281741) ^ 44366067460 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 842955281741) ^ 9471407660 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 842955281741) ^ 4836260 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_914480876299 : Nat.Prime 914480876299 := by
  apply lucas_primality 914480876299 (2 : ZMod 914480876299)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (173, 1), (5779, 1), (13859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (173, 1), (5779, 1), (13859, 1)] : List FactorBlock).map factorBlockValue).prod) = 914480876299 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_11
      · exact prime_oneHundredTwentyThreeDQ_173
      · exact prime_oneHundredTwentyThreeDQ_5779
      · exact prime_oneHundredTwentyThreeDQ_13859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 914480876299) ^ 457240438149 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 914480876299) ^ 304826958766 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 914480876299) ^ 83134625118 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 914480876299) ^ 5286016626 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 914480876299) ^ 158242062 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 914480876299) ^ 65984622 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_918977753503 : Nat.Prime 918977753503 := by
  apply lucas_primality 918977753503 (3 : ZMod 918977753503)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (51054319639, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (51054319639, 1)] : List FactorBlock).map factorBlockValue).prod) = 918977753503 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_51054319639
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 918977753503) ^ 459488876751 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 918977753503) ^ 306325917834 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 918977753503) ^ 18 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_955320538439 : Nat.Prime 955320538439 := by
  apply lucas_primality 955320538439 (7 : ZMod 955320538439)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (68237181317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (68237181317, 1)] : List FactorBlock).map factorBlockValue).prod) = 955320538439 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_7
      · exact prime_oneHundredTwentyThreeDQ_68237181317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 955320538439) ^ 477660269219 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (7 : ZMod 955320538439) ^ 136474362634 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (7 : ZMod 955320538439) ^ 14 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_959625519287 : Nat.Prime 959625519287 := by
  apply lucas_primality 959625519287 (7 : ZMod 959625519287)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (17, 1), (4032039997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (17, 1), (4032039997, 1)] : List FactorBlock).map factorBlockValue).prod) = 959625519287 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_7
      · exact prime_oneHundredTwentyThreeDQ_17
      · exact prime_oneHundredTwentyThreeDQ_4032039997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 959625519287) ^ 479812759643 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (7 : ZMod 959625519287) ^ 137089359898 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (7 : ZMod 959625519287) ^ 56448559958 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (7 : ZMod 959625519287) ^ 238 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_988200538751 : Nat.Prime 988200538751 := by
  apply lucas_primality 988200538751 (23 : ZMod 988200538751)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 4), (101, 1), (7827331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 4), (101, 1), (7827331, 1)] : List FactorBlock).map factorBlockValue).prod) = 988200538751 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_5
      · exact prime_oneHundredTwentyThreeDQ_101
      · exact prime_oneHundredTwentyThreeDQ_7827331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (23 : ZMod 988200538751) ^ 494100269375 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (23 : ZMod 988200538751) ^ 197640107750 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (23 : ZMod 988200538751) ^ 9784163750 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (23 : ZMod 988200538751) ^ 126250 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_1022826169121 : Nat.Prime 1022826169121 := by
  apply lucas_primality 1022826169121 (3 : ZMod 1022826169121)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (7, 1), (2621, 1), (348431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (7, 1), (2621, 1), (348431, 1)] : List FactorBlock).map factorBlockValue).prod) = 1022826169121 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_5
      · exact prime_oneHundredTwentyThreeDQ_7
      · exact prime_oneHundredTwentyThreeDQ_2621
      · exact prime_oneHundredTwentyThreeDQ_348431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1022826169121) ^ 511413084560 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1022826169121) ^ 204565233824 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1022826169121) ^ 146118024160 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1022826169121) ^ 390242720 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1022826169121) ^ 2935520 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_1062117475429 : Nat.Prime 1062117475429 := by
  apply lucas_primality 1062117475429 (2 : ZMod 1062117475429)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (29, 1), (131, 1), (2909, 1), (8009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (29, 1), (131, 1), (2909, 1), (8009, 1)] : List FactorBlock).map factorBlockValue).prod) = 1062117475429 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_29
      · exact prime_oneHundredTwentyThreeDQ_131
      · exact prime_oneHundredTwentyThreeDQ_2909
      · exact prime_oneHundredTwentyThreeDQ_8009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1062117475429) ^ 531058737714 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1062117475429) ^ 354039158476 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1062117475429) ^ 36624740532 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1062117475429) ^ 8107766988 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1062117475429) ^ 365114292 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1062117475429) ^ 132615492 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_1199515371611 : Nat.Prime 1199515371611 := by
  apply lucas_primality 1199515371611 (2 : ZMod 1199515371611)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (139, 1), (431, 1), (2002229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (139, 1), (431, 1), (2002229, 1)] : List FactorBlock).map factorBlockValue).prod) = 1199515371611 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_5
      · exact prime_oneHundredTwentyThreeDQ_139
      · exact prime_oneHundredTwentyThreeDQ_431
      · exact prime_oneHundredTwentyThreeDQ_2002229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1199515371611) ^ 599757685805 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1199515371611) ^ 239903074322 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1199515371611) ^ 8629606990 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1199515371611) ^ 2783098310 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1199515371611) ^ 599090 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_1210281000961 : Nat.Prime 1210281000961 := by
  apply lucas_primality 1210281000961 (29 : ZMod 1210281000961)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 15), (3, 1), (5, 1), (1381, 1), (1783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 15), (3, 1), (5, 1), (1381, 1), (1783, 1)] : List FactorBlock).map factorBlockValue).prod) = 1210281000961 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_5
      · exact prime_oneHundredTwentyThreeDQ_1381
      · exact prime_oneHundredTwentyThreeDQ_1783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (29 : ZMod 1210281000961) ^ 605140500480 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (29 : ZMod 1210281000961) ^ 403427000320 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (29 : ZMod 1210281000961) ^ 242056200192 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (29 : ZMod 1210281000961) ^ 876380160 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (29 : ZMod 1210281000961) ^ 678789120 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_1403736441413 : Nat.Prime 1403736441413 := by
  apply lucas_primality 1403736441413 (2 : ZMod 1403736441413)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (47, 1), (7466683199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (47, 1), (7466683199, 1)] : List FactorBlock).map factorBlockValue).prod) = 1403736441413 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_47
      · exact prime_oneHundredTwentyThreeDQ_7466683199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1403736441413) ^ 701868220706 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1403736441413) ^ 29866732796 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1403736441413) ^ 188 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_1418133949927 : Nat.Prime 1418133949927 := by
  apply lucas_primality 1418133949927 (3 : ZMod 1418133949927)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (157, 1), (1505450053, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (157, 1), (1505450053, 1)] : List FactorBlock).map factorBlockValue).prod) = 1418133949927 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_157
      · exact prime_oneHundredTwentyThreeDQ_1505450053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1418133949927) ^ 709066974963 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1418133949927) ^ 472711316642 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1418133949927) ^ 9032700318 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1418133949927) ^ 942 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_1430499735023 : Nat.Prime 1430499735023 := by
  apply lucas_primality 1430499735023 (5 : ZMod 1430499735023)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (163, 1), (230949263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (163, 1), (230949263, 1)] : List FactorBlock).map factorBlockValue).prod) = 1430499735023 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_19
      · exact prime_oneHundredTwentyThreeDQ_163
      · exact prime_oneHundredTwentyThreeDQ_230949263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1430499735023) ^ 715249867511 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 1430499735023) ^ 75289459738 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 1430499735023) ^ 8776071994 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 1430499735023) ^ 6194 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_1678875508927 : Nat.Prime 1678875508927 := by
  apply lucas_primality 1678875508927 (3 : ZMod 1678875508927)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (11, 2), (17, 1), (521, 1), (12433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (11, 2), (17, 1), (521, 1), (12433, 1)] : List FactorBlock).map factorBlockValue).prod) = 1678875508927 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_7
      · exact prime_oneHundredTwentyThreeDQ_11
      · exact prime_oneHundredTwentyThreeDQ_17
      · exact prime_oneHundredTwentyThreeDQ_521
      · exact prime_oneHundredTwentyThreeDQ_12433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1678875508927) ^ 839437754463 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1678875508927) ^ 559625169642 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1678875508927) ^ 239839358418 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1678875508927) ^ 152625046266 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1678875508927) ^ 98757382878 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1678875508927) ^ 3222409806 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1678875508927) ^ 135033822 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_2046811681877 : Nat.Prime 2046811681877 := by
  apply lucas_primality 2046811681877 (2 : ZMod 2046811681877)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (39361763113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (39361763113, 1)] : List FactorBlock).map factorBlockValue).prod) = 2046811681877 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_13
      · exact prime_oneHundredTwentyThreeDQ_39361763113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2046811681877) ^ 1023405840938 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2046811681877) ^ 157447052452 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2046811681877) ^ 52 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_2140239695533 : Nat.Prime 2140239695533 := by
  apply lucas_primality 2140239695533 (5 : ZMod 2140239695533)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (281, 1), (797, 1), (796373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (281, 1), (797, 1), (796373, 1)] : List FactorBlock).map factorBlockValue).prod) = 2140239695533 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_281
      · exact prime_oneHundredTwentyThreeDQ_797
      · exact prime_oneHundredTwentyThreeDQ_796373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2140239695533) ^ 1070119847766 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 2140239695533) ^ 713413231844 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 2140239695533) ^ 7616511372 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 2140239695533) ^ 2685369756 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 2140239695533) ^ 2687484 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_2426519858207 : Nat.Prime 2426519858207 := by
  apply lucas_primality 2426519858207 (5 : ZMod 2426519858207)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (239, 1), (21817, 1), (232681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (239, 1), (21817, 1), (232681, 1)] : List FactorBlock).map factorBlockValue).prod) = 2426519858207 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_239
      · exact prime_oneHundredTwentyThreeDQ_21817
      · exact prime_oneHundredTwentyThreeDQ_232681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2426519858207) ^ 1213259929103 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 2426519858207) ^ 10152802754 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 2426519858207) ^ 111221518 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 2426519858207) ^ 10428526 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_2587847008057 : Nat.Prime 2587847008057 := by
  apply lucas_primality 2587847008057 (5 : ZMod 2587847008057)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (79, 1), (151, 1), (9039061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (79, 1), (151, 1), (9039061, 1)] : List FactorBlock).map factorBlockValue).prod) = 2587847008057 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_79
      · exact prime_oneHundredTwentyThreeDQ_151
      · exact prime_oneHundredTwentyThreeDQ_9039061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2587847008057) ^ 1293923504028 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 2587847008057) ^ 862615669352 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 2587847008057) ^ 32757557064 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 2587847008057) ^ 17138059656 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 2587847008057) ^ 286296 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_2995333119683 : Nat.Prime 2995333119683 := by
  apply lucas_primality 2995333119683 (2 : ZMod 2995333119683)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (48311824511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (48311824511, 1)] : List FactorBlock).map factorBlockValue).prod) = 2995333119683 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_31
      · exact prime_oneHundredTwentyThreeDQ_48311824511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2995333119683) ^ 1497666559841 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2995333119683) ^ 96623649022 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2995333119683) ^ 62 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_3945795860701 : Nat.Prime 3945795860701 := by
  apply lucas_primality 3945795860701 (11 : ZMod 3945795860701)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 2), (929, 1), (4719287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 2), (929, 1), (4719287, 1)] : List FactorBlock).map factorBlockValue).prod) = 3945795860701 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_5
      · exact prime_oneHundredTwentyThreeDQ_929
      · exact prime_oneHundredTwentyThreeDQ_4719287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 3945795860701) ^ 1972897930350 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (11 : ZMod 3945795860701) ^ 1315265286900 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (11 : ZMod 3945795860701) ^ 789159172140 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (11 : ZMod 3945795860701) ^ 4247358300 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (11 : ZMod 3945795860701) ^ 836100 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_4012688116243 : Nat.Prime 4012688116243 := by
  apply lucas_primality 4012688116243 (2 : ZMod 4012688116243)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (17, 1), (1008719989, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (17, 1), (1008719989, 1)] : List FactorBlock).map factorBlockValue).prod) = 4012688116243 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_13
      · exact prime_oneHundredTwentyThreeDQ_17
      · exact prime_oneHundredTwentyThreeDQ_1008719989
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4012688116243) ^ 2006344058121 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 4012688116243) ^ 1337562705414 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 4012688116243) ^ 308668316634 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 4012688116243) ^ 236040477426 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 4012688116243) ^ 3978 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_4628130868657 : Nat.Prime 4628130868657 := by
  apply lucas_primality 4628130868657 (11 : ZMod 4628130868657)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (163, 1), (239, 1), (825007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (163, 1), (239, 1), (825007, 1)] : List FactorBlock).map factorBlockValue).prod) = 4628130868657 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_163
      · exact prime_oneHundredTwentyThreeDQ_239
      · exact prime_oneHundredTwentyThreeDQ_825007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 4628130868657) ^ 2314065434328 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (11 : ZMod 4628130868657) ^ 1542710289552 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (11 : ZMod 4628130868657) ^ 28393440912 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (11 : ZMod 4628130868657) ^ 19364564304 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (11 : ZMod 4628130868657) ^ 5609808 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_4944391472773 : Nat.Prime 4944391472773 := by
  apply lucas_primality 4944391472773 (2 : ZMod 4944391472773)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (43, 1), (3194051339, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (43, 1), (3194051339, 1)] : List FactorBlock).map factorBlockValue).prod) = 4944391472773 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_43
      · exact prime_oneHundredTwentyThreeDQ_3194051339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4944391472773) ^ 2472195736386 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 4944391472773) ^ 1648130490924 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 4944391472773) ^ 114985848204 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 4944391472773) ^ 1548 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_6100779900937 : Nat.Prime 6100779900937 := by
  apply lucas_primality 6100779900937 (5 : ZMod 6100779900937)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 2), (5187738011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 2), (5187738011, 1)] : List FactorBlock).map factorBlockValue).prod) = 6100779900937 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_7
      · exact prime_oneHundredTwentyThreeDQ_5187738011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 6100779900937) ^ 3050389950468 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 6100779900937) ^ 2033593300312 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 6100779900937) ^ 871539985848 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 6100779900937) ^ 1176 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_6115088362667 : Nat.Prime 6115088362667 := by
  apply lucas_primality 6115088362667 (2 : ZMod 6115088362667)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (105432557977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (105432557977, 1)] : List FactorBlock).map factorBlockValue).prod) = 6115088362667 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_29
      · exact prime_oneHundredTwentyThreeDQ_105432557977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 6115088362667) ^ 3057544181333 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 6115088362667) ^ 210865115954 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 6115088362667) ^ 58 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_12395726288009 : Nat.Prime 12395726288009 := by
  apply lucas_primality 12395726288009 (3 : ZMod 12395726288009)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (221352255143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (221352255143, 1)] : List FactorBlock).map factorBlockValue).prod) = 12395726288009 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_7
      · exact prime_oneHundredTwentyThreeDQ_221352255143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 12395726288009) ^ 6197863144004 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 12395726288009) ^ 1770818041144 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 12395726288009) ^ 56 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_14857333202917 : Nat.Prime 14857333202917 := by
  apply lucas_primality 14857333202917 (6 : ZMod 14857333202917)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (43, 1), (3199253489, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (43, 1), (3199253489, 1)] : List FactorBlock).map factorBlockValue).prod) = 14857333202917 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_43
      · exact prime_oneHundredTwentyThreeDQ_3199253489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 14857333202917) ^ 7428666601458 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (6 : ZMod 14857333202917) ^ 4952444400972 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (6 : ZMod 14857333202917) ^ 345519376812 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (6 : ZMod 14857333202917) ^ 4644 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_15492669108097 : Nat.Prime 15492669108097 := by
  apply lucas_primality 15492669108097 (7 : ZMod 15492669108097)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (31, 1), (227, 1), (5733337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (31, 1), (227, 1), (5733337, 1)] : List FactorBlock).map factorBlockValue).prod) = 15492669108097 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_31
      · exact prime_oneHundredTwentyThreeDQ_227
      · exact prime_oneHundredTwentyThreeDQ_5733337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 15492669108097) ^ 7746334554048 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (7 : ZMod 15492669108097) ^ 5164223036032 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (7 : ZMod 15492669108097) ^ 499763519616 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (7 : ZMod 15492669108097) ^ 68249643648 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (7 : ZMod 15492669108097) ^ 2702208 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_16223421964261 : Nat.Prime 16223421964261 := by
  apply lucas_primality 16223421964261 (2 : ZMod 16223421964261)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (38627195153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (38627195153, 1)] : List FactorBlock).map factorBlockValue).prod) = 16223421964261 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_5
      · exact prime_oneHundredTwentyThreeDQ_7
      · exact prime_oneHundredTwentyThreeDQ_38627195153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 16223421964261) ^ 8111710982130 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 16223421964261) ^ 5407807321420 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 16223421964261) ^ 3244684392852 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 16223421964261) ^ 2317631709180 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 16223421964261) ^ 420 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_19461898163093 : Nat.Prime 19461898163093 := by
  apply lucas_primality 19461898163093 (2 : ZMod 19461898163093)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (11, 1), (113, 1), (559185673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (11, 1), (113, 1), (559185673, 1)] : List FactorBlock).map factorBlockValue).prod) = 19461898163093 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_7
      · exact prime_oneHundredTwentyThreeDQ_11
      · exact prime_oneHundredTwentyThreeDQ_113
      · exact prime_oneHundredTwentyThreeDQ_559185673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 19461898163093) ^ 9730949081546 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 19461898163093) ^ 2780271166156 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 19461898163093) ^ 1769263469372 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 19461898163093) ^ 172229187284 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 19461898163093) ^ 34804 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_19764010775021 : Nat.Prime 19764010775021 := by
  apply lucas_primality 19764010775021 (10 : ZMod 19764010775021)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (988200538751, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (988200538751, 1)] : List FactorBlock).map factorBlockValue).prod) = 19764010775021 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_5
      · exact prime_oneHundredTwentyThreeDQ_988200538751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 19764010775021) ^ 9882005387510 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (10 : ZMod 19764010775021) ^ 3952802155004 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (10 : ZMod 19764010775021) ^ 20 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_24505700548913 : Nat.Prime 24505700548913 := by
  apply lucas_primality 24505700548913 (3 : ZMod 24505700548913)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (11, 1), (153281, 1), (908377, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (11, 1), (153281, 1), (908377, 1)] : List FactorBlock).map factorBlockValue).prod) = 24505700548913 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_11
      · exact prime_oneHundredTwentyThreeDQ_153281
      · exact prime_oneHundredTwentyThreeDQ_908377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 24505700548913) ^ 12252850274456 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 24505700548913) ^ 2227790958992 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 24505700548913) ^ 159874352 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 24505700548913) ^ 26977456 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_26533200616991 : Nat.Prime 26533200616991 := by
  apply lucas_primality 26533200616991 (23 : ZMod 26533200616991)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (23, 1), (29, 1), (2339, 1), (1700723, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (23, 1), (29, 1), (2339, 1), (1700723, 1)] : List FactorBlock).map factorBlockValue).prod) = 26533200616991 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_5
      · exact prime_oneHundredTwentyThreeDQ_23
      · exact prime_oneHundredTwentyThreeDQ_29
      · exact prime_oneHundredTwentyThreeDQ_2339
      · exact prime_oneHundredTwentyThreeDQ_1700723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 26533200616991) ^ 13266600308495 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (23 : ZMod 26533200616991) ^ 5306640123398 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (23 : ZMod 26533200616991) ^ 1153617418130 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (23 : ZMod 26533200616991) ^ 914937952310 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (23 : ZMod 26533200616991) ^ 11343822410 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (23 : ZMod 26533200616991) ^ 15601130 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_36842610273787 : Nat.Prime 36842610273787 := by
  apply lucas_primality 36842610273787 (2 : ZMod 36842610273787)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (2046811681877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (2046811681877, 1)] : List FactorBlock).map factorBlockValue).prod) = 36842610273787 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_2046811681877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 36842610273787) ^ 18421305136893 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 36842610273787) ^ 12280870091262 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 36842610273787) ^ 18 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_42563046765511 : Nat.Prime 42563046765511 := by
  apply lucas_primality 42563046765511 (3 : ZMod 42563046765511)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (233759, 1), (2023121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (233759, 1), (2023121, 1)] : List FactorBlock).map factorBlockValue).prod) = 42563046765511 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_5
      · exact prime_oneHundredTwentyThreeDQ_233759
      · exact prime_oneHundredTwentyThreeDQ_2023121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 42563046765511) ^ 21281523382755 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 42563046765511) ^ 14187682255170 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 42563046765511) ^ 8512609353102 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 42563046765511) ^ 182080890 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 42563046765511) ^ 21038310 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_44840525001631 : Nat.Prime 44840525001631 := by
  apply lucas_primality 44840525001631 (3 : ZMod 44840525001631)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (59779, 1), (25003499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (59779, 1), (25003499, 1)] : List FactorBlock).map factorBlockValue).prod) = 44840525001631 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_5
      · exact prime_oneHundredTwentyThreeDQ_59779
      · exact prime_oneHundredTwentyThreeDQ_25003499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 44840525001631) ^ 22420262500815 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 44840525001631) ^ 14946841667210 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 44840525001631) ^ 8968105000326 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 44840525001631) ^ 750104970 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 44840525001631) ^ 1793370 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_45752552594669 : Nat.Prime 45752552594669 := by
  apply lucas_primality 45752552594669 (2 : ZMod 45752552594669)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (47, 1), (243364641461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (47, 1), (243364641461, 1)] : List FactorBlock).map factorBlockValue).prod) = 45752552594669 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_47
      · exact prime_oneHundredTwentyThreeDQ_243364641461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 45752552594669) ^ 22876276297334 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 45752552594669) ^ 973458565844 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 45752552594669) ^ 188 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_47339388206371 : Nat.Prime 47339388206371 := by
  apply lucas_primality 47339388206371 (3 : ZMod 47339388206371)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (13, 1), (13229, 1), (1019503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (13, 1), (13229, 1), (1019503, 1)] : List FactorBlock).map factorBlockValue).prod) = 47339388206371 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_5
      · exact prime_oneHundredTwentyThreeDQ_13
      · exact prime_oneHundredTwentyThreeDQ_13229
      · exact prime_oneHundredTwentyThreeDQ_1019503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 47339388206371) ^ 23669694103185 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 47339388206371) ^ 15779796068790 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 47339388206371) ^ 9467877641274 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 47339388206371) ^ 3641491400490 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 47339388206371) ^ 3578455530 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 47339388206371) ^ 46433790 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_48920706901337 : Nat.Prime 48920706901337 := by
  apply lucas_primality 48920706901337 (3 : ZMod 48920706901337)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (6115088362667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (6115088362667, 1)] : List FactorBlock).map factorBlockValue).prod) = 48920706901337 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_6115088362667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 48920706901337) ^ 24460353450668 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 48920706901337) ^ 8 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_53066401233983 : Nat.Prime 53066401233983 := by
  apply lucas_primality 53066401233983 (5 : ZMod 53066401233983)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (26533200616991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (26533200616991, 1)] : List FactorBlock).map factorBlockValue).prod) = 53066401233983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_26533200616991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 53066401233983) ^ 26533200616991 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 53066401233983) ^ 2 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_60043194618203 : Nat.Prime 60043194618203 := by
  apply lucas_primality 60043194618203 (2 : ZMod 60043194618203)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 1), (698176681607, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 1), (698176681607, 1)] : List FactorBlock).map factorBlockValue).prod) = 60043194618203 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_43
      · exact prime_oneHundredTwentyThreeDQ_698176681607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 60043194618203) ^ 30021597309101 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 60043194618203) ^ 1396353363214 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 60043194618203) ^ 86 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_66013739715089 : Nat.Prime 66013739715089 := by
  apply lucas_primality 66013739715089 (3 : ZMod 66013739715089)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (11, 1), (20183, 1), (18583861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (11, 1), (20183, 1), (18583861, 1)] : List FactorBlock).map factorBlockValue).prod) = 66013739715089 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_11
      · exact prime_oneHundredTwentyThreeDQ_20183
      · exact prime_oneHundredTwentyThreeDQ_18583861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 66013739715089) ^ 33006869857544 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 66013739715089) ^ 6001249065008 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 66013739715089) ^ 3270759536 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 66013739715089) ^ 3552208 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_69929752389041 : Nat.Prime 69929752389041 := by
  apply lucas_primality 69929752389041 (3 : ZMod 69929752389041)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (179, 1), (12613, 1), (387169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (179, 1), (12613, 1), (387169, 1)] : List FactorBlock).map factorBlockValue).prod) = 69929752389041 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_5
      · exact prime_oneHundredTwentyThreeDQ_179
      · exact prime_oneHundredTwentyThreeDQ_12613
      · exact prime_oneHundredTwentyThreeDQ_387169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 69929752389041) ^ 34964876194520 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 69929752389041) ^ 13985950477808 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 69929752389041) ^ 390669007760 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 69929752389041) ^ 5544260080 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 69929752389041) ^ 180618160 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_74689946986103 : Nat.Prime 74689946986103 := by
  apply lucas_primality 74689946986103 (5 : ZMod 74689946986103)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (433, 1), (12321007421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (433, 1), (12321007421, 1)] : List FactorBlock).map factorBlockValue).prod) = 74689946986103 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_7
      · exact prime_oneHundredTwentyThreeDQ_433
      · exact prime_oneHundredTwentyThreeDQ_12321007421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 74689946986103) ^ 37344973493051 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 74689946986103) ^ 10669992426586 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 74689946986103) ^ 172494103894 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 74689946986103) ^ 6062 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_81270296932081 : Nat.Prime 81270296932081 := by
  apply lucas_primality 81270296932081 (14 : ZMod 81270296932081)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (23, 1), (31, 1), (199, 1), (2386591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (23, 1), (31, 1), (199, 1), (2386591, 1)] : List FactorBlock).map factorBlockValue).prod) = 81270296932081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_5
      · exact prime_oneHundredTwentyThreeDQ_23
      · exact prime_oneHundredTwentyThreeDQ_31
      · exact prime_oneHundredTwentyThreeDQ_199
      · exact prime_oneHundredTwentyThreeDQ_2386591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 81270296932081) ^ 40635148466040 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (14 : ZMod 81270296932081) ^ 27090098977360 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (14 : ZMod 81270296932081) ^ 16254059386416 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (14 : ZMod 81270296932081) ^ 3533491170960 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (14 : ZMod 81270296932081) ^ 2621622481680 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (14 : ZMod 81270296932081) ^ 408393451920 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (14 : ZMod 81270296932081) ^ 34052880 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_105464035294687 : Nat.Prime 105464035294687 := by
  apply lucas_primality 105464035294687 (3 : ZMod 105464035294687)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (149, 1), (2657, 1), (14799739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (149, 1), (2657, 1), (14799739, 1)] : List FactorBlock).map factorBlockValue).prod) = 105464035294687 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_149
      · exact prime_oneHundredTwentyThreeDQ_2657
      · exact prime_oneHundredTwentyThreeDQ_14799739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 105464035294687) ^ 52732017647343 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 105464035294687) ^ 35154678431562 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 105464035294687) ^ 707812317414 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 105464035294687) ^ 39692899998 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 105464035294687) ^ 7126074 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_108159489589871 : Nat.Prime 108159489589871 := by
  apply lucas_primality 108159489589871 (11 : ZMod 108159489589871)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (223, 1), (48502013269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (223, 1), (48502013269, 1)] : List FactorBlock).map factorBlockValue).prod) = 108159489589871 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_5
      · exact prime_oneHundredTwentyThreeDQ_223
      · exact prime_oneHundredTwentyThreeDQ_48502013269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 108159489589871) ^ 54079744794935 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (11 : ZMod 108159489589871) ^ 21631897917974 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (11 : ZMod 108159489589871) ^ 485020132690 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (11 : ZMod 108159489589871) ^ 2230 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_109001339774377 : Nat.Prime 109001339774377 := by
  apply lucas_primality 109001339774377 (5 : ZMod 109001339774377)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (19, 1), (47, 1), (61, 1), (11910809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (19, 1), (47, 1), (61, 1), (11910809, 1)] : List FactorBlock).map factorBlockValue).prod) = 109001339774377 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_7
      · exact prime_oneHundredTwentyThreeDQ_19
      · exact prime_oneHundredTwentyThreeDQ_47
      · exact prime_oneHundredTwentyThreeDQ_61
      · exact prime_oneHundredTwentyThreeDQ_11910809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 109001339774377) ^ 54500669887188 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 109001339774377) ^ 36333779924792 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 109001339774377) ^ 15571619967768 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 109001339774377) ^ 5736912619704 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 109001339774377) ^ 2319177442008 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 109001339774377) ^ 1786907209416 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 109001339774377) ^ 9151464 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_109593990089351 : Nat.Prime 109593990089351 := by
  apply lucas_primality 109593990089351 (11 : ZMod 109593990089351)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (13, 1), (61, 1), (45119, 1), (61261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (13, 1), (61, 1), (45119, 1), (61261, 1)] : List FactorBlock).map factorBlockValue).prod) = 109593990089351 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_5
      · exact prime_oneHundredTwentyThreeDQ_13
      · exact prime_oneHundredTwentyThreeDQ_61
      · exact prime_oneHundredTwentyThreeDQ_45119
      · exact prime_oneHundredTwentyThreeDQ_61261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 109593990089351) ^ 54796995044675 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (11 : ZMod 109593990089351) ^ 21918798017870 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (11 : ZMod 109593990089351) ^ 8430306929950 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (11 : ZMod 109593990089351) ^ 1796622788350 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (11 : ZMod 109593990089351) ^ 2428998650 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (11 : ZMod 109593990089351) ^ 1788968350 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_130816944578447 : Nat.Prime 130816944578447 := by
  apply lucas_primality 130816944578447 (5 : ZMod 130816944578447)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (19, 1), (173, 1), (2842734247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (19, 1), (173, 1), (2842734247, 1)] : List FactorBlock).map factorBlockValue).prod) = 130816944578447 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_7
      · exact prime_oneHundredTwentyThreeDQ_19
      · exact prime_oneHundredTwentyThreeDQ_173
      · exact prime_oneHundredTwentyThreeDQ_2842734247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 130816944578447) ^ 65408472289223 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 130816944578447) ^ 18688134939778 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 130816944578447) ^ 6885102346234 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 130816944578447) ^ 756167309702 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 130816944578447) ^ 46018 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_133688978062141 : Nat.Prime 133688978062141 := by
  apply lucas_primality 133688978062141 (7 : ZMod 133688978062141)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (101, 1), (199, 1), (110858731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (101, 1), (199, 1), (110858731, 1)] : List FactorBlock).map factorBlockValue).prod) = 133688978062141 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_5
      · exact prime_oneHundredTwentyThreeDQ_101
      · exact prime_oneHundredTwentyThreeDQ_199
      · exact prime_oneHundredTwentyThreeDQ_110858731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 133688978062141) ^ 66844489031070 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (7 : ZMod 133688978062141) ^ 44562992687380 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (7 : ZMod 133688978062141) ^ 26737795612428 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (7 : ZMod 133688978062141) ^ 1323653248140 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (7 : ZMod 133688978062141) ^ 671803909860 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (7 : ZMod 133688978062141) ^ 1205940 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_212894019958223 : Nat.Prime 212894019958223 := by
  apply lucas_primality 212894019958223 (5 : ZMod 212894019958223)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (4628130868657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (4628130868657, 1)] : List FactorBlock).map factorBlockValue).prod) = 212894019958223 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_23
      · exact prime_oneHundredTwentyThreeDQ_4628130868657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 212894019958223) ^ 106447009979111 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 212894019958223) ^ 9256261737314 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 212894019958223) ^ 46 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_247896867899357 : Nat.Prime 247896867899357 := by
  apply lucas_primality 247896867899357 (2 : ZMod 247896867899357)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (41, 1), (397, 1), (292882439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (41, 1), (397, 1), (292882439, 1)] : List FactorBlock).map factorBlockValue).prod) = 247896867899357 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_13
      · exact prime_oneHundredTwentyThreeDQ_41
      · exact prime_oneHundredTwentyThreeDQ_397
      · exact prime_oneHundredTwentyThreeDQ_292882439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 247896867899357) ^ 123948433949678 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 247896867899357) ^ 19068989838412 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 247896867899357) ^ 6046265070716 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 247896867899357) ^ 624425359948 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 247896867899357) ^ 846404 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_257930760457319 : Nat.Prime 257930760457319 := by
  apply lucas_primality 257930760457319 (11 : ZMod 257930760457319)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (101, 1), (109, 1), (269, 1), (1117, 1), (2999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (101, 1), (109, 1), (269, 1), (1117, 1), (2999, 1)] : List FactorBlock).map factorBlockValue).prod) = 257930760457319 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_13
      · exact prime_oneHundredTwentyThreeDQ_101
      · exact prime_oneHundredTwentyThreeDQ_109
      · exact prime_oneHundredTwentyThreeDQ_269
      · exact prime_oneHundredTwentyThreeDQ_1117
      · exact prime_oneHundredTwentyThreeDQ_2999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 257930760457319) ^ 128965380228659 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (11 : ZMod 257930760457319) ^ 19840827727486 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (11 : ZMod 257930760457319) ^ 2553769905518 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (11 : ZMod 257930760457319) ^ 2366337251902 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (11 : ZMod 257930760457319) ^ 958850410622 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (11 : ZMod 257930760457319) ^ 230913841054 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (11 : ZMod 257930760457319) ^ 86005588682 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_273528084167717 : Nat.Prime 273528084167717 := by
  apply lucas_primality 273528084167717 (2 : ZMod 273528084167717)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (73, 1), (491, 1), (887, 1), (307267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (73, 1), (491, 1), (887, 1), (307267, 1)] : List FactorBlock).map factorBlockValue).prod) = 273528084167717 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_7
      · exact prime_oneHundredTwentyThreeDQ_73
      · exact prime_oneHundredTwentyThreeDQ_491
      · exact prime_oneHundredTwentyThreeDQ_887
      · exact prime_oneHundredTwentyThreeDQ_307267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 273528084167717) ^ 136764042083858 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 273528084167717) ^ 39075440595388 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 273528084167717) ^ 3746960057092 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 273528084167717) ^ 557083674476 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 273528084167717) ^ 308374390268 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 273528084167717) ^ 890196748 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_366020420757353 : Nat.Prime 366020420757353 := by
  apply lucas_primality 366020420757353 (3 : ZMod 366020420757353)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (45752552594669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (45752552594669, 1)] : List FactorBlock).map factorBlockValue).prod) = 366020420757353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_45752552594669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 366020420757353) ^ 183010210378676 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 366020420757353) ^ 8 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_385447666294679 : Nat.Prime 385447666294679 := by
  apply lucas_primality 385447666294679 (7 : ZMod 385447666294679)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 2), (567467, 1), (2009593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 2), (567467, 1), (2009593, 1)] : List FactorBlock).map factorBlockValue).prod) = 385447666294679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_13
      · exact prime_oneHundredTwentyThreeDQ_567467
      · exact prime_oneHundredTwentyThreeDQ_2009593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 385447666294679) ^ 192723833147339 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (7 : ZMod 385447666294679) ^ 29649820484206 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (7 : ZMod 385447666294679) ^ 679242434 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (7 : ZMod 385447666294679) ^ 191803846 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_913439410268023 : Nat.Prime 913439410268023 := by
  apply lucas_primality 913439410268023 (3 : ZMod 913439410268023)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (11, 1), (17, 1), (90457457939, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (11, 1), (17, 1), (90457457939, 1)] : List FactorBlock).map factorBlockValue).prod) = 913439410268023 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_11
      · exact prime_oneHundredTwentyThreeDQ_17
      · exact prime_oneHundredTwentyThreeDQ_90457457939
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 913439410268023) ^ 456719705134011 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 913439410268023) ^ 304479803422674 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 913439410268023) ^ 83039946388002 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 913439410268023) ^ 53731730015766 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 913439410268023) ^ 10098 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_921314287658533 : Nat.Prime 921314287658533 := by
  apply lucas_primality 921314287658533 (2 : ZMod 921314287658533)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (284831, 1), (269549981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (284831, 1), (269549981, 1)] : List FactorBlock).map factorBlockValue).prod) = 921314287658533 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_284831
      · exact prime_oneHundredTwentyThreeDQ_269549981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 921314287658533) ^ 460657143829266 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 921314287658533) ^ 307104762552844 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 921314287658533) ^ 3234599772 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 921314287658533) ^ 3417972 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_1277364119749339 : Nat.Prime 1277364119749339 := by
  apply lucas_primality 1277364119749339 (2 : ZMod 1277364119749339)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (212894019958223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (212894019958223, 1)] : List FactorBlock).map factorBlockValue).prod) = 1277364119749339 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_212894019958223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1277364119749339) ^ 638682059874669 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1277364119749339) ^ 425788039916446 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1277364119749339) ^ 6 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_2319007431785003 : Nat.Prime 2319007431785003 := by
  apply lucas_primality 2319007431785003 (5 : ZMod 2319007431785003)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (17, 1), (15319, 1), (636055141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (17, 1), (15319, 1), (636055141, 1)] : List FactorBlock).map factorBlockValue).prod) = 2319007431785003 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_7
      · exact prime_oneHundredTwentyThreeDQ_17
      · exact prime_oneHundredTwentyThreeDQ_15319
      · exact prime_oneHundredTwentyThreeDQ_636055141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2319007431785003) ^ 1159503715892501 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 2319007431785003) ^ 331286775969286 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 2319007431785003) ^ 136412201869706 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 2319007431785003) ^ 151381123558 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 2319007431785003) ^ 3645922 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_2532804983319613 : Nat.Prime 2532804983319613 := by
  apply lucas_primality 2532804983319613 (2 : ZMod 2532804983319613)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (2999, 1), (70379153699, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (2999, 1), (70379153699, 1)] : List FactorBlock).map factorBlockValue).prod) = 2532804983319613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_2999
      · exact prime_oneHundredTwentyThreeDQ_70379153699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2532804983319613) ^ 1266402491659806 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2532804983319613) ^ 844268327773204 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2532804983319613) ^ 844549844388 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2532804983319613) ^ 35988 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_3119894689839401 : Nat.Prime 3119894689839401 := by
  apply lucas_primality 3119894689839401 (12 : ZMod 3119894689839401)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (11, 1), (1418133949927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (11, 1), (1418133949927, 1)] : List FactorBlock).map factorBlockValue).prod) = 3119894689839401 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_5
      · exact prime_oneHundredTwentyThreeDQ_11
      · exact prime_oneHundredTwentyThreeDQ_1418133949927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (12 : ZMod 3119894689839401) ^ 1559947344919700 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (12 : ZMod 3119894689839401) ^ 623978937967880 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (12 : ZMod 3119894689839401) ^ 283626789985400 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (12 : ZMod 3119894689839401) ^ 2200 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_3273142492240051 : Nat.Prime 3273142492240051 := by
  apply lucas_primality 3273142492240051 (2 : ZMod 3273142492240051)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (73, 1), (4519, 1), (66146741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (73, 1), (4519, 1), (66146741, 1)] : List FactorBlock).map factorBlockValue).prod) = 3273142492240051 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_5
      · exact prime_oneHundredTwentyThreeDQ_73
      · exact prime_oneHundredTwentyThreeDQ_4519
      · exact prime_oneHundredTwentyThreeDQ_66146741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3273142492240051) ^ 1636571246120025 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 3273142492240051) ^ 1091047497413350 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 3273142492240051) ^ 654628498448010 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 3273142492240051) ^ 44837568386850 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 3273142492240051) ^ 724306813950 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 3273142492240051) ^ 49483050 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_4297030639798109 : Nat.Prime 4297030639798109 := by
  apply lucas_primality 4297030639798109 (2 : ZMod 4297030639798109)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (257893, 1), (4165516939, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (257893, 1), (4165516939, 1)] : List FactorBlock).map factorBlockValue).prod) = 4297030639798109 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_257893
      · exact prime_oneHundredTwentyThreeDQ_4165516939
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4297030639798109) ^ 2148515319899054 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 4297030639798109) ^ 16662067756 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 4297030639798109) ^ 1031572 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_5975488216114349 : Nat.Prime 5975488216114349 := by
  apply lucas_primality 5975488216114349 (2 : ZMod 5975488216114349)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (37, 1), (137, 1), (1381, 1), (11231657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (37, 1), (137, 1), (1381, 1), (11231657, 1)] : List FactorBlock).map factorBlockValue).prod) = 5975488216114349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_19
      · exact prime_oneHundredTwentyThreeDQ_37
      · exact prime_oneHundredTwentyThreeDQ_137
      · exact prime_oneHundredTwentyThreeDQ_1381
      · exact prime_oneHundredTwentyThreeDQ_11231657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5975488216114349) ^ 2987744108057174 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 5975488216114349) ^ 314499379795492 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 5975488216114349) ^ 161499681516604 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 5975488216114349) ^ 43616702307404 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 5975488216114349) ^ 4326928469308 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 5975488216114349) ^ 532021964 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_6851823352338157 : Nat.Prime 6851823352338157 := by
  apply lucas_primality 6851823352338157 (2 : ZMod 6851823352338157)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1223, 1), (215389, 1), (2167579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1223, 1), (215389, 1), (2167579, 1)] : List FactorBlock).map factorBlockValue).prod) = 6851823352338157 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_1223
      · exact prime_oneHundredTwentyThreeDQ_215389
      · exact prime_oneHundredTwentyThreeDQ_2167579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6851823352338157) ^ 3425911676169078 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 6851823352338157) ^ 2283941117446052 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 6851823352338157) ^ 5602472078772 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 6851823352338157) ^ 31811389404 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 6851823352338157) ^ 3161048964 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_8028501394952449 : Nat.Prime 8028501394952449 := by
  apply lucas_primality 8028501394952449 (13 : ZMod 8028501394952449)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 2), (31, 1), (37, 1), (43, 1), (173, 1), (408389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 2), (31, 1), (37, 1), (43, 1), (173, 1), (408389, 1)] : List FactorBlock).map factorBlockValue).prod) = 8028501394952449 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_31
      · exact prime_oneHundredTwentyThreeDQ_37
      · exact prime_oneHundredTwentyThreeDQ_43
      · exact prime_oneHundredTwentyThreeDQ_173
      · exact prime_oneHundredTwentyThreeDQ_408389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 8028501394952449) ^ 4014250697476224 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (13 : ZMod 8028501394952449) ^ 2676167131650816 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (13 : ZMod 8028501394952449) ^ 258983915966208 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (13 : ZMod 8028501394952449) ^ 216986524187904 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (13 : ZMod 8028501394952449) ^ 186709334766336 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (13 : ZMod 8028501394952449) ^ 46407522514176 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (13 : ZMod 8028501394952449) ^ 19658956032 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_11151518252563883 : Nat.Prime 11151518252563883 := by
  apply lucas_primality 11151518252563883 (2 : ZMod 11151518252563883)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (131, 1), (42563046765511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (131, 1), (42563046765511, 1)] : List FactorBlock).map factorBlockValue).prod) = 11151518252563883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_131
      · exact prime_oneHundredTwentyThreeDQ_42563046765511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 11151518252563883) ^ 5575759126281941 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 11151518252563883) ^ 85126093531022 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 11151518252563883) ^ 262 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_17668655337510829 : Nat.Prime 17668655337510829 := by
  apply lucas_primality 17668655337510829 (13 : ZMod 17668655337510829)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (523, 1), (134060634143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (523, 1), (134060634143, 1)] : List FactorBlock).map factorBlockValue).prod) = 17668655337510829 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_7
      · exact prime_oneHundredTwentyThreeDQ_523
      · exact prime_oneHundredTwentyThreeDQ_134060634143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 17668655337510829) ^ 8834327668755414 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (13 : ZMod 17668655337510829) ^ 5889551779170276 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (13 : ZMod 17668655337510829) ^ 2524093619644404 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (13 : ZMod 17668655337510829) ^ 33783279804036 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (13 : ZMod 17668655337510829) ^ 131796 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_22303036505127767 : Nat.Prime 22303036505127767 := by
  apply lucas_primality 22303036505127767 (5 : ZMod 22303036505127767)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11151518252563883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11151518252563883, 1)] : List FactorBlock).map factorBlockValue).prod) = 22303036505127767 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_11151518252563883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 22303036505127767) ^ 11151518252563883 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 22303036505127767) ^ 2 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_23790626604074719 : Nat.Prime 23790626604074719 := by
  apply lucas_primality 23790626604074719 (3 : ZMod 23790626604074719)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (19, 1), (31, 1), (73, 1), (359, 1), (523, 1), (18191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (19, 1), (31, 1), (73, 1), (359, 1), (523, 1), (18191, 1)] : List FactorBlock).map factorBlockValue).prod) = 23790626604074719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_19
      · exact prime_oneHundredTwentyThreeDQ_31
      · exact prime_oneHundredTwentyThreeDQ_73
      · exact prime_oneHundredTwentyThreeDQ_359
      · exact prime_oneHundredTwentyThreeDQ_523
      · exact prime_oneHundredTwentyThreeDQ_18191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 23790626604074719) ^ 11895313302037359 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 23790626604074719) ^ 7930208868024906 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 23790626604074719) ^ 1252138242319722 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 23790626604074719) ^ 767439567873378 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 23790626604074719) ^ 325898994576366 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 23790626604074719) ^ 66269154886002 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 23790626604074719) ^ 45488769797466 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 23790626604074719) ^ 1307824012098 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_25182985811079769 : Nat.Prime 25182985811079769 := by
  apply lucas_primality 25182985811079769 (33 : ZMod 25182985811079769)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (17, 1), (24971, 1), (353112493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (17, 1), (24971, 1), (353112493, 1)] : List FactorBlock).map factorBlockValue).prod) = 25182985811079769 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_7
      · exact prime_oneHundredTwentyThreeDQ_17
      · exact prime_oneHundredTwentyThreeDQ_24971
      · exact prime_oneHundredTwentyThreeDQ_353112493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (33 : ZMod 25182985811079769) ^ 12591492905539884 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (33 : ZMod 25182985811079769) ^ 8394328603693256 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (33 : ZMod 25182985811079769) ^ 3597569401582824 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (33 : ZMod 25182985811079769) ^ 1481352106534104 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (33 : ZMod 25182985811079769) ^ 1008489280008 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (33 : ZMod 25182985811079769) ^ 71317176 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_26512159077345917 : Nat.Prime 26512159077345917 := by
  apply lucas_primality 26512159077345917 (2 : ZMod 26512159077345917)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (37, 1), (4111, 1), (3351911569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (37, 1), (4111, 1), (3351911569, 1)] : List FactorBlock).map factorBlockValue).prod) = 26512159077345917 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_13
      · exact prime_oneHundredTwentyThreeDQ_37
      · exact prime_oneHundredTwentyThreeDQ_4111
      · exact prime_oneHundredTwentyThreeDQ_3351911569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 26512159077345917) ^ 13256079538672958 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 26512159077345917) ^ 2039396852103532 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 26512159077345917) ^ 716544839928268 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 26512159077345917) ^ 6449077858756 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 26512159077345917) ^ 7909564 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_39268249280304763 : Nat.Prime 39268249280304763 := by
  apply lucas_primality 39268249280304763 (2 : ZMod 39268249280304763)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (109, 1), (60043194618203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (109, 1), (60043194618203, 1)] : List FactorBlock).map factorBlockValue).prod) = 39268249280304763 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_109
      · exact prime_oneHundredTwentyThreeDQ_60043194618203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 39268249280304763) ^ 19634124640152381 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 39268249280304763) ^ 13089416426768254 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 39268249280304763) ^ 360259167709218 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 39268249280304763) ^ 654 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_42142467542890691 : Nat.Prime 42142467542890691 := by
  apply lucas_primality 42142467542890691 (7 : ZMod 42142467542890691)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (247896867899357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (247896867899357, 1)] : List FactorBlock).map factorBlockValue).prod) = 42142467542890691 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_5
      · exact prime_oneHundredTwentyThreeDQ_17
      · exact prime_oneHundredTwentyThreeDQ_247896867899357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 42142467542890691) ^ 21071233771445345 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (7 : ZMod 42142467542890691) ^ 8428493508578138 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (7 : ZMod 42142467542890691) ^ 2478968678993570 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (7 : ZMod 42142467542890691) ^ 170 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_42147896915954971 : Nat.Prime 42147896915954971 := by
  apply lucas_primality 42147896915954971 (2 : ZMod 42147896915954971)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 1), (19, 1), (601, 1), (5858781301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 1), (19, 1), (601, 1), (5858781301, 1)] : List FactorBlock).map factorBlockValue).prod) = 42147896915954971 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_5
      · exact prime_oneHundredTwentyThreeDQ_7
      · exact prime_oneHundredTwentyThreeDQ_19
      · exact prime_oneHundredTwentyThreeDQ_601
      · exact prime_oneHundredTwentyThreeDQ_5858781301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 42147896915954971) ^ 21073948457977485 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 42147896915954971) ^ 14049298971984990 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 42147896915954971) ^ 8429579383190994 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 42147896915954971) ^ 6021128130850710 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 42147896915954971) ^ 2218310363997630 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 42147896915954971) ^ 70129612172970 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 42147896915954971) ^ 7193970 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_62204093268204473 : Nat.Prime 62204093268204473 := by
  apply lucas_primality 62204093268204473 (3 : ZMod 62204093268204473)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (1017847, 1), (587628869, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (1017847, 1), (587628869, 1)] : List FactorBlock).map factorBlockValue).prod) = 62204093268204473 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_13
      · exact prime_oneHundredTwentyThreeDQ_1017847
      · exact prime_oneHundredTwentyThreeDQ_587628869
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 62204093268204473) ^ 31102046634102236 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 62204093268204473) ^ 4784930251400344 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 62204093268204473) ^ 61113402376 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 62204093268204473) ^ 105856088 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_68148360928716203 : Nat.Prime 68148360928716203 := by
  apply lucas_primality 68148360928716203 (2 : ZMod 68148360928716203)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (6317, 1), (40759, 1), (132339967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (6317, 1), (40759, 1), (132339967, 1)] : List FactorBlock).map factorBlockValue).prod) = 68148360928716203 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_6317
      · exact prime_oneHundredTwentyThreeDQ_40759
      · exact prime_oneHundredTwentyThreeDQ_132339967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 68148360928716203) ^ 34074180464358101 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 68148360928716203) ^ 10788089429906 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 68148360928716203) ^ 1671983143078 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 68148360928716203) ^ 514949206 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_73257488963930321 : Nat.Prime 73257488963930321 := by
  apply lucas_primality 73257488963930321 (3 : ZMod 73257488963930321)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (7, 1), (130816944578447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (7, 1), (130816944578447, 1)] : List FactorBlock).map factorBlockValue).prod) = 73257488963930321 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_5
      · exact prime_oneHundredTwentyThreeDQ_7
      · exact prime_oneHundredTwentyThreeDQ_130816944578447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 73257488963930321) ^ 36628744481965160 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 73257488963930321) ^ 14651497792786064 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 73257488963930321) ^ 10465355566275760 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 73257488963930321) ^ 560 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_100731943244319077 : Nat.Prime 100731943244319077 := by
  apply lucas_primality 100731943244319077 (2 : ZMod 100731943244319077)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (25182985811079769, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (25182985811079769, 1)] : List FactorBlock).map factorBlockValue).prod) = 100731943244319077 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_25182985811079769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 100731943244319077) ^ 50365971622159538 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 100731943244319077) ^ 4 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_111851613009889721 : Nat.Prime 111851613009889721 := by
  apply lucas_primality 111851613009889721 (6 : ZMod 111851613009889721)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (11, 1), (23, 1), (31, 1), (59, 1), (6042936539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (11, 1), (23, 1), (31, 1), (59, 1), (6042936539, 1)] : List FactorBlock).map factorBlockValue).prod) = 111851613009889721 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_5
      · exact prime_oneHundredTwentyThreeDQ_11
      · exact prime_oneHundredTwentyThreeDQ_23
      · exact prime_oneHundredTwentyThreeDQ_31
      · exact prime_oneHundredTwentyThreeDQ_59
      · exact prime_oneHundredTwentyThreeDQ_6042936539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 111851613009889721) ^ 55925806504944860 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (6 : ZMod 111851613009889721) ^ 22370322601977944 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (6 : ZMod 111851613009889721) ^ 10168328455444520 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (6 : ZMod 111851613009889721) ^ 4863113609125640 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (6 : ZMod 111851613009889721) ^ 3608116548706120 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (6 : ZMod 111851613009889721) ^ 1895790051015080 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (6 : ZMod 111851613009889721) ^ 18509480 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_129583617140390807 : Nat.Prime 129583617140390807 := by
  apply lucas_primality 129583617140390807 (5 : ZMod 129583617140390807)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2269, 1), (4119133, 1), (6932339, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2269, 1), (4119133, 1), (6932339, 1)] : List FactorBlock).map factorBlockValue).prod) = 129583617140390807 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_2269
      · exact prime_oneHundredTwentyThreeDQ_4119133
      · exact prime_oneHundredTwentyThreeDQ_6932339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 129583617140390807) ^ 64791808570195403 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 129583617140390807) ^ 57110452684174 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 129583617140390807) ^ 31458954382 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 129583617140390807) ^ 18692625554 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_140228518397647921 : Nat.Prime 140228518397647921 := by
  apply lucas_primality 140228518397647921 (14 : ZMod 140228518397647921)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (1693, 1), (345118424881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (1693, 1), (345118424881, 1)] : List FactorBlock).map factorBlockValue).prod) = 140228518397647921 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_5
      · exact prime_oneHundredTwentyThreeDQ_1693
      · exact prime_oneHundredTwentyThreeDQ_345118424881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 140228518397647921) ^ 70114259198823960 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (14 : ZMod 140228518397647921) ^ 46742839465882640 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (14 : ZMod 140228518397647921) ^ 28045703679529584 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (14 : ZMod 140228518397647921) ^ 82828421971440 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (14 : ZMod 140228518397647921) ^ 406320 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_143399998955215939 : Nat.Prime 143399998955215939 := by
  apply lucas_primality 143399998955215939 (2 : ZMod 143399998955215939)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (41, 1), (44840525001631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (41, 1), (44840525001631, 1)] : List FactorBlock).map factorBlockValue).prod) = 143399998955215939 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_13
      · exact prime_oneHundredTwentyThreeDQ_41
      · exact prime_oneHundredTwentyThreeDQ_44840525001631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 143399998955215939) ^ 71699999477607969 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 143399998955215939) ^ 47799999651738646 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 143399998955215939) ^ 11030769150401226 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 143399998955215939) ^ 3497560950127218 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 143399998955215939) ^ 3198 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_147451771633535077 : Nat.Prime 147451771633535077 := by
  apply lucas_primality 147451771633535077 (5 : ZMod 147451771633535077)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (29, 1), (89, 1), (659, 1), (7224292637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (29, 1), (89, 1), (659, 1), (7224292637, 1)] : List FactorBlock).map factorBlockValue).prod) = 147451771633535077 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_29
      · exact prime_oneHundredTwentyThreeDQ_89
      · exact prime_oneHundredTwentyThreeDQ_659
      · exact prime_oneHundredTwentyThreeDQ_7224292637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 147451771633535077) ^ 73725885816767538 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 147451771633535077) ^ 49150590544511692 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 147451771633535077) ^ 5084543849432244 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 147451771633535077) ^ 1656761479028484 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 147451771633535077) ^ 223750791553164 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 147451771633535077) ^ 20410548 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_422960814287413279 : Nat.Prime 422960814287413279 := by
  apply lucas_primality 422960814287413279 (3 : ZMod 422960814287413279)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1877, 1), (4281047, 1), (8772727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1877, 1), (4281047, 1), (8772727, 1)] : List FactorBlock).map factorBlockValue).prod) = 422960814287413279 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_1877
      · exact prime_oneHundredTwentyThreeDQ_4281047
      · exact prime_oneHundredTwentyThreeDQ_8772727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 422960814287413279) ^ 211480407143706639 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 422960814287413279) ^ 140986938095804426 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 422960814287413279) ^ 225338739631014 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 422960814287413279) ^ 98798451474 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 422960814287413279) ^ 48213151314 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_487934319167696389 : Nat.Prime 487934319167696389 := by
  apply lucas_primality 487934319167696389 (2 : ZMod 487934319167696389)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (1289, 1), (2426519858207, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (1289, 1), (2426519858207, 1)] : List FactorBlock).map factorBlockValue).prod) = 487934319167696389 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_13
      · exact prime_oneHundredTwentyThreeDQ_1289
      · exact prime_oneHundredTwentyThreeDQ_2426519858207
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 487934319167696389) ^ 243967159583848194 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 487934319167696389) ^ 162644773055898796 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 487934319167696389) ^ 37533409166745876 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 487934319167696389) ^ 378537097880292 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 487934319167696389) ^ 201084 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_670984611308268199 : Nat.Prime 670984611308268199 := by
  apply lucas_primality 670984611308268199 (3 : ZMod 670984611308268199)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (47, 1), (24925801, 1), (95458439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (47, 1), (24925801, 1), (95458439, 1)] : List FactorBlock).map factorBlockValue).prod) = 670984611308268199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_47
      · exact prime_oneHundredTwentyThreeDQ_24925801
      · exact prime_oneHundredTwentyThreeDQ_95458439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 670984611308268199) ^ 335492305654134099 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 670984611308268199) ^ 223661537102756066 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 670984611308268199) ^ 14276268325707834 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 670984611308268199) ^ 26919279798 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 670984611308268199) ^ 7029075882 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_765627353215602223 : Nat.Prime 765627353215602223 := by
  apply lucas_primality 765627353215602223 (5 : ZMod 765627353215602223)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1933, 1), (66013739715089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1933, 1), (66013739715089, 1)] : List FactorBlock).map factorBlockValue).prod) = 765627353215602223 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_1933
      · exact prime_oneHundredTwentyThreeDQ_66013739715089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 765627353215602223) ^ 382813676607801111 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 765627353215602223) ^ 255209117738534074 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 765627353215602223) ^ 396082438290534 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 765627353215602223) ^ 11598 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_769511728058840147 : Nat.Prime 769511728058840147 := by
  apply lucas_primality 769511728058840147 (2 : ZMod 769511728058840147)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (439, 1), (4993, 1), (56311, 1), (3117209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (439, 1), (4993, 1), (56311, 1), (3117209, 1)] : List FactorBlock).map factorBlockValue).prod) = 769511728058840147 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_439
      · exact prime_oneHundredTwentyThreeDQ_4993
      · exact prime_oneHundredTwentyThreeDQ_56311
      · exact prime_oneHundredTwentyThreeDQ_3117209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 769511728058840147) ^ 384755864029420073 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 769511728058840147) ^ 1752874095806014 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 769511728058840147) ^ 154118110967122 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 769511728058840147) ^ 13665389143486 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 769511728058840147) ^ 246859202594 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_1005477753206977117 : Nat.Prime 1005477753206977117 := by
  apply lucas_primality 1005477753206977117 (2 : ZMod 1005477753206977117)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (283, 1), (349, 1), (25031, 1), (3081119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (283, 1), (349, 1), (25031, 1), (3081119, 1)] : List FactorBlock).map factorBlockValue).prod) = 1005477753206977117 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_11
      · exact prime_oneHundredTwentyThreeDQ_283
      · exact prime_oneHundredTwentyThreeDQ_349
      · exact prime_oneHundredTwentyThreeDQ_25031
      · exact prime_oneHundredTwentyThreeDQ_3081119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1005477753206977117) ^ 502738876603488558 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1005477753206977117) ^ 335159251068992372 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1005477753206977117) ^ 91407068473361556 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1005477753206977117) ^ 3552924922992852 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1005477753206977117) ^ 2881025080822284 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1005477753206977117) ^ 40169300196036 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1005477753206977117) ^ 326335254564 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_1036668937123126457 : Nat.Prime 1036668937123126457 := by
  apply lucas_primality 1036668937123126457 (3 : ZMod 1036668937123126457)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (129583617140390807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (129583617140390807, 1)] : List FactorBlock).map factorBlockValue).prod) = 1036668937123126457 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_129583617140390807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 1036668937123126457) ^ 518334468561563228 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1036668937123126457) ^ 8 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_1424371553698679479 : Nat.Prime 1424371553698679479 := by
  apply lucas_primality 1424371553698679479 (3 : ZMod 1424371553698679479)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (1451, 1), (1693, 1), (34361, 1), (937477, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (1451, 1), (1693, 1), (34361, 1), (937477, 1)] : List FactorBlock).map factorBlockValue).prod) = 1424371553698679479 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_1451
      · exact prime_oneHundredTwentyThreeDQ_1693
      · exact prime_oneHundredTwentyThreeDQ_34361
      · exact prime_oneHundredTwentyThreeDQ_937477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1424371553698679479) ^ 712185776849339739 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1424371553698679479) ^ 474790517899559826 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1424371553698679479) ^ 981648210681378 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1424371553698679479) ^ 841329919491246 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1424371553698679479) ^ 41453146116198 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1424371553698679479) ^ 1519366932414 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_1570729971212190521 : Nat.Prime 1570729971212190521 := by
  apply lucas_primality 1570729971212190521 (3 : ZMod 1570729971212190521)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (39268249280304763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (39268249280304763, 1)] : List FactorBlock).map factorBlockValue).prod) = 1570729971212190521 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_5
      · exact prime_oneHundredTwentyThreeDQ_39268249280304763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1570729971212190521) ^ 785364985606095260 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1570729971212190521) ^ 314145994242438104 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 1570729971212190521) ^ 40 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_3351654105219542953 : Nat.Prime 3351654105219542953 := by
  apply lucas_primality 3351654105219542953 (5 : ZMod 3351654105219542953)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (1637, 1), (56099, 1), (506900707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (1637, 1), (56099, 1), (506900707, 1)] : List FactorBlock).map factorBlockValue).prod) = 3351654105219542953 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_1637
      · exact prime_oneHundredTwentyThreeDQ_56099
      · exact prime_oneHundredTwentyThreeDQ_506900707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 3351654105219542953) ^ 1675827052609771476 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 3351654105219542953) ^ 1117218035073180984 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 3351654105219542953) ^ 2047436838863496 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 3351654105219542953) ^ 59745344929848 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 3351654105219542953) ^ 6612052536 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_4111856362216271923 : Nat.Prime 4111856362216271923 := by
  apply lucas_primality 4111856362216271923 (2 : ZMod 4111856362216271923)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (19, 1), (89, 1), (36842610273787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (19, 1), (89, 1), (36842610273787, 1)] : List FactorBlock).map factorBlockValue).prod) = 4111856362216271923 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_11
      · exact prime_oneHundredTwentyThreeDQ_19
      · exact prime_oneHundredTwentyThreeDQ_89
      · exact prime_oneHundredTwentyThreeDQ_36842610273787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4111856362216271923) ^ 2055928181108135961 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 4111856362216271923) ^ 1370618787405423974 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 4111856362216271923) ^ 373805123837842902 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 4111856362216271923) ^ 216413492748224838 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 4111856362216271923) ^ 46200633283328898 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 4111856362216271923) ^ 111606 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_6168559768548107981 : Nat.Prime 6168559768548107981 := by
  apply lucas_primality 6168559768548107981 (2 : ZMod 6168559768548107981)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (19, 1), (2319007431785003, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (19, 1), (2319007431785003, 1)] : List FactorBlock).map factorBlockValue).prod) = 6168559768548107981 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_5
      · exact prime_oneHundredTwentyThreeDQ_7
      · exact prime_oneHundredTwentyThreeDQ_19
      · exact prime_oneHundredTwentyThreeDQ_2319007431785003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6168559768548107981) ^ 3084279884274053990 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 6168559768548107981) ^ 1233711953709621596 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 6168559768548107981) ^ 881222824078301140 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 6168559768548107981) ^ 324661040449900420 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 6168559768548107981) ^ 2660 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_6884737533938997307 : Nat.Prime 6884737533938997307 := by
  apply lucas_primality 6884737533938997307 (2 : ZMod 6884737533938997307)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (7, 1), (17, 1), (89, 1), (4012688116243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (7, 1), (17, 1), (89, 1), (4012688116243, 1)] : List FactorBlock).map factorBlockValue).prod) = 6884737533938997307 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_7
      · exact prime_oneHundredTwentyThreeDQ_17
      · exact prime_oneHundredTwentyThreeDQ_89
      · exact prime_oneHundredTwentyThreeDQ_4012688116243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6884737533938997307) ^ 3442368766969498653 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 6884737533938997307) ^ 2294912511312999102 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 6884737533938997307) ^ 983533933419856758 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 6884737533938997307) ^ 404984560819941018 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 6884737533938997307) ^ 77356601504932554 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 6884737533938997307) ^ 1715742 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_12337119537096215963 : Nat.Prime 12337119537096215963 := by
  apply lucas_primality 12337119537096215963 (2 : ZMod 12337119537096215963)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (6168559768548107981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (6168559768548107981, 1)] : List FactorBlock).map factorBlockValue).prod) = 12337119537096215963 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_6168559768548107981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 12337119537096215963) ^ 6168559768548107981 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 12337119537096215963) ^ 2 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_18932046908044083887 : Nat.Prime 18932046908044083887 := by
  apply lucas_primality 18932046908044083887 (5 : ZMod 18932046908044083887)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1901, 1), (5189, 1), (959625519287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1901, 1), (5189, 1), (959625519287, 1)] : List FactorBlock).map factorBlockValue).prod) = 18932046908044083887 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_1901
      · exact prime_oneHundredTwentyThreeDQ_5189
      · exact prime_oneHundredTwentyThreeDQ_959625519287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 18932046908044083887) ^ 9466023454022041943 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 18932046908044083887) ^ 9958993639160486 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 18932046908044083887) ^ 3648496224329174 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 18932046908044083887) ^ 19728578 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_25555136900618217751 : Nat.Prime 25555136900618217751 := by
  apply lucas_primality 25555136900618217751 (6 : ZMod 25555136900618217751)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 3), (11, 1), (13, 1), (302723, 1), (787110113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 3), (11, 1), (13, 1), (302723, 1), (787110113, 1)] : List FactorBlock).map factorBlockValue).prod) = 25555136900618217751 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_5
      · exact prime_oneHundredTwentyThreeDQ_11
      · exact prime_oneHundredTwentyThreeDQ_13
      · exact prime_oneHundredTwentyThreeDQ_302723
      · exact prime_oneHundredTwentyThreeDQ_787110113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 25555136900618217751) ^ 12777568450309108875 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (6 : ZMod 25555136900618217751) ^ 8518378966872739250 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (6 : ZMod 25555136900618217751) ^ 5111027380123643550 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (6 : ZMod 25555136900618217751) ^ 2323194263692565250 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (6 : ZMod 25555136900618217751) ^ 1965779761586016750 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (6 : ZMod 25555136900618217751) ^ 84417559619250 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (6 : ZMod 25555136900618217751) ^ 32467041750 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_25933795647479510069 : Nat.Prime 25933795647479510069 := by
  apply lucas_primality 25933795647479510069 (2 : ZMod 25933795647479510069)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (6299, 1), (31327, 1), (1729267091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (6299, 1), (31327, 1), (1729267091, 1)] : List FactorBlock).map factorBlockValue).prod) = 25933795647479510069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_19
      · exact prime_oneHundredTwentyThreeDQ_6299
      · exact prime_oneHundredTwentyThreeDQ_31327
      · exact prime_oneHundredTwentyThreeDQ_1729267091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 25933795647479510069) ^ 12966897823739755034 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 25933795647479510069) ^ 1364936613025237372 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 25933795647479510069) ^ 4117129012141532 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 25933795647479510069) ^ 827841658871884 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 25933795647479510069) ^ 14996986748 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_33551929945480087019 : Nat.Prime 33551929945480087019 := by
  apply lucas_primality 33551929945480087019 (2 : ZMod 33551929945480087019)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (229, 1), (73257488963930321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (229, 1), (73257488963930321, 1)] : List FactorBlock).map factorBlockValue).prod) = 33551929945480087019 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_229
      · exact prime_oneHundredTwentyThreeDQ_73257488963930321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 33551929945480087019) ^ 16775964972740043509 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 33551929945480087019) ^ 146514977927860642 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 33551929945480087019) ^ 458 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_39812622367211315597 : Nat.Prime 39812622367211315597 := by
  apply lucas_primality 39812622367211315597 (2 : ZMod 39812622367211315597)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (765627353215602223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (765627353215602223, 1)] : List FactorBlock).map factorBlockValue).prod) = 39812622367211315597 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_13
      · exact prime_oneHundredTwentyThreeDQ_765627353215602223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 39812622367211315597) ^ 19906311183605657798 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 39812622367211315597) ^ 3062509412862408892 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 39812622367211315597) ^ 52 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_40582258612570016203 : Nat.Prime 40582258612570016203 := by
  apply lucas_primality 40582258612570016203 (3 : ZMod 40582258612570016203)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (20411, 1), (47339388206371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (20411, 1), (47339388206371, 1)] : List FactorBlock).map factorBlockValue).prod) = 40582258612570016203 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_7
      · exact prime_oneHundredTwentyThreeDQ_20411
      · exact prime_oneHundredTwentyThreeDQ_47339388206371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 40582258612570016203) ^ 20291129306285008101 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 40582258612570016203) ^ 13527419537523338734 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 40582258612570016203) ^ 5797465516081430886 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 40582258612570016203) ^ 1988254304667582 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 40582258612570016203) ^ 857262 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_61938929534095539589 : Nat.Prime 61938929534095539589 := by
  apply lucas_primality 61938929534095539589 (2 : ZMod 61938929534095539589)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (17, 1), (396619, 1), (58886624501, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (17, 1), (396619, 1), (58886624501, 1)] : List FactorBlock).map factorBlockValue).prod) = 61938929534095539589 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_13
      · exact prime_oneHundredTwentyThreeDQ_17
      · exact prime_oneHundredTwentyThreeDQ_396619
      · exact prime_oneHundredTwentyThreeDQ_58886624501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 61938929534095539589) ^ 30969464767047769794 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 61938929534095539589) ^ 20646309844698513196 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 61938929534095539589) ^ 4764533041084272276 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 61938929534095539589) ^ 3643466443182090564 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 61938929534095539589) ^ 156167328176652 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 61938929534095539589) ^ 1051833588 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_67340047169201976727 : Nat.Prime 67340047169201976727 := by
  apply lucas_primality 67340047169201976727 (3 : ZMod 67340047169201976727)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (43, 1), (397, 1), (619, 1), (1062117475429, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (43, 1), (397, 1), (619, 1), (1062117475429, 1)] : List FactorBlock).map factorBlockValue).prod) = 67340047169201976727 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_43
      · exact prime_oneHundredTwentyThreeDQ_397
      · exact prime_oneHundredTwentyThreeDQ_619
      · exact prime_oneHundredTwentyThreeDQ_1062117475429
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 67340047169201976727) ^ 33670023584600988363 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 67340047169201976727) ^ 22446682389733992242 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 67340047169201976727) ^ 1566047608586092482 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 67340047169201976727) ^ 169622285060962158 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 67340047169201976727) ^ 108788444538290754 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 67340047169201976727) ^ 63401694 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_134903845900098415927 : Nat.Prime 134903845900098415927 := by
  apply lucas_primality 134903845900098415927 (6 : ZMod 134903845900098415927)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (1433, 1), (10501, 1), (498052330879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (1433, 1), (10501, 1), (498052330879, 1)] : List FactorBlock).map factorBlockValue).prod) = 134903845900098415927 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_1433
      · exact prime_oneHundredTwentyThreeDQ_10501
      · exact prime_oneHundredTwentyThreeDQ_498052330879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 134903845900098415927) ^ 67451922950049207963 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (6 : ZMod 134903845900098415927) ^ 44967948633366138642 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (6 : ZMod 134903845900098415927) ^ 94140855478086822 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (6 : ZMod 134903845900098415927) ^ 12846761822692926 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (6 : ZMod 134903845900098415927) ^ 270862794 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_173186634009254498821 : Nat.Prime 173186634009254498821 := by
  apply lucas_primality 173186634009254498821 (2 : ZMod 173186634009254498821)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (11, 1), (167, 1), (12697, 1), (84313, 1), (489257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (11, 1), (167, 1), (12697, 1), (84313, 1), (489257, 1)] : List FactorBlock).map factorBlockValue).prod) = 173186634009254498821 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_5
      · exact prime_oneHundredTwentyThreeDQ_11
      · exact prime_oneHundredTwentyThreeDQ_167
      · exact prime_oneHundredTwentyThreeDQ_12697
      · exact prime_oneHundredTwentyThreeDQ_84313
      · exact prime_oneHundredTwentyThreeDQ_489257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 173186634009254498821) ^ 86593317004627249410 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 173186634009254498821) ^ 57728878003084832940 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 173186634009254498821) ^ 34637326801850899764 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 173186634009254498821) ^ 15744239455386772620 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 173186634009254498821) ^ 1037045712630266460 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 173186634009254498821) ^ 13639964874321060 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 173186634009254498821) ^ 2054091706015140 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 173186634009254498821) ^ 353978857756260 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_193321534648399602553 : Nat.Prime 193321534648399602553 := by
  apply lucas_primality 193321534648399602553 (5 : ZMod 193321534648399602553)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (83, 1), (301759, 1), (107203610803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (83, 1), (301759, 1), (107203610803, 1)] : List FactorBlock).map factorBlockValue).prod) = 193321534648399602553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_83
      · exact prime_oneHundredTwentyThreeDQ_301759
      · exact prime_oneHundredTwentyThreeDQ_107203610803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 193321534648399602553) ^ 96660767324199801276 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 193321534648399602553) ^ 64440511549466534184 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 193321534648399602553) ^ 2329175116245778344 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 193321534648399602553) ^ 640648778158728 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 193321534648399602553) ^ 1803311784 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_256223811061086791179 : Nat.Prime 256223811061086791179 := by
  apply lucas_primality 256223811061086791179 (2 : ZMod 256223811061086791179)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (6863, 1), (366020420757353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (6863, 1), (366020420757353, 1)] : List FactorBlock).map factorBlockValue).prod) = 256223811061086791179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_17
      · exact prime_oneHundredTwentyThreeDQ_6863
      · exact prime_oneHundredTwentyThreeDQ_366020420757353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 256223811061086791179) ^ 128111905530543395589 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 85407937020362263726 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 15071988885946281834 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 37334082917250006 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 700026 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_320510527058681839513 : Nat.Prime 320510527058681839513 := by
  apply lucas_primality 320510527058681839513 (11 : ZMod 320510527058681839513)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (11549, 1), (385447666294679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (11549, 1), (385447666294679, 1)] : List FactorBlock).map factorBlockValue).prod) = 320510527058681839513 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_11549
      · exact prime_oneHundredTwentyThreeDQ_385447666294679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 320510527058681839513) ^ 160255263529340919756 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (11 : ZMod 320510527058681839513) ^ 106836842352893946504 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (11 : ZMod 320510527058681839513) ^ 27752231973216888 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (11 : ZMod 320510527058681839513) ^ 831528 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_436828283214730158953 : Nat.Prime 436828283214730158953 := by
  apply lucas_primality 436828283214730158953 (3 : ZMod 436828283214730158953)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (59, 1), (773, 1), (1151, 1), (77527, 1), (13417171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (59, 1), (773, 1), (1151, 1), (77527, 1), (13417171, 1)] : List FactorBlock).map factorBlockValue).prod) = 436828283214730158953 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_59
      · exact prime_oneHundredTwentyThreeDQ_773
      · exact prime_oneHundredTwentyThreeDQ_1151
      · exact prime_oneHundredTwentyThreeDQ_77527
      · exact prime_oneHundredTwentyThreeDQ_13417171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 436828283214730158953) ^ 218414141607365079476 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 436828283214730158953) ^ 7403869207029324728 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 436828283214730158953) ^ 565107740251914824 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 436828283214730158953) ^ 379520663088384152 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 436828283214730158953) ^ 5634530979074776 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 436828283214730158953) ^ 32557405969912 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_642943883070206397899 : Nat.Prime 642943883070206397899 := by
  apply lucas_primality 642943883070206397899 (2 : ZMod 642943883070206397899)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (109, 1), (1583, 1), (109593990089351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (109, 1), (1583, 1), (109593990089351, 1)] : List FactorBlock).map factorBlockValue).prod) = 642943883070206397899 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_17
      · exact prime_oneHundredTwentyThreeDQ_109
      · exact prime_oneHundredTwentyThreeDQ_1583
      · exact prime_oneHundredTwentyThreeDQ_109593990089351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 642943883070206397899) ^ 321471941535103198949 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 642943883070206397899) ^ 37820228415894493994 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 642943883070206397899) ^ 5898567734589049522 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 642943883070206397899) ^ 406155327271134806 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 642943883070206397899) ^ 5866598 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_721933744101063946817 : Nat.Prime 721933744101063946817 := by
  apply lucas_primality 721933744101063946817 (3 : ZMod 721933744101063946817)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (7, 1), (13, 1), (29, 1), (619, 1), (1427, 1), (4839086167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (7, 1), (13, 1), (29, 1), (619, 1), (1427, 1), (4839086167, 1)] : List FactorBlock).map factorBlockValue).prod) = 721933744101063946817 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_7
      · exact prime_oneHundredTwentyThreeDQ_13
      · exact prime_oneHundredTwentyThreeDQ_29
      · exact prime_oneHundredTwentyThreeDQ_619
      · exact prime_oneHundredTwentyThreeDQ_1427
      · exact prime_oneHundredTwentyThreeDQ_4839086167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 721933744101063946817) ^ 360966872050531973408 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 721933744101063946817) ^ 103133392014437706688 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 721933744101063946817) ^ 55533364930851072832 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 721933744101063946817) ^ 24894267037967722304 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 721933744101063946817) ^ 1166290378192348864 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 721933744101063946817) ^ 505910122004950208 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 721933744101063946817) ^ 149188032448 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_1134848600826185800781 : Nat.Prime 1134848600826185800781 := by
  apply lucas_primality 1134848600826185800781 (2 : ZMod 1134848600826185800781)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (43, 1), (521, 1), (2532804983319613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (43, 1), (521, 1), (2532804983319613, 1)] : List FactorBlock).map factorBlockValue).prod) = 1134848600826185800781 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_5
      · exact prime_oneHundredTwentyThreeDQ_43
      · exact prime_oneHundredTwentyThreeDQ_521
      · exact prime_oneHundredTwentyThreeDQ_2532804983319613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1134848600826185800781) ^ 567424300413092900390 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1134848600826185800781) ^ 226969720165237160156 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1134848600826185800781) ^ 26391827926190367460 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1134848600826185800781) ^ 2178212285654867180 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1134848600826185800781) ^ 448060 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_1205269042013298899237 : Nat.Prime 1205269042013298899237 := by
  apply lucas_primality 1205269042013298899237 (2 : ZMod 1205269042013298899237)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (1549, 1), (47713, 1), (341461, 1), (519119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (1549, 1), (47713, 1), (341461, 1), (519119, 1)] : List FactorBlock).map factorBlockValue).prod) = 1205269042013298899237 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_23
      · exact prime_oneHundredTwentyThreeDQ_1549
      · exact prime_oneHundredTwentyThreeDQ_47713
      · exact prime_oneHundredTwentyThreeDQ_341461
      · exact prime_oneHundredTwentyThreeDQ_519119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1205269042013298899237) ^ 602634521006649449618 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1205269042013298899237) ^ 52403001826665169532 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1205269042013298899237) ^ 778094927058294964 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1205269042013298899237) ^ 25260810303550372 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1205269042013298899237) ^ 3529741440496276 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1205269042013298899237) ^ 2321758675782044 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_1336931512631403248311 : Nat.Prime 1336931512631403248311 := by
  apply lucas_primality 1336931512631403248311 (13 : ZMod 1336931512631403248311)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (19, 1), (50733167, 1), (46231962649, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (19, 1), (50733167, 1), (46231962649, 1)] : List FactorBlock).map factorBlockValue).prod) = 1336931512631403248311 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_5
      · exact prime_oneHundredTwentyThreeDQ_19
      · exact prime_oneHundredTwentyThreeDQ_50733167
      · exact prime_oneHundredTwentyThreeDQ_46231962649
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 1336931512631403248311) ^ 668465756315701624155 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (13 : ZMod 1336931512631403248311) ^ 445643837543801082770 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (13 : ZMod 1336931512631403248311) ^ 267386302526280649662 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (13 : ZMod 1336931512631403248311) ^ 70364816454284381490 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (13 : ZMod 1336931512631403248311) ^ 26352218709930 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (13 : ZMod 1336931512631403248311) ^ 28917905190 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_1838504180635051403989 : Nat.Prime 1838504180635051403989 := by
  apply lucas_primality 1838504180635051403989 (2 : ZMod 1838504180635051403989)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (821, 1), (62204093268204473, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (821, 1), (62204093268204473, 1)] : List FactorBlock).map factorBlockValue).prod) = 1838504180635051403989 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_821
      · exact prime_oneHundredTwentyThreeDQ_62204093268204473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1838504180635051403989) ^ 919252090317525701994 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1838504180635051403989) ^ 612834726878350467996 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1838504180635051403989) ^ 2239347357655361028 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 1838504180635051403989) ^ 29556 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_2361295683120577261463 : Nat.Prime 2361295683120577261463 := by
  apply lucas_primality 2361295683120577261463 (5 : ZMod 2361295683120577261463)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (14461, 1), (4297030639798109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (14461, 1), (4297030639798109, 1)] : List FactorBlock).map factorBlockValue).prod) = 2361295683120577261463 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_19
      · exact prime_oneHundredTwentyThreeDQ_14461
      · exact prime_oneHundredTwentyThreeDQ_4297030639798109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2361295683120577261463) ^ 1180647841560288630731 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 2361295683120577261463) ^ 124278720164240908498 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 2361295683120577261463) ^ 163287164312328142 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 2361295683120577261463) ^ 549518 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_2707258320970369460597 : Nat.Prime 2707258320970369460597 := by
  apply lucas_primality 2707258320970369460597 (2 : ZMod 2707258320970369460597)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (39812622367211315597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (39812622367211315597, 1)] : List FactorBlock).map factorBlockValue).prod) = 2707258320970369460597 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_17
      · exact prime_oneHundredTwentyThreeDQ_39812622367211315597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2707258320970369460597) ^ 1353629160485184730298 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2707258320970369460597) ^ 159250489468845262388 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 2707258320970369460597) ^ 68 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_3074685732733041494149 : Nat.Prime 3074685732733041494149 := by
  apply lucas_primality 3074685732733041494149 (2 : ZMod 3074685732733041494149)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (256223811061086791179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (256223811061086791179, 1)] : List FactorBlock).map factorBlockValue).prod) = 3074685732733041494149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_256223811061086791179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3074685732733041494149) ^ 1537342866366520747074 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 3074685732733041494149) ^ 1024895244244347164716 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 3074685732733041494149) ^ 12 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_3284043825257810554081 : Nat.Prime 3284043825257810554081 := by
  apply lucas_primality 3284043825257810554081 (22 : ZMod 3284043825257810554081)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 1), (25013, 1), (273528084167717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 1), (25013, 1), (273528084167717, 1)] : List FactorBlock).map factorBlockValue).prod) = 3284043825257810554081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_5
      · exact prime_oneHundredTwentyThreeDQ_25013
      · exact prime_oneHundredTwentyThreeDQ_273528084167717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (22 : ZMod 3284043825257810554081) ^ 1642021912628905277040 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (22 : ZMod 3284043825257810554081) ^ 1094681275085936851360 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (22 : ZMod 3284043825257810554081) ^ 656808765051562110816 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (22 : ZMod 3284043825257810554081) ^ 131293480400504160 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (22 : ZMod 3284043825257810554081) ^ 12006240 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_3945063790520879818283 : Nat.Prime 3945063790520879818283 := by
  apply lucas_primality 3945063790520879818283 (2 : ZMod 3945063790520879818283)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (8929, 1), (869419, 1), (254092639391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (8929, 1), (869419, 1), (254092639391, 1)] : List FactorBlock).map factorBlockValue).prod) = 3945063790520879818283 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_8929
      · exact prime_oneHundredTwentyThreeDQ_869419
      · exact prime_oneHundredTwentyThreeDQ_254092639391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3945063790520879818283) ^ 1972531895260439909141 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 3945063790520879818283) ^ 441825936893367658 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 3945063790520879818283) ^ 4537586354244478 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 3945063790520879818283) ^ 15526084502 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_17939447122633204255601 : Nat.Prime 17939447122633204255601 := by
  apply lucas_primality 17939447122633204255601 (3 : ZMod 17939447122633204255601)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 2), (3618071, 1), (12395726288009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 2), (3618071, 1), (12395726288009, 1)] : List FactorBlock).map factorBlockValue).prod) = 17939447122633204255601 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_5
      · exact prime_oneHundredTwentyThreeDQ_3618071
      · exact prime_oneHundredTwentyThreeDQ_12395726288009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 17939447122633204255601) ^ 8969723561316602127800 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 17939447122633204255601) ^ 3587889424526640851120 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 17939447122633204255601) ^ 4958290515203600 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 17939447122633204255601) ^ 1447228400 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_21383825971815701546303 : Nat.Prime 21383825971815701546303 := by
  apply lucas_primality 21383825971815701546303 (5 : ZMod 21383825971815701546303)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (53, 1), (661, 1), (77347, 1), (3945795860701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (53, 1), (661, 1), (77347, 1), (3945795860701, 1)] : List FactorBlock).map factorBlockValue).prod) = 21383825971815701546303 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_53
      · exact prime_oneHundredTwentyThreeDQ_661
      · exact prime_oneHundredTwentyThreeDQ_77347
      · exact prime_oneHundredTwentyThreeDQ_3945795860701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 21383825971815701546303) ^ 10691912985907850773151 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 21383825971815701546303) ^ 403468414562560406534 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 21383825971815701546303) ^ 32350720078389866182 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 21383825971815701546303) ^ 276466132775876266 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 21383825971815701546303) ^ 5419394902 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_58888919967460251514613 : Nat.Prime 58888919967460251514613 := by
  apply lucas_primality 58888919967460251514613 (2 : ZMod 58888919967460251514613)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (229043197, 1), (4944391472773, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (229043197, 1), (4944391472773, 1)] : List FactorBlock).map factorBlockValue).prod) = 58888919967460251514613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_13
      · exact prime_oneHundredTwentyThreeDQ_229043197
      · exact prime_oneHundredTwentyThreeDQ_4944391472773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 58888919967460251514613) ^ 29444459983730125757306 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 58888919967460251514613) ^ 4529916920573865501124 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 58888919967460251514613) ^ 257108356584196 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 58888919967460251514613) ^ 11910246244 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_88248200670482467391473 : Nat.Prime 88248200670482467391473 := by
  apply lucas_primality 88248200670482467391473 (5 : ZMod 88248200670482467391473)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (1838504180635051403989, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (1838504180635051403989, 1)] : List FactorBlock).map factorBlockValue).prod) = 88248200670482467391473 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_1838504180635051403989
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 88248200670482467391473) ^ 44124100335241233695736 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 88248200670482467391473) ^ 29416066890160822463824 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 88248200670482467391473) ^ 48 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_164264015977687338492443 : Nat.Prime 164264015977687338492443 := by
  apply lucas_primality 164264015977687338492443 (2 : ZMod 164264015977687338492443)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (4946003, 1), (1277364119749339, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (4946003, 1), (1277364119749339, 1)] : List FactorBlock).map factorBlockValue).prod) = 164264015977687338492443 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_13
      · exact prime_oneHundredTwentyThreeDQ_4946003
      · exact prime_oneHundredTwentyThreeDQ_1277364119749339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 164264015977687338492443) ^ 82132007988843669246221 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 164264015977687338492443) ^ 12635693536745179884034 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 164264015977687338492443) ^ 33211467113482814 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 164264015977687338492443) ^ 128596078 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_486038486138155962003989 : Nat.Prime 486038486138155962003989 := by
  apply lucas_primality 486038486138155962003989 (2 : ZMod 486038486138155962003989)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (37, 1), (3284043825257810554081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (37, 1), (3284043825257810554081, 1)] : List FactorBlock).map factorBlockValue).prod) = 486038486138155962003989 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_37
      · exact prime_oneHundredTwentyThreeDQ_3284043825257810554081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 486038486138155962003989) ^ 243019243069077981001994 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 486038486138155962003989) ^ 13136175301031242216324 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 486038486138155962003989) ^ 148 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_497643265214472763492283 : Nat.Prime 497643265214472763492283 := by
  apply lucas_primality 497643265214472763492283 (2 : ZMod 497643265214472763492283)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (43, 1), (61, 1), (293, 1), (661, 1), (636931, 1), (69909419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (43, 1), (61, 1), (293, 1), (661, 1), (636931, 1), (69909419, 1)] : List FactorBlock).map factorBlockValue).prod) = 497643265214472763492283 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_11
      · exact prime_oneHundredTwentyThreeDQ_43
      · exact prime_oneHundredTwentyThreeDQ_61
      · exact prime_oneHundredTwentyThreeDQ_293
      · exact prime_oneHundredTwentyThreeDQ_661
      · exact prime_oneHundredTwentyThreeDQ_636931
      · exact prime_oneHundredTwentyThreeDQ_69909419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 497643265214472763492283) ^ 248821632607236381746141 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 497643265214472763492283) ^ 45240296837679342135662 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 497643265214472763492283) ^ 11573099191034250313774 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 497643265214472763492283) ^ 8158086314991356778562 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 497643265214472763492283) ^ 1698441178206391684274 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 497643265214472763492283) ^ 752864243894815073362 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 497643265214472763492283) ^ 781314247876885822 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 497643265214472763492283) ^ 7118400815410478 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_623382060343832397026233 : Nat.Prime 623382060343832397026233 := by
  apply lucas_primality 623382060343832397026233 (5 : ZMod 623382060343832397026233)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (2361295683120577261463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (2361295683120577261463, 1)] : List FactorBlock).map factorBlockValue).prod) = 623382060343832397026233 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_11
      · exact prime_oneHundredTwentyThreeDQ_2361295683120577261463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 623382060343832397026233) ^ 311691030171916198513116 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 623382060343832397026233) ^ 207794020114610799008744 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 623382060343832397026233) ^ 56671096394893854275112 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 623382060343832397026233) ^ 264 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_1416564319130368985581919 : Nat.Prime 1416564319130368985581919 := by
  apply lucas_primality 1416564319130368985581919 (13 : ZMod 1416564319130368985581919)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (563, 1), (40582258612570016203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (563, 1), (40582258612570016203, 1)] : List FactorBlock).map factorBlockValue).prod) = 1416564319130368985581919 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_31
      · exact prime_oneHundredTwentyThreeDQ_563
      · exact prime_oneHundredTwentyThreeDQ_40582258612570016203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 1416564319130368985581919) ^ 708282159565184492790959 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (13 : ZMod 1416564319130368985581919) ^ 45695623197753838244578 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (13 : ZMod 1416564319130368985581919) ^ 2516100033979341004586 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (13 : ZMod 1416564319130368985581919) ^ 34906 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_2014864654990746658499681 : Nat.Prime 2014864654990746658499681 := by
  apply lucas_primality 2014864654990746658499681 (3 : ZMod 2014864654990746658499681)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (7, 1), (41, 1), (47, 1), (71, 1), (5081, 1), (2587847008057, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (7, 1), (41, 1), (47, 1), (71, 1), (5081, 1), (2587847008057, 1)] : List FactorBlock).map factorBlockValue).prod) = 2014864654990746658499681 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_5
      · exact prime_oneHundredTwentyThreeDQ_7
      · exact prime_oneHundredTwentyThreeDQ_41
      · exact prime_oneHundredTwentyThreeDQ_47
      · exact prime_oneHundredTwentyThreeDQ_71
      · exact prime_oneHundredTwentyThreeDQ_5081
      · exact prime_oneHundredTwentyThreeDQ_2587847008057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2014864654990746658499681) ^ 1007432327495373329249840 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 2014864654990746658499681) ^ 402972930998149331699936 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 2014864654990746658499681) ^ 287837807855820951214240 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 2014864654990746658499681) ^ 49143040365627967280480 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 2014864654990746658499681) ^ 42869460744483971457440 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 2014864654990746658499681) ^ 28378375422404882514080 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 2014864654990746658499681) ^ 396548839793494717280 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 2014864654990746658499681) ^ 778587238240 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_6932298552922112722691399 : Nat.Prime 6932298552922112722691399 := by
  apply lucas_primality 6932298552922112722691399 (11 : ZMod 6932298552922112722691399)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 2), (60111803, 1), (109001339774377, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 2), (60111803, 1), (109001339774377, 1)] : List FactorBlock).map factorBlockValue).prod) = 6932298552922112722691399 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_23
      · exact prime_oneHundredTwentyThreeDQ_60111803
      · exact prime_oneHundredTwentyThreeDQ_109001339774377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 6932298552922112722691399) ^ 3466149276461056361345699 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (11 : ZMod 6932298552922112722691399) ^ 301404284909657074899626 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (11 : ZMod 6932298552922112722691399) ^ 115323417481290866 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (11 : ZMod 6932298552922112722691399) ^ 63598287574 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_13458475404409732400175611 : Nat.Prime 13458475404409732400175611 := by
  apply lucas_primality 13458475404409732400175611 (2 : ZMod 13458475404409732400175611)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1748963, 1), (769511728058840147, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1748963, 1), (769511728058840147, 1)] : List FactorBlock).map factorBlockValue).prod) = 13458475404409732400175611 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_5
      · exact prime_oneHundredTwentyThreeDQ_1748963
      · exact prime_oneHundredTwentyThreeDQ_769511728058840147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 13458475404409732400175611) ^ 6729237702204866200087805 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 13458475404409732400175611) ^ 2691695080881946480035122 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 13458475404409732400175611) ^ 7695117280588401470 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 13458475404409732400175611) ^ 17489630 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_32265104669324863231395047 : Nat.Prime 32265104669324863231395047 := by
  apply lucas_primality 32265104669324863231395047 (5 : ZMod 32265104669324863231395047)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (59, 1), (101, 1), (2707258320970369460597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (59, 1), (101, 1), (2707258320970369460597, 1)] : List FactorBlock).map factorBlockValue).prod) = 32265104669324863231395047 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_59
      · exact prime_oneHundredTwentyThreeDQ_101
      · exact prime_oneHundredTwentyThreeDQ_2707258320970369460597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 32265104669324863231395047) ^ 16132552334662431615697523 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 32265104669324863231395047) ^ 546866180836014631040594 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 32265104669324863231395047) ^ 319456481874503596350446 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 32265104669324863231395047) ^ 11918 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_169683578465165879327768351 : Nat.Prime 169683578465165879327768351 := by
  apply lucas_primality 169683578465165879327768351 (17 : ZMod 169683578465165879327768351)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (31, 1), (105601, 1), (1036668937123126457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (31, 1), (105601, 1), (1036668937123126457, 1)] : List FactorBlock).map factorBlockValue).prod) = 169683578465165879327768351 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_5
      · exact prime_oneHundredTwentyThreeDQ_31
      · exact prime_oneHundredTwentyThreeDQ_105601
      · exact prime_oneHundredTwentyThreeDQ_1036668937123126457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 169683578465165879327768351) ^ 84841789232582939663884175 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (17 : ZMod 169683578465165879327768351) ^ 33936715693033175865553670 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (17 : ZMod 169683578465165879327768351) ^ 5473663821456963849282850 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (17 : ZMod 169683578465165879327768351) ^ 1606836852540846008350 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (17 : ZMod 169683578465165879327768351) ^ 163681550 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_268796352577906023260438959 : Nat.Prime 268796352577906023260438959 := by
  apply lucas_primality 268796352577906023260438959 (6 : ZMod 268796352577906023260438959)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (13, 2), (37663, 1), (1005477753206977117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (13, 2), (37663, 1), (1005477753206977117, 1)] : List FactorBlock).map factorBlockValue).prod) = 268796352577906023260438959 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_7
      · exact prime_oneHundredTwentyThreeDQ_13
      · exact prime_oneHundredTwentyThreeDQ_37663
      · exact prime_oneHundredTwentyThreeDQ_1005477753206977117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 268796352577906023260438959) ^ 134398176288953011630219479 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (6 : ZMod 268796352577906023260438959) ^ 89598784192635341086812986 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (6 : ZMod 268796352577906023260438959) ^ 38399478939700860465776994 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (6 : ZMod 268796352577906023260438959) ^ 20676642505992771020033766 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (6 : ZMod 268796352577906023260438959) ^ 7136881092263123576466 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (6 : ZMod 268796352577906023260438959) ^ 267331974 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_285695140952155517846556929 : Nat.Prime 285695140952155517846556929 := by
  apply lucas_primality 285695140952155517846556929 (3 : ZMod 285695140952155517846556929)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (97, 1), (359, 1), (33546529, 1), (955320538439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (97, 1), (359, 1), (33546529, 1), (955320538439, 1)] : List FactorBlock).map factorBlockValue).prod) = 285695140952155517846556929 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_97
      · exact prime_oneHundredTwentyThreeDQ_359
      · exact prime_oneHundredTwentyThreeDQ_33546529
      · exact prime_oneHundredTwentyThreeDQ_955320538439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 285695140952155517846556929) ^ 142847570476077758923278464 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 285695140952155517846556929) ^ 2945310731465520802541824 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 285695140952155517846556929) ^ 795808192067285565032192 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 285695140952155517846556929) ^ 8516384540175692032 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 285695140952155517846556929) ^ 299056839517952 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_492945175405583588419991447 : Nat.Prime 492945175405583588419991447 := by
  apply lucas_primality 492945175405583588419991447 (5 : ZMod 492945175405583588419991447)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (17, 1), (31, 1), (5295791, 1), (8028501394952449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (17, 1), (31, 1), (5295791, 1), (8028501394952449, 1)] : List FactorBlock).map factorBlockValue).prod) = 492945175405583588419991447 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_11
      · exact prime_oneHundredTwentyThreeDQ_17
      · exact prime_oneHundredTwentyThreeDQ_31
      · exact prime_oneHundredTwentyThreeDQ_5295791
      · exact prime_oneHundredTwentyThreeDQ_8028501394952449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 492945175405583588419991447) ^ 246472587702791794209995723 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 492945175405583588419991447) ^ 44813197764143962583635586 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 492945175405583588419991447) ^ 28996775023857858142352438 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 492945175405583588419991447) ^ 15901457271147857690967466 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 492945175405583588419991447) ^ 93082445173078693706 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 492945175405583588419991447) ^ 61399400854 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_572515065923807710960226287 : Nat.Prime 572515065923807710960226287 := by
  apply lucas_primality 572515065923807710960226287 (3 : ZMod 572515065923807710960226287)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (47, 1), (2267, 1), (2384831, 1), (19764010775021, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (47, 1), (2267, 1), (2384831, 1), (19764010775021, 1)] : List FactorBlock).map factorBlockValue).prod) = 572515065923807710960226287 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_19
      · exact prime_oneHundredTwentyThreeDQ_47
      · exact prime_oneHundredTwentyThreeDQ_2267
      · exact prime_oneHundredTwentyThreeDQ_2384831
      · exact prime_oneHundredTwentyThreeDQ_19764010775021
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 572515065923807710960226287) ^ 286257532961903855480113143 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 572515065923807710960226287) ^ 190838355307935903653408762 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 572515065923807710960226287) ^ 30132371890726721629485594 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 572515065923807710960226287) ^ 12181171615400164062983538 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 572515065923807710960226287) ^ 252543037460876802364458 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 572515065923807710960226287) ^ 240065256583719228306 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 572515065923807710960226287) ^ 28967554836966 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_1154117672576564750665852991 : Nat.Prime 1154117672576564750665852991 := by
  apply lucas_primality 1154117672576564750665852991 (14 : ZMod 1154117672576564750665852991)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 2), (17, 1), (97, 1), (1694450239, 1), (842955281741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 2), (17, 1), (97, 1), (1694450239, 1), (842955281741, 1)] : List FactorBlock).map factorBlockValue).prod) = 1154117672576564750665852991 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_5
      · exact prime_oneHundredTwentyThreeDQ_7
      · exact prime_oneHundredTwentyThreeDQ_17
      · exact prime_oneHundredTwentyThreeDQ_97
      · exact prime_oneHundredTwentyThreeDQ_1694450239
      · exact prime_oneHundredTwentyThreeDQ_842955281741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 1154117672576564750665852991) ^ 577058836288282375332926495 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (14 : ZMod 1154117672576564750665852991) ^ 230823534515312950133170598 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (14 : ZMod 1154117672576564750665852991) ^ 164873953225223535809407570 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (14 : ZMod 1154117672576564750665852991) ^ 67889274857444985333285470 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (14 : ZMod 1154117672576564750665852991) ^ 11898120335840873718204670 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (14 : ZMod 1154117672576564750665852991) ^ 681116297199545410 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (14 : ZMod 1154117672576564750665852991) ^ 1369132737614390 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_2077411810637816551198535383 : Nat.Prime 2077411810637816551198535383 := by
  apply lucas_primality 2077411810637816551198535383 (3 : ZMod 2077411810637816551198535383)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 2), (17, 1), (97, 1), (1694450239, 1), (842955281741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 2), (17, 1), (97, 1), (1694450239, 1), (842955281741, 1)] : List FactorBlock).map factorBlockValue).prod) = 2077411810637816551198535383 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_7
      · exact prime_oneHundredTwentyThreeDQ_17
      · exact prime_oneHundredTwentyThreeDQ_97
      · exact prime_oneHundredTwentyThreeDQ_1694450239
      · exact prime_oneHundredTwentyThreeDQ_842955281741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2077411810637816551198535383) ^ 1038705905318908275599267691 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 2077411810637816551198535383) ^ 692470603545938850399511794 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 2077411810637816551198535383) ^ 296773115805402364456933626 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 2077411810637816551198535383) ^ 122200694743400973599913846 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 2077411810637816551198535383) ^ 21416616604513572692768406 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 2077411810637816551198535383) ^ 1226009334959181738 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (3 : ZMod 2077411810637816551198535383) ^ 2464438927705902 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_5193529526594541377996338459 : Nat.Prime 5193529526594541377996338459 := by
  apply lucas_primality 5193529526594541377996338459 (2 : ZMod 5193529526594541377996338459)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (29, 1), (337, 1), (13963, 1), (487934319167696389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (29, 1), (337, 1), (13963, 1), (487934319167696389, 1)] : List FactorBlock).map factorBlockValue).prod) = 5193529526594541377996338459 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_13
      · exact prime_oneHundredTwentyThreeDQ_29
      · exact prime_oneHundredTwentyThreeDQ_337
      · exact prime_oneHundredTwentyThreeDQ_13963
      · exact prime_oneHundredTwentyThreeDQ_487934319167696389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5193529526594541377996338459) ^ 2596764763297270688998169229 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 5193529526594541377996338459) ^ 1731176508864847125998779486 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 5193529526594541377996338459) ^ 399502271276503182922795266 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 5193529526594541377996338459) ^ 179087225054984185448149602 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 5193529526594541377996338459) ^ 15411066844494188065271034 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 5193529526594541377996338459) ^ 371949403895619951156366 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 5193529526594541377996338459) ^ 10643911122 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_9088676671540447411493592301 : Nat.Prime 9088676671540447411493592301 := by
  apply lucas_primality 9088676671540447411493592301 (18 : ZMod 9088676671540447411493592301)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (41, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (41, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 9088676671540447411493592301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_5
      · exact prime_oneHundredTwentyThreeDQ_41
      · exact prime_oneHundredTwentyThreeDQ_171401
      · exact prime_oneHundredTwentyThreeDQ_714027719
      · exact prime_oneHundredTwentyThreeDQ_6037638679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (18 : ZMod 9088676671540447411493592301) ^ 4544338335770223705746796150 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (18 : ZMod 9088676671540447411493592301) ^ 3029558890513482470497864100 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (18 : ZMod 9088676671540447411493592301) ^ 1817735334308089482298718460 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (18 : ZMod 9088676671540447411493592301) ^ 221675040769279205158380300 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (18 : ZMod 9088676671540447411493592301) ^ 53025808901584281372300 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (18 : ZMod 9088676671540447411493592301) ^ 12728744878797131700 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (18 : ZMod 9088676671540447411493592301) ^ 1505336300291123700 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_11186063595742089121838267447 : Nat.Prime 11186063595742089121838267447 := by
  apply lucas_primality 11186063595742089121838267447 (5 : ZMod 11186063595742089121838267447)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (241, 1), (1430499735023, 1), (16223421964261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (241, 1), (1430499735023, 1), (16223421964261, 1)] : List FactorBlock).map factorBlockValue).prod) = 11186063595742089121838267447 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_241
      · exact prime_oneHundredTwentyThreeDQ_1430499735023
      · exact prime_oneHundredTwentyThreeDQ_16223421964261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 11186063595742089121838267447) ^ 5593031797871044560919133723 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 11186063595742089121838267447) ^ 46415201642083357352026006 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 11186063595742089121838267447) ^ 7819689386773802 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 11186063595742089121838267447) ^ 689500872281086 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_29083765348929431716779495379 : Nat.Prime 29083765348929431716779495379 := by
  apply lucas_primality 29083765348929431716779495379 (2 : ZMod 29083765348929431716779495379)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (6907, 1), (27061, 1), (25933795647479510069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (6907, 1), (27061, 1), (25933795647479510069, 1)] : List FactorBlock).map factorBlockValue).prod) = 29083765348929431716779495379 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_6907
      · exact prime_oneHundredTwentyThreeDQ_27061
      · exact prime_oneHundredTwentyThreeDQ_25933795647479510069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 29083765348929431716779495379) ^ 14541882674464715858389747689 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 29083765348929431716779495379) ^ 9694588449643143905593165126 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 29083765348929431716779495379) ^ 4210766664098658131863254 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 29083765348929431716779495379) ^ 1074748359222845856279498 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (2 : ZMod 29083765348929431716779495379) ^ 1121461962 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_36354706686161789645974369223 : Nat.Prime 36354706686161789645974369223 := by
  apply lucas_primality 36354706686161789645974369223 (5 : ZMod 36354706686161789645974369223)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (149, 1), (251, 1), (486038486138155962003989, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (149, 1), (251, 1), (486038486138155962003989, 1)] : List FactorBlock).map factorBlockValue).prod) = 36354706686161789645974369223 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_149
      · exact prime_oneHundredTwentyThreeDQ_251
      · exact prime_oneHundredTwentyThreeDQ_486038486138155962003989
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 36354706686161789645974369223) ^ 18177353343080894822987184611 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 36354706686161789645974369223) ^ 243991320041354292926002478 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 36354706686161789645974369223) ^ 144839468869170476677188722 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (5 : ZMod 36354706686161789645974369223) ^ 74798 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyThreeDQ_72709413372323579291948738431 : Nat.Prime 72709413372323579291948738431 := by
  apply lucas_primality 72709413372323579291948738431 (11 : ZMod 72709413372323579291948738431)
  · rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (3137, 1), (23027, 1), (33551929945480087019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (3137, 1), (23027, 1), (33551929945480087019, 1)] : List FactorBlock).map factorBlockValue).prod) = 72709413372323579291948738431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyThreeDQ_2
      · exact prime_oneHundredTwentyThreeDQ_3
      · exact prime_oneHundredTwentyThreeDQ_5
      · exact prime_oneHundredTwentyThreeDQ_3137
      · exact prime_oneHundredTwentyThreeDQ_23027
      · exact prime_oneHundredTwentyThreeDQ_33551929945480087019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 72709413372323579291948738431) ^ 36354706686161789645974369215 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (11 : ZMod 72709413372323579291948738431) ^ 24236471124107859763982912810 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (11 : ZMod 72709413372323579291948738431) ^ 14541882674464715858389747686 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (11 : ZMod 72709413372323579291948738431) ^ 23178008725637098913595390 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (11 : ZMod 72709413372323579291948738431) ^ 3157572127169130989358090 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide
    · change (11 : ZMod 72709413372323579291948738431) ^ 2167070970 ≠ 1
      rw [← oneHundredTwentyThreeDQFastPow_eq_pow]
      decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476800 : Nat.totient 145418826744647158583897476800 = 37832319506721499351326720000 := by
  rw [← show ((([(2, 6), (3, 1), (5, 2), (41, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476800 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_2, prime_oneHundredTwentyThreeDQ_3, prime_oneHundredTwentyThreeDQ_5, prime_oneHundredTwentyThreeDQ_41, prime_oneHundredTwentyThreeDQ_171401, prime_oneHundredTwentyThreeDQ_714027719, prime_oneHundredTwentyThreeDQ_6037638679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476801 : Nat.totient 145418826744647158583897476801 = 129330784556734926230251280640 := by
  rw [← show ((([(11, 1), (53, 1), (373, 1), (4957, 1), (134903845900098415927, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476801 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_11, prime_oneHundredTwentyThreeDQ_53, prime_oneHundredTwentyThreeDQ_373, prime_oneHundredTwentyThreeDQ_4957, prime_oneHundredTwentyThreeDQ_134903845900098415927]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476802 : Nat.totient 145418826744647158583897476802 = 72615735949183349518533574656 := by
  rw [← show ((([(2, 1), (907, 1), (5417, 1), (752833, 1), (8493257, 1), (2314470259, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476802 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_2, prime_oneHundredTwentyThreeDQ_907, prime_oneHundredTwentyThreeDQ_5417, prime_oneHundredTwentyThreeDQ_752833, prime_oneHundredTwentyThreeDQ_8493257, prime_oneHundredTwentyThreeDQ_2314470259]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476803 : Nat.totient 145418826744647158583897476803 = 83096409789335435966040352896 := by
  rw [← show ((([(3, 4), (7, 1), (1326653, 1), (193321534648399602553, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476803 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_3, prime_oneHundredTwentyThreeDQ_7, prime_oneHundredTwentyThreeDQ_1326653, prime_oneHundredTwentyThreeDQ_193321534648399602553]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476804 : Nat.totient 145418826744647158583897476804 = 70744266735333573215119397760 := by
  rw [← show ((([(2, 2), (37, 1), (2607469, 1), (314147747, 1), (1199515371611, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476804 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_2, prime_oneHundredTwentyThreeDQ_37, prime_oneHundredTwentyThreeDQ_2607469, prime_oneHundredTwentyThreeDQ_314147747, prime_oneHundredTwentyThreeDQ_1199515371611]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476805 : Nat.totient 145418826744647158583897476805 = 116170978073921642755598764032 := by
  rw [← show ((([(5, 1), (709, 1), (5986848097, 1), (6851823352338157, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476805 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_5, prime_oneHundredTwentyThreeDQ_709, prime_oneHundredTwentyThreeDQ_5986848097, prime_oneHundredTwentyThreeDQ_6851823352338157]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476806 : Nat.totient 145418826744647158583897476806 = 47623869294301044541197753216 := by
  rw [← show ((([(2, 1), (3, 1), (59, 1), (1733, 1), (39668467, 1), (5975488216114349, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476806 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_2, prime_oneHundredTwentyThreeDQ_3, prime_oneHundredTwentyThreeDQ_59, prime_oneHundredTwentyThreeDQ_1733, prime_oneHundredTwentyThreeDQ_39668467, prime_oneHundredTwentyThreeDQ_5975488216114349]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476807 : Nat.totient 145418826744647158583897476807 = 145249143166181992704569707600 := by
  rw [← show ((([(857, 1), (169683578465165879327768351, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476807 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_857, prime_oneHundredTwentyThreeDQ_169683578465165879327768351]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476808 : Nat.totient 145418826744647158583897476808 = 68427385569490602164995261440 := by
  rw [← show ((([(2, 3), (17, 1), (25867, 1), (29021, 1), (1424371553698679479, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476808 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_2, prime_oneHundredTwentyThreeDQ_17, prime_oneHundredTwentyThreeDQ_25867, prime_oneHundredTwentyThreeDQ_29021, prime_oneHundredTwentyThreeDQ_1424371553698679479]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476809 : Nat.totient 145418826744647158583897476809 = 96941550516081060875445490176 := by
  rw [← show ((([(3, 1), (22369, 1), (2352041639, 1), (921314287658533, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476809 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_3, prime_oneHundredTwentyThreeDQ_22369, prime_oneHundredTwentyThreeDQ_2352041639, prime_oneHundredTwentyThreeDQ_921314287658533]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476810 : Nat.totient 145418826744647158583897476810 = 49857883455307597228764849168 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (2077411810637816551198535383, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476810 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_2, prime_oneHundredTwentyThreeDQ_5, prime_oneHundredTwentyThreeDQ_7, prime_oneHundredTwentyThreeDQ_2077411810637816551198535383]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476811 : Nat.totient 145418826744647158583897476811 = 134232763148905069462059209352 := by
  rw [← show ((([(13, 1), (11186063595742089121838267447, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476811 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_13, prime_oneHundredTwentyThreeDQ_11186063595742089121838267447]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476812 : Nat.totient 145418826744647158583897476812 = 43405145318399076227757392640 := by
  rw [← show ((([(2, 2), (3, 2), (11, 1), (67, 1), (12547, 1), (436828283214730158953, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476812 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_2, prime_oneHundredTwentyThreeDQ_3, prime_oneHundredTwentyThreeDQ_11, prime_oneHundredTwentyThreeDQ_67, prime_oneHundredTwentyThreeDQ_12547, prime_oneHundredTwentyThreeDQ_436828283214730158953]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476813 : Nat.totient 145418826744647158583897476813 = 145416811879992167837238904960 := by
  rw [← show ((([(72173, 1), (2014864654990746658499681, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476813 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_72173, prime_oneHundredTwentyThreeDQ_2014864654990746658499681]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476814 : Nat.totient 145418826744647158583897476814 = 72709413310384649756679310056 := by
  rw [← show ((([(2, 1), (1173888763, 1), (61938929534095539589, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476814 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_2, prime_oneHundredTwentyThreeDQ_1173888763, prime_oneHundredTwentyThreeDQ_61938929534095539589]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476815 : Nat.totient 145418826744647158583897476815 = 71068727784699485501257175040 := by
  rw [← show ((([(3, 1), (5, 1), (19, 1), (43, 1), (103, 1), (164627, 1), (498521, 1), (1403736441413, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476815 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_3, prime_oneHundredTwentyThreeDQ_5, prime_oneHundredTwentyThreeDQ_19, prime_oneHundredTwentyThreeDQ_43, prime_oneHundredTwentyThreeDQ_103, prime_oneHundredTwentyThreeDQ_164627, prime_oneHundredTwentyThreeDQ_498521, prime_oneHundredTwentyThreeDQ_1403736441413]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476816 : Nat.totient 145418826744647158583897476816 = 72709413372323579291948738400 := by
  rw [← show ((([(2, 4), (9088676671540447411493592301, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476816 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_2, prime_oneHundredTwentyThreeDQ_9088676671540447411493592301]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476817 : Nat.totient 145418826744647158583897476817 = 124644708596960567850173642352 := by
  rw [← show ((([(7, 1), (3017416133, 1), (6884737533938997307, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476817 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_7, prime_oneHundredTwentyThreeDQ_3017416133, prime_oneHundredTwentyThreeDQ_6884737533938997307]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476818 : Nat.totient 145418826744647158583897476818 = 46909279719254556667297296000 := by
  rw [← show ((([(2, 1), (3, 1), (31, 1), (2439301, 1), (320510527058681839513, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476818 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_2, prime_oneHundredTwentyThreeDQ_3, prime_oneHundredTwentyThreeDQ_31, prime_oneHundredTwentyThreeDQ_2439301, prime_oneHundredTwentyThreeDQ_320510527058681839513]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476819 : Nat.totient 145418826744647158583897476819 = 145150030392069252560637037320 := by
  rw [← show ((([(541, 1), (268796352577906023260438959, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476819 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_541, prime_oneHundredTwentyThreeDQ_268796352577906023260438959]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476820 : Nat.totient 145418826744647158583897476820 = 57091450777705913833439308800 := by
  rw [← show ((([(2, 2), (5, 1), (61, 1), (467, 1), (277740317081, 1), (918977753503, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476820 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_2, prime_oneHundredTwentyThreeDQ_5, prime_oneHundredTwentyThreeDQ_61, prime_oneHundredTwentyThreeDQ_467, prime_oneHundredTwentyThreeDQ_277740317081, prime_oneHundredTwentyThreeDQ_918977753503]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476821 : Nat.totient 145418826744647158583897476821 = 96945884422408721825496290664 := by
  rw [← show ((([(3, 2), (1309677463, 1), (12337119537096215963, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476821 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_3, prime_oneHundredTwentyThreeDQ_1309677463, prime_oneHundredTwentyThreeDQ_12337119537096215963]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476822 : Nat.totient 145418826744647158583897476822 = 69547877978400679168158244320 := by
  rw [← show ((([(2, 1), (23, 1), (271211, 1), (598922059, 1), (19461898163093, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476822 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_2, prime_oneHundredTwentyThreeDQ_23, prime_oneHundredTwentyThreeDQ_271211, prime_oneHundredTwentyThreeDQ_598922059, prime_oneHundredTwentyThreeDQ_19461898163093]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476823 : Nat.totient 145418826744647158583897476823 = 132129610418695468494498045880 := by
  rw [← show ((([(11, 1), (1907, 1), (6932298552922112722691399, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476823 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_11, prime_oneHundredTwentyThreeDQ_1907, prime_oneHundredTwentyThreeDQ_6932298552922112722691399]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476824 : Nat.totient 145418826744647158583897476824 = 36917203147416517551414018048 := by
  rw [← show ((([(2, 3), (3, 1), (7, 1), (13, 1), (29, 1), (337, 1), (13963, 1), (487934319167696389, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476824 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_2, prime_oneHundredTwentyThreeDQ_3, prime_oneHundredTwentyThreeDQ_7, prime_oneHundredTwentyThreeDQ_13, prime_oneHundredTwentyThreeDQ_29, prime_oneHundredTwentyThreeDQ_337, prime_oneHundredTwentyThreeDQ_13963, prime_oneHundredTwentyThreeDQ_487934319167696389]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476825 : Nat.totient 145418826744647158583897476825 = 109439258004974412397204558080 := by
  rw [← show ((([(5, 2), (17, 1), (2083, 1), (164264015977687338492443, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476825 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_5, prime_oneHundredTwentyThreeDQ_17, prime_oneHundredTwentyThreeDQ_2083, prime_oneHundredTwentyThreeDQ_164264015977687338492443]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476826 : Nat.totient 145418826744647158583897476826 = 72709076158052268766425132000 := by
  rw [← show ((([(2, 1), (216071, 1), (102808553, 1), (3273142492240051, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476826 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_2, prime_oneHundredTwentyThreeDQ_216071, prime_oneHundredTwentyThreeDQ_102808553, prime_oneHundredTwentyThreeDQ_3273142492240051]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476827 : Nat.totient 145418826744647158583897476827 = 96945884496429506044308647208 := by
  rw [← show ((([(3, 1), (53066401233983, 1), (913439410268023, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476827 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_3, prime_oneHundredTwentyThreeDQ_53066401233983, prime_oneHundredTwentyThreeDQ_913439410268023]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476828 : Nat.totient 145418826744647158583897476828 = 71780088280327554120324851520 := by
  rw [← show ((([(2, 2), (79, 1), (8191, 1), (381019, 1), (147451771633535077, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476828 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_2, prime_oneHundredTwentyThreeDQ_79, prime_oneHundredTwentyThreeDQ_8191, prime_oneHundredTwentyThreeDQ_381019, prime_oneHundredTwentyThreeDQ_147451771633535077]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476829 : Nat.totient 145418826744647158583897476829 = 145386561639977833720666077276 := by
  rw [← show ((([(4507, 1), (32265104669324863231395047, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476829 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_4507, prime_oneHundredTwentyThreeDQ_32265104669324863231395047]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476830 : Nat.totient 145418826744647158583897476830 = 38760875123130601061745623040 := by
  rw [← show ((([(2, 1), (3, 3), (5, 1), (2221, 1), (2096209, 1), (140866157, 1), (821234273, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476830 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_2, prime_oneHundredTwentyThreeDQ_3, prime_oneHundredTwentyThreeDQ_5, prime_oneHundredTwentyThreeDQ_2221, prime_oneHundredTwentyThreeDQ_2096209, prime_oneHundredTwentyThreeDQ_140866157, prime_oneHundredTwentyThreeDQ_821234273]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476831 : Nat.totient 145418826744647158583897476831 = 124644684967886249946601618200 := by
  rw [← show ((([(7, 1), (5265851, 1), (3945063790520879818283, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476831 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_7, prime_oneHundredTwentyThreeDQ_5265851, prime_oneHundredTwentyThreeDQ_3945063790520879818283]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476832 : Nat.totient 145418826744647158583897476832 = 71161891028538970762681283584 := by
  rw [← show ((([(2, 5), (47, 1), (139943, 1), (14123063, 1), (48920706901337, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476832 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_2, prime_oneHundredTwentyThreeDQ_47, prime_oneHundredTwentyThreeDQ_139943, prime_oneHundredTwentyThreeDQ_14123063, prime_oneHundredTwentyThreeDQ_48920706901337]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476833 : Nat.totient 145418826744647158583897476833 = 96323292108109198449967104000 := by
  rw [← show ((([(3, 1), (281, 1), (349, 1), (125711, 1), (3248689, 1), (1210281000961, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476833 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_3, prime_oneHundredTwentyThreeDQ_281, prime_oneHundredTwentyThreeDQ_349, prime_oneHundredTwentyThreeDQ_125711, prime_oneHundredTwentyThreeDQ_3248689, prime_oneHundredTwentyThreeDQ_1210281000961]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476834 : Nat.totient 145418826744647158583897476834 = 62032012575135099417375436800 := by
  rw [← show ((([(2, 1), (11, 1), (19, 1), (109, 1), (4421, 1), (721933744101063946817, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476834 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_2, prime_oneHundredTwentyThreeDQ_11, prime_oneHundredTwentyThreeDQ_19, prime_oneHundredTwentyThreeDQ_109, prime_oneHundredTwentyThreeDQ_4421, prime_oneHundredTwentyThreeDQ_721933744101063946817]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476835 : Nat.totient 145418826744647158583897476835 = 114540771323111433289770457728 := by
  rw [← show ((([(5, 1), (107, 1), (163, 1), (24469429, 1), (68148360928716203, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476835 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_5, prime_oneHundredTwentyThreeDQ_107, prime_oneHundredTwentyThreeDQ_163, prime_oneHundredTwentyThreeDQ_24469429, prime_oneHundredTwentyThreeDQ_68148360928716203]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476836 : Nat.totient 145418826744647158583897476836 = 48472856712911832265157373600 := by
  rw [← show ((([(2, 2), (3, 1), (566701, 1), (21383825971815701546303, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476836 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_2, prime_oneHundredTwentyThreeDQ_3, prime_oneHundredTwentyThreeDQ_566701, prime_oneHundredTwentyThreeDQ_21383825971815701546303]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476837 : Nat.totient 145418826744647158583897476837 = 132343783253580323395663939584 := by
  rw [← show ((([(13, 1), (97, 1), (263, 1), (16538827, 1), (26512159077345917, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476837 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_13, prime_oneHundredTwentyThreeDQ_97, prime_oneHundredTwentyThreeDQ_263, prime_oneHundredTwentyThreeDQ_16538827, prime_oneHundredTwentyThreeDQ_26512159077345917]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476838 : Nat.totient 145418826744647158583897476838 = 61366687727454317697102028800 := by
  rw [← show ((([(2, 1), (7, 2), (73, 1), (991, 1), (1979, 1), (8707, 1), (33521, 1), (35511313909, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476838 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_2, prime_oneHundredTwentyThreeDQ_7, prime_oneHundredTwentyThreeDQ_73, prime_oneHundredTwentyThreeDQ_991, prime_oneHundredTwentyThreeDQ_1979, prime_oneHundredTwentyThreeDQ_8707, prime_oneHundredTwentyThreeDQ_33521, prime_oneHundredTwentyThreeDQ_35511313909]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476839 : Nat.totient 145418826744647158583897476839 = 96945884496325421637021328464 := by
  rw [← show ((([(3, 2), (914480876299, 1), (17668655337510829, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476839 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_3, prime_oneHundredTwentyThreeDQ_914480876299, prime_oneHundredTwentyThreeDQ_17668655337510829]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476840 : Nat.totient 145418826744647158583897476840 = 57891796306620615633938761728 := by
  rw [← show ((([(2, 3), (5, 1), (233, 1), (2237, 1), (293179, 1), (23790626604074719, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476840 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_2, prime_oneHundredTwentyThreeDQ_5, prime_oneHundredTwentyThreeDQ_233, prime_oneHundredTwentyThreeDQ_2237, prime_oneHundredTwentyThreeDQ_293179, prime_oneHundredTwentyThreeDQ_23790626604074719]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476841 : Nat.totient 145418826744647158583897476841 = 138033219461306834335043589120 := by
  rw [← show ((([(37, 1), (41, 1), (31177, 1), (3074685732733041494149, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476841 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_37, prime_oneHundredTwentyThreeDQ_41, prime_oneHundredTwentyThreeDQ_31177, prime_oneHundredTwentyThreeDQ_3074685732733041494149]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476842 : Nat.totient 145418826744647158583897476842 = 45601644478272027507262923264 := by
  rw [← show ((([(2, 1), (3, 1), (17, 1), (2287, 1), (623382060343832397026233, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476842 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_2, prime_oneHundredTwentyThreeDQ_3, prime_oneHundredTwentyThreeDQ_17, prime_oneHundredTwentyThreeDQ_2287, prime_oneHundredTwentyThreeDQ_623382060343832397026233]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476843 : Nat.totient 145418826744647158583897476843 = 144882224797749825773944477800 := by
  rw [← show ((([(271, 1), (130500871, 1), (4111856362216271923, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476843 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_271, prime_oneHundredTwentyThreeDQ_130500871, prime_oneHundredTwentyThreeDQ_4111856362216271923]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476844 : Nat.totient 145418826744647158583897476844 = 72302262226606108483551116352 := by
  rw [← show ((([(2, 2), (227, 1), (1427, 1), (2003, 1), (33374239, 1), (1678875508927, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476844 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_2, prime_oneHundredTwentyThreeDQ_227, prime_oneHundredTwentyThreeDQ_1427, prime_oneHundredTwentyThreeDQ_2003, prime_oneHundredTwentyThreeDQ_33374239, prime_oneHundredTwentyThreeDQ_1678875508927]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476845 : Nat.totient 145418826744647158583897476845 = 57806241687313156207263477120 := by
  rw [← show ((([(3, 1), (5, 1), (7, 1), (11, 2), (23, 1), (497643265214472763492283, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476845 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_3, prime_oneHundredTwentyThreeDQ_5, prime_oneHundredTwentyThreeDQ_7, prime_oneHundredTwentyThreeDQ_11, prime_oneHundredTwentyThreeDQ_23, prime_oneHundredTwentyThreeDQ_497643265214472763492283]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476846 : Nat.totient 145418826744647158583897476846 = 72709408814901137392515837120 := by
  rw [← show ((([(2, 1), (15975769, 1), (12122507941, 1), (375436412387, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476846 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_2, prime_oneHundredTwentyThreeDQ_15975769, prime_oneHundredTwentyThreeDQ_12122507941, prime_oneHundredTwentyThreeDQ_375436412387]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476847 : Nat.totient 145418826744647158583897476847 = 143364496881238997225489752320 := by
  rw [← show ((([(71, 1), (23209, 1), (88248200670482467391473, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476847 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_71, prime_oneHundredTwentyThreeDQ_23209, prime_oneHundredTwentyThreeDQ_88248200670482467391473]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476848 : Nat.totient 145418826744647158583897476848 = 48472939015893455405551119360 := by
  rw [← show ((([(2, 4), (3, 2), (14996321, 1), (67340047169201976727, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476848 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_2, prime_oneHundredTwentyThreeDQ_3, prime_oneHundredTwentyThreeDQ_14996321, prime_oneHundredTwentyThreeDQ_67340047169201976727]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476849 : Nat.totient 145418826744647158583897476849 = 140727896281697133316306241280 := by
  rw [← show ((([(31, 1), (247777217, 1), (18932046908044083887, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476849 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_31, prime_oneHundredTwentyThreeDQ_247777217, prime_oneHundredTwentyThreeDQ_18932046908044083887]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476850 : Nat.totient 145418826744647158583897476850 = 53693105259543383317598295360 := by
  rw [← show ((([(2, 1), (5, 2), (13, 1), (2995333119683, 1), (74689946986103, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476850 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_2, prime_oneHundredTwentyThreeDQ_5, prime_oneHundredTwentyThreeDQ_13, prime_oneHundredTwentyThreeDQ_2995333119683, prime_oneHundredTwentyThreeDQ_74689946986103]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476851 : Nat.totient 145418826744647158583897476851 = 96168245403091350821568768000 := by
  rw [← show ((([(3, 1), (139, 1), (1201, 1), (2070643, 1), (140228518397647921, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476851 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_3, prime_oneHundredTwentyThreeDQ_139, prime_oneHundredTwentyThreeDQ_1201, prime_oneHundredTwentyThreeDQ_2070643, prime_oneHundredTwentyThreeDQ_140228518397647921]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476852 : Nat.totient 145418826744647158583897476852 = 62322354319134496535956061496 := by
  rw [← show ((([(2, 2), (7, 1), (5193529526594541377996338459, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476852 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_2, prime_oneHundredTwentyThreeDQ_7, prime_oneHundredTwentyThreeDQ_5193529526594541377996338459]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476853 : Nat.totient 145418826744647158583897476853 = 132961648904983551860373374208 := by
  rw [← show ((([(19, 1), (29, 1), (2699, 1), (35509, 1), (37058327, 1), (74309082979, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476853 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_19, prime_oneHundredTwentyThreeDQ_29, prime_oneHundredTwentyThreeDQ_2699, prime_oneHundredTwentyThreeDQ_35509, prime_oneHundredTwentyThreeDQ_37058327, prime_oneHundredTwentyThreeDQ_74309082979]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476854 : Nat.totient 145418826744647158583897476854 = 47445555213814747776020507520 := by
  rw [← show ((([(2, 1), (3, 1), (53, 1), (811, 1), (877, 1), (642943883070206397899, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476854 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_2, prime_oneHundredTwentyThreeDQ_3, prime_oneHundredTwentyThreeDQ_53, prime_oneHundredTwentyThreeDQ_811, prime_oneHundredTwentyThreeDQ_877, prime_oneHundredTwentyThreeDQ_642943883070206397899]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476855 : Nat.totient 145418826744647158583897476855 = 116281227494100087937517270400 := by
  rw [← show ((([(5, 1), (2161, 1), (13458475404409732400175611, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476855 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_5, prime_oneHundredTwentyThreeDQ_2161, prime_oneHundredTwentyThreeDQ_13458475404409732400175611]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476856 : Nat.totient 145418826744647158583897476856 = 65724619864623129371372382720 := by
  rw [← show ((([(2, 3), (11, 1), (229, 1), (967, 1), (3623, 1), (287948027, 1), (7153087979, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476856 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_2, prime_oneHundredTwentyThreeDQ_11, prime_oneHundredTwentyThreeDQ_229, prime_oneHundredTwentyThreeDQ_967, prime_oneHundredTwentyThreeDQ_3623, prime_oneHundredTwentyThreeDQ_287948027, prime_oneHundredTwentyThreeDQ_7153087979]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476857 : Nat.totient 145418826744647158583897476857 = 96944404917335779781685981504 := by
  rw [← show ((([(3, 3), (108739, 1), (166189, 1), (20697107, 1), (14399904703, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476857 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_3, prime_oneHundredTwentyThreeDQ_108739, prime_oneHundredTwentyThreeDQ_166189, prime_oneHundredTwentyThreeDQ_20697107, prime_oneHundredTwentyThreeDQ_14399904703]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476858 : Nat.totient 145418826744647158583897476858 = 71017501950176308485544128816 := by
  rw [← show ((([(2, 1), (43, 1), (71443, 1), (91761259, 1), (257930760457319, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476858 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_2, prime_oneHundredTwentyThreeDQ_43, prime_oneHundredTwentyThreeDQ_71443, prime_oneHundredTwentyThreeDQ_91761259, prime_oneHundredTwentyThreeDQ_257930760457319]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476859 : Nat.totient 145418826744647158583897476859 = 115749134491181039512215552000 := by
  rw [← show ((([(7, 1), (17, 1), (131, 1), (179, 1), (6701, 1), (317353, 1), (24505700548913, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476859 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_7, prime_oneHundredTwentyThreeDQ_17, prime_oneHundredTwentyThreeDQ_131, prime_oneHundredTwentyThreeDQ_179, prime_oneHundredTwentyThreeDQ_6701, prime_oneHundredTwentyThreeDQ_317353, prime_oneHundredTwentyThreeDQ_24505700548913]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476860 : Nat.totient 145418826744647158583897476860 = 38764308692281958092950458368 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (3137, 1), (23027, 1), (33551929945480087019, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476860 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_2, prime_oneHundredTwentyThreeDQ_3, prime_oneHundredTwentyThreeDQ_5, prime_oneHundredTwentyThreeDQ_3137, prime_oneHundredTwentyThreeDQ_23027, prime_oneHundredTwentyThreeDQ_33551929945480087019]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476861 : Nat.totient 145418826744647158583897476861 = 145133131603695003066050919424 := by
  rw [← show ((([(509, 1), (285695140952155517846556929, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476861 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_509, prime_oneHundredTwentyThreeDQ_285695140952155517846556929]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476862 : Nat.totient 145418826744647158583897476862 = 72709413372323579291948738430 := by
  rw [← show ((([(2, 1), (72709413372323579291948738431, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476862 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_2, prime_oneHundredTwentyThreeDQ_72709413372323579291948738431]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476863 : Nat.totient 145418826744647158583897476863 = 88825151537332519283458283520 := by
  rw [← show ((([(3, 1), (13, 1), (137, 1), (10139, 1), (63689, 1), (42147896915954971, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476863 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_3, prime_oneHundredTwentyThreeDQ_13, prime_oneHundredTwentyThreeDQ_137, prime_oneHundredTwentyThreeDQ_10139, prime_oneHundredTwentyThreeDQ_63689, prime_oneHundredTwentyThreeDQ_42147896915954971]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476864 : Nat.totient 145418826744647158583897476864 = 72528093139474892061794201600 := by
  rw [← show ((([(2, 8), (401, 1), (1416564319130368985581919, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476864 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_2, prime_oneHundredTwentyThreeDQ_401, prime_oneHundredTwentyThreeDQ_1416564319130368985581919]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476865 : Nat.totient 145418826744647158583897476865 = 114363280694095392513438015472 := by
  rw [← show ((([(5, 1), (59, 1), (492945175405583588419991447, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476865 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_5, prime_oneHundredTwentyThreeDQ_59, prime_oneHundredTwentyThreeDQ_492945175405583588419991447]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476866 : Nat.totient 145418826744647158583897476866 = 41548236212756331023970707640 := by
  rw [← show ((([(2, 1), (3, 2), (7, 1), (1154117672576564750665852991, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476866 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_2, prime_oneHundredTwentyThreeDQ_3, prime_oneHundredTwentyThreeDQ_7, prime_oneHundredTwentyThreeDQ_1154117672576564750665852991]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476867 : Nat.totient 145418826744647158583897476867 = 130888898224888965518762080000 := by
  rw [← show ((([(11, 1), (101, 1), (115337, 1), (1134848600826185800781, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476867 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_11, prime_oneHundredTwentyThreeDQ_101, prime_oneHundredTwentyThreeDQ_115337, prime_oneHundredTwentyThreeDQ_1134848600826185800781]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476868 : Nat.totient 145418826744647158583897476868 = 69548075705062085280069064320 := by
  rw [← show ((([(2, 2), (23, 1), (1182289, 1), (1336931512631403248311, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476868 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_2, prime_oneHundredTwentyThreeDQ_23, prime_oneHundredTwentyThreeDQ_1182289, prime_oneHundredTwentyThreeDQ_1336931512631403248311]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476869 : Nat.totient 145418826744647158583897476869 = 95772080254260082259001476160 := by
  rw [← show ((([(3, 1), (83, 1), (16567, 1), (325921333, 1), (108159489589871, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476869 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_3, prime_oneHundredTwentyThreeDQ_83, prime_oneHundredTwentyThreeDQ_16567, prime_oneHundredTwentyThreeDQ_325921333, prime_oneHundredTwentyThreeDQ_108159489589871]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476870 : Nat.totient 145418826744647158583897476870 = 58076039672398259815448033280 := by
  rw [← show ((([(2, 1), (5, 1), (997, 1), (1753, 1), (1363823611, 1), (6100779900937, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476870 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_2, prime_oneHundredTwentyThreeDQ_5, prime_oneHundredTwentyThreeDQ_997, prime_oneHundredTwentyThreeDQ_1753, prime_oneHundredTwentyThreeDQ_1363823611, prime_oneHundredTwentyThreeDQ_6100779900937]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476871 : Nat.totient 145418826744647158583897476871 = 143784907343011265421057251328 := by
  rw [← show ((([(89, 1), (15492669108097, 1), (105464035294687, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476871 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_89, prime_oneHundredTwentyThreeDQ_15492669108097, prime_oneHundredTwentyThreeDQ_105464035294687]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476872 : Nat.totient 145418826744647158583897476872 = 45891526919721535369404357120 := by
  rw [← show ((([(2, 3), (3, 1), (19, 1), (1559, 1), (61031, 1), (3351654105219542953, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476872 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_2, prime_oneHundredTwentyThreeDQ_3, prime_oneHundredTwentyThreeDQ_19, prime_oneHundredTwentyThreeDQ_1559, prime_oneHundredTwentyThreeDQ_61031, prime_oneHundredTwentyThreeDQ_3351654105219542953]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476873 : Nat.totient 145418826744647158583897476873 = 124642686425830712401839033600 := by
  rw [← show ((([(7, 1), (61673, 1), (107966143, 1), (3119894689839401, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476873 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_7, prime_oneHundredTwentyThreeDQ_61673, prime_oneHundredTwentyThreeDQ_107966143, prime_oneHundredTwentyThreeDQ_3119894689839401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476874 : Nat.totient 145418826744647158583897476874 = 72696595627411779894379367040 := by
  rw [← show ((([(2, 1), (5881, 1), (160093, 1), (349340203, 1), (221064267763, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476874 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_2, prime_oneHundredTwentyThreeDQ_5881, prime_oneHundredTwentyThreeDQ_160093, prime_oneHundredTwentyThreeDQ_349340203, prime_oneHundredTwentyThreeDQ_221064267763]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476875 : Nat.totient 145418826744647158583897476875 = 77380040837242770490200168000 := by
  rw [← show ((([(3, 2), (5, 4), (439, 1), (58888919967460251514613, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476875 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_3, prime_oneHundredTwentyThreeDQ_5, prime_oneHundredTwentyThreeDQ_439, prime_oneHundredTwentyThreeDQ_58888919967460251514613]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476876 : Nat.totient 145418826744647158583897476876 = 63168359090215436443351010304 := by
  rw [← show ((([(2, 2), (13, 1), (17, 1), (1633056307, 1), (100731943244319077, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476876 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_2, prime_oneHundredTwentyThreeDQ_13, prime_oneHundredTwentyThreeDQ_17, prime_oneHundredTwentyThreeDQ_1633056307, prime_oneHundredTwentyThreeDQ_100731943244319077]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476877 : Nat.totient 145418826744647158583897476877 = 145418826514679034400910564352 := by
  rw [← show ((([(883092643, 1), (2298442127, 1), (71644160257, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476877 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_883092643, prime_oneHundredTwentyThreeDQ_2298442127, prime_oneHundredTwentyThreeDQ_71644160257]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476878 : Nat.totient 145418826744647158583897476878 = 42834137929363761637782343680 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (37, 1), (1049, 1), (135829, 1), (11003347, 1), (37982380157, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476878 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_2, prime_oneHundredTwentyThreeDQ_3, prime_oneHundredTwentyThreeDQ_11, prime_oneHundredTwentyThreeDQ_37, prime_oneHundredTwentyThreeDQ_1049, prime_oneHundredTwentyThreeDQ_135829, prime_oneHundredTwentyThreeDQ_11003347, prime_oneHundredTwentyThreeDQ_37982380157]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476879 : Nat.totient 145418826744647158583897476879 = 140009799334263943071226060800 := by
  rw [← show ((([(47, 1), (67, 1), (887, 1), (4283, 1), (1123626241, 1), (10818185111, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476879 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_47, prime_oneHundredTwentyThreeDQ_67, prime_oneHundredTwentyThreeDQ_887, prime_oneHundredTwentyThreeDQ_4283, prime_oneHundredTwentyThreeDQ_1123626241, prime_oneHundredTwentyThreeDQ_10818185111]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476880 : Nat.totient 145418826744647158583897476880 = 48249555586764008266514534400 := by
  rw [← show ((([(2, 4), (5, 1), (7, 1), (31, 1), (5332973, 1), (1570729971212190521, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476880 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_2, prime_oneHundredTwentyThreeDQ_5, prime_oneHundredTwentyThreeDQ_7, prime_oneHundredTwentyThreeDQ_31, prime_oneHundredTwentyThreeDQ_5332973, prime_oneHundredTwentyThreeDQ_1570729971212190521]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476881 : Nat.totient 145418826744647158583897476881 = 95355930420969001017986304000 := by
  rw [← show ((([(3, 1), (61, 1), (140797, 1), (5517906211, 1), (1022826169121, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476881 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_3, prime_oneHundredTwentyThreeDQ_61, prime_oneHundredTwentyThreeDQ_140797, prime_oneHundredTwentyThreeDQ_5517906211, prime_oneHundredTwentyThreeDQ_1022826169121]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476882 : Nat.totient 145418826744647158583897476882 = 67732648986306399836233400320 := by
  rw [← show ((([(2, 1), (29, 1), (41, 1), (113, 1), (449, 1), (1205269042013298899237, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476882 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_2, prime_oneHundredTwentyThreeDQ_29, prime_oneHundredTwentyThreeDQ_41, prime_oneHundredTwentyThreeDQ_113, prime_oneHundredTwentyThreeDQ_449, prime_oneHundredTwentyThreeDQ_1205269042013298899237]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476883 : Nat.totient 145418826744647158583897476883 = 145418584589769912487917926400 := by
  rw [← show ((([(600641, 1), (2979022723, 1), (81270296932081, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476883 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_600641, prime_oneHundredTwentyThreeDQ_2979022723, prime_oneHundredTwentyThreeDQ_81270296932081]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476884 : Nat.totient 145418826744647158583897476884 = 48472942240989533526925829760 := by
  rw [← show ((([(2, 2), (3, 5), (6707958641, 1), (22303036505127767, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476884 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_2, prime_oneHundredTwentyThreeDQ_3, prime_oneHundredTwentyThreeDQ_6707958641, prime_oneHundredTwentyThreeDQ_22303036505127767]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476885 : Nat.totient 145418826744647158583897476885 = 116331394163754883173014756160 := by
  rw [← show ((([(5, 1), (31723, 1), (6857736239, 1), (133688978062141, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476885 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_5, prime_oneHundredTwentyThreeDQ_31723, prime_oneHundredTwentyThreeDQ_6857736239, prime_oneHundredTwentyThreeDQ_133688978062141]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476886 : Nat.totient 145418826744647158583897476886 = 72289115603200746095692114944 := by
  rw [← show ((([(2, 1), (173, 1), (7795763, 1), (25189729, 1), (2140239695533, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476886 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_2, prime_oneHundredTwentyThreeDQ_173, prime_oneHundredTwentyThreeDQ_7795763, prime_oneHundredTwentyThreeDQ_25189729, prime_oneHundredTwentyThreeDQ_2140239695533]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476887 : Nat.totient 145418826744647158583897476887 = 83096470278881162392759470000 := by
  rw [← show ((([(3, 1), (7, 2), (38710171, 1), (25555136900618217751, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476887 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_3, prime_oneHundredTwentyThreeDQ_7, prime_oneHundredTwentyThreeDQ_38710171, prime_oneHundredTwentyThreeDQ_25555136900618217751]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476888 : Nat.totient 145418826744647158583897476888 = 71933695948447082376590224000 := by
  rw [← show ((([(2, 3), (149, 1), (251, 1), (486038486138155962003989, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476888 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_2, prime_oneHundredTwentyThreeDQ_149, prime_oneHundredTwentyThreeDQ_251, prime_oneHundredTwentyThreeDQ_486038486138155962003989]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476889 : Nat.totient 145418826744647158583897476889 = 121795520575911215830201267200 := by
  rw [← show ((([(11, 1), (13, 1), (521, 1), (2908937, 1), (670984611308268199, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476889 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_11, prime_oneHundredTwentyThreeDQ_13, prime_oneHundredTwentyThreeDQ_521, prime_oneHundredTwentyThreeDQ_2908937, prime_oneHundredTwentyThreeDQ_670984611308268199]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476890 : Nat.totient 145418826744647158583897476890 = 38771306652678512128729539840 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (6907, 1), (27061, 1), (25933795647479510069, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476890 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_2, prime_oneHundredTwentyThreeDQ_3, prime_oneHundredTwentyThreeDQ_5, prime_oneHundredTwentyThreeDQ_6907, prime_oneHundredTwentyThreeDQ_27061, prime_oneHundredTwentyThreeDQ_25933795647479510069]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476891 : Nat.totient 145418826744647158583897476891 = 131751111905082536180226976800 := by
  rw [← show ((([(19, 1), (23, 1), (5443, 1), (1450711, 1), (42142467542890691, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476891 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_19, prime_oneHundredTwentyThreeDQ_23, prime_oneHundredTwentyThreeDQ_5443, prime_oneHundredTwentyThreeDQ_1450711, prime_oneHundredTwentyThreeDQ_42142467542890691]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476892 : Nat.totient 145418826744647158583897476892 = 72709413372323579291948738444 := by
  rw [← show ((([(2, 2), (36354706686161789645974369223, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476892 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_2, prime_oneHundredTwentyThreeDQ_36354706686161789645974369223]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476893 : Nat.totient 145418826744647158583897476893 = 91241463221482287500322048000 := by
  rw [← show ((([(3, 2), (17, 1), (52981, 1), (17939447122633204255601, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476893 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_3, prime_oneHundredTwentyThreeDQ_17, prime_oneHundredTwentyThreeDQ_52981, prime_oneHundredTwentyThreeDQ_17939447122633204255601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476894 : Nat.totient 145418826744647158583897476894 = 61636929074863585764999321600 := by
  rw [← show ((([(2, 1), (7, 1), (191, 1), (193, 1), (1627, 1), (173186634009254498821, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476894 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_2, prime_oneHundredTwentyThreeDQ_7, prime_oneHundredTwentyThreeDQ_191, prime_oneHundredTwentyThreeDQ_193, prime_oneHundredTwentyThreeDQ_1627, prime_oneHundredTwentyThreeDQ_173186634009254498821]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476895 : Nat.totient 145418826744647158583897476895 = 116335061395717726867117981512 := by
  rw [← show ((([(5, 1), (29083765348929431716779495379, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476895 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_5, prime_oneHundredTwentyThreeDQ_29083765348929431716779495379]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476896 : Nat.totient 145418826744647158583897476896 = 48410234689956401412360483840 := by
  rw [← show ((([(2, 5), (3, 1), (773, 1), (131895216811, 1), (14857333202917, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476896 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_2, prime_oneHundredTwentyThreeDQ_3, prime_oneHundredTwentyThreeDQ_773, prime_oneHundredTwentyThreeDQ_131895216811, prime_oneHundredTwentyThreeDQ_14857333202917]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476897 : Nat.totient 145418826744647158583897476897 = 145418826744224197425798481476 := by
  rw [← show ((([(343811582143, 1), (422960814287413279, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476897 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_343811582143, prime_oneHundredTwentyThreeDQ_422960814287413279]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476898 : Nat.totient 145418826744647158583897476898 = 72136898306399771580988512036 := by
  rw [← show ((([(2, 1), (127, 1), (572515065923807710960226287, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476898 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_2, prime_oneHundredTwentyThreeDQ_127, prime_oneHundredTwentyThreeDQ_572515065923807710960226287]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476899 : Nat.totient 145418826744647158583897476899 = 96856375002556399128543744000 := by
  rw [← show ((([(3, 1), (1109, 1), (46457, 1), (13454101, 1), (69929752389041, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476899 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_3, prime_oneHundredTwentyThreeDQ_1109, prime_oneHundredTwentyThreeDQ_46457, prime_oneHundredTwentyThreeDQ_13454101, prime_oneHundredTwentyThreeDQ_69929752389041]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476900 : Nat.totient 145418826744647158583897476900 = 52846818679608519622499164800 := by
  rw [← show ((([(2, 2), (5, 2), (11, 1), (1619, 1), (569419, 1), (143399998955215939, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476900 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_2, prime_oneHundredTwentyThreeDQ_5, prime_oneHundredTwentyThreeDQ_11, prime_oneHundredTwentyThreeDQ_1619, prime_oneHundredTwentyThreeDQ_569419, prime_oneHundredTwentyThreeDQ_143399998955215939]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyThreeDQ_145418826744647158583897476901 : Nat.totient 145418826744647158583897476901 = 121729964281614014653485164160 := by
  rw [← show ((([(7, 1), (43, 1), (7699, 1), (561019, 1), (111851613009889721, 1)] : List FactorBlock).map factorBlockValue).prod) = 145418826744647158583897476901 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyThreeDQ_7, prime_oneHundredTwentyThreeDQ_43, prime_oneHundredTwentyThreeDQ_7699, prime_oneHundredTwentyThreeDQ_561019, prime_oneHundredTwentyThreeDQ_111851613009889721]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64OneHundredTwentyThreeDQ : certifiedKill 1 145418826744647158583897476799 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_oneHundredTwentyThreeDQ_145418826744647158583897476800, phi_oneHundredTwentyThreeDQ_145418826744647158583897476801, phi_oneHundredTwentyThreeDQ_145418826744647158583897476802,
    phi_oneHundredTwentyThreeDQ_145418826744647158583897476803, phi_oneHundredTwentyThreeDQ_145418826744647158583897476804, phi_oneHundredTwentyThreeDQ_145418826744647158583897476805,
    phi_oneHundredTwentyThreeDQ_145418826744647158583897476806, phi_oneHundredTwentyThreeDQ_145418826744647158583897476807, phi_oneHundredTwentyThreeDQ_145418826744647158583897476808,
    phi_oneHundredTwentyThreeDQ_145418826744647158583897476809, phi_oneHundredTwentyThreeDQ_145418826744647158583897476810, phi_oneHundredTwentyThreeDQ_145418826744647158583897476811,
    phi_oneHundredTwentyThreeDQ_145418826744647158583897476812, phi_oneHundredTwentyThreeDQ_145418826744647158583897476813, phi_oneHundredTwentyThreeDQ_145418826744647158583897476814,
    phi_oneHundredTwentyThreeDQ_145418826744647158583897476815, phi_oneHundredTwentyThreeDQ_145418826744647158583897476816, phi_oneHundredTwentyThreeDQ_145418826744647158583897476817,
    phi_oneHundredTwentyThreeDQ_145418826744647158583897476818, phi_oneHundredTwentyThreeDQ_145418826744647158583897476819, phi_oneHundredTwentyThreeDQ_145418826744647158583897476820,
    phi_oneHundredTwentyThreeDQ_145418826744647158583897476821, phi_oneHundredTwentyThreeDQ_145418826744647158583897476822, phi_oneHundredTwentyThreeDQ_145418826744647158583897476823,
    phi_oneHundredTwentyThreeDQ_145418826744647158583897476824, phi_oneHundredTwentyThreeDQ_145418826744647158583897476825, phi_oneHundredTwentyThreeDQ_145418826744647158583897476826,
    phi_oneHundredTwentyThreeDQ_145418826744647158583897476827, phi_oneHundredTwentyThreeDQ_145418826744647158583897476828, phi_oneHundredTwentyThreeDQ_145418826744647158583897476829,
    phi_oneHundredTwentyThreeDQ_145418826744647158583897476830, phi_oneHundredTwentyThreeDQ_145418826744647158583897476831, phi_oneHundredTwentyThreeDQ_145418826744647158583897476832,
    phi_oneHundredTwentyThreeDQ_145418826744647158583897476833, phi_oneHundredTwentyThreeDQ_145418826744647158583897476834, phi_oneHundredTwentyThreeDQ_145418826744647158583897476835,
    phi_oneHundredTwentyThreeDQ_145418826744647158583897476836, phi_oneHundredTwentyThreeDQ_145418826744647158583897476837, phi_oneHundredTwentyThreeDQ_145418826744647158583897476838,
    phi_oneHundredTwentyThreeDQ_145418826744647158583897476839, phi_oneHundredTwentyThreeDQ_145418826744647158583897476840, phi_oneHundredTwentyThreeDQ_145418826744647158583897476841,
    phi_oneHundredTwentyThreeDQ_145418826744647158583897476842, phi_oneHundredTwentyThreeDQ_145418826744647158583897476843, phi_oneHundredTwentyThreeDQ_145418826744647158583897476844,
    phi_oneHundredTwentyThreeDQ_145418826744647158583897476845, phi_oneHundredTwentyThreeDQ_145418826744647158583897476846, phi_oneHundredTwentyThreeDQ_145418826744647158583897476847,
    phi_oneHundredTwentyThreeDQ_145418826744647158583897476848, phi_oneHundredTwentyThreeDQ_145418826744647158583897476849, phi_oneHundredTwentyThreeDQ_145418826744647158583897476850,
    phi_oneHundredTwentyThreeDQ_145418826744647158583897476851, phi_oneHundredTwentyThreeDQ_145418826744647158583897476852, phi_oneHundredTwentyThreeDQ_145418826744647158583897476853,
    phi_oneHundredTwentyThreeDQ_145418826744647158583897476854, phi_oneHundredTwentyThreeDQ_145418826744647158583897476855, phi_oneHundredTwentyThreeDQ_145418826744647158583897476856,
    phi_oneHundredTwentyThreeDQ_145418826744647158583897476857, phi_oneHundredTwentyThreeDQ_145418826744647158583897476858, phi_oneHundredTwentyThreeDQ_145418826744647158583897476859,
    phi_oneHundredTwentyThreeDQ_145418826744647158583897476860, phi_oneHundredTwentyThreeDQ_145418826744647158583897476861, phi_oneHundredTwentyThreeDQ_145418826744647158583897476862,
    phi_oneHundredTwentyThreeDQ_145418826744647158583897476863, phi_oneHundredTwentyThreeDQ_145418826744647158583897476864, phi_oneHundredTwentyThreeDQ_145418826744647158583897476865,
    phi_oneHundredTwentyThreeDQ_145418826744647158583897476866, phi_oneHundredTwentyThreeDQ_145418826744647158583897476867, phi_oneHundredTwentyThreeDQ_145418826744647158583897476868,
    phi_oneHundredTwentyThreeDQ_145418826744647158583897476869, phi_oneHundredTwentyThreeDQ_145418826744647158583897476870, phi_oneHundredTwentyThreeDQ_145418826744647158583897476871,
    phi_oneHundredTwentyThreeDQ_145418826744647158583897476872, phi_oneHundredTwentyThreeDQ_145418826744647158583897476873, phi_oneHundredTwentyThreeDQ_145418826744647158583897476874,
    phi_oneHundredTwentyThreeDQ_145418826744647158583897476875, phi_oneHundredTwentyThreeDQ_145418826744647158583897476876, phi_oneHundredTwentyThreeDQ_145418826744647158583897476877,
    phi_oneHundredTwentyThreeDQ_145418826744647158583897476878, phi_oneHundredTwentyThreeDQ_145418826744647158583897476879, phi_oneHundredTwentyThreeDQ_145418826744647158583897476880,
    phi_oneHundredTwentyThreeDQ_145418826744647158583897476881, phi_oneHundredTwentyThreeDQ_145418826744647158583897476882, phi_oneHundredTwentyThreeDQ_145418826744647158583897476883,
    phi_oneHundredTwentyThreeDQ_145418826744647158583897476884, phi_oneHundredTwentyThreeDQ_145418826744647158583897476885, phi_oneHundredTwentyThreeDQ_145418826744647158583897476886,
    phi_oneHundredTwentyThreeDQ_145418826744647158583897476887, phi_oneHundredTwentyThreeDQ_145418826744647158583897476888, phi_oneHundredTwentyThreeDQ_145418826744647158583897476889,
    phi_oneHundredTwentyThreeDQ_145418826744647158583897476890, phi_oneHundredTwentyThreeDQ_145418826744647158583897476891, phi_oneHundredTwentyThreeDQ_145418826744647158583897476892,
    phi_oneHundredTwentyThreeDQ_145418826744647158583897476893, phi_oneHundredTwentyThreeDQ_145418826744647158583897476894, phi_oneHundredTwentyThreeDQ_145418826744647158583897476895,
    phi_oneHundredTwentyThreeDQ_145418826744647158583897476896, phi_oneHundredTwentyThreeDQ_145418826744647158583897476897, phi_oneHundredTwentyThreeDQ_145418826744647158583897476898,
    phi_oneHundredTwentyThreeDQ_145418826744647158583897476899, phi_oneHundredTwentyThreeDQ_145418826744647158583897476900, phi_oneHundredTwentyThreeDQ_145418826744647158583897476901
    ]

end TotientTailPeriodKiller
end Erdos249257
