import Erdos249257.DiagonalPincerCertificatesT64
/- Kernel-checked off-diagonal certificate at a freely chosen position. -/
namespace Erdos249257
namespace TotientTailPeriodKiller
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
private def oneHundredFiftyFiveEWFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem oneHundredFiftyFiveEWFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : oneHundredFiftyFiveEWFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [oneHundredFiftyFiveEWFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [oneHundredFiftyFiveEWFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then oneHundredFiftyFiveEWFastPow a n * oneHundredFiftyFiveEWFastPow a n * a else oneHundredFiftyFiveEWFastPow a n * oneHundredFiftyFiveEWFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_oneHundredFiftyFiveEW_2 : Nat.Prime 2 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_3 : Nat.Prime 3 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_5 : Nat.Prime 5 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_7 : Nat.Prime 7 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_11 : Nat.Prime 11 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_13 : Nat.Prime 13 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_17 : Nat.Prime 17 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_19 : Nat.Prime 19 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_23 : Nat.Prime 23 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_29 : Nat.Prime 29 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_31 : Nat.Prime 31 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_37 : Nat.Prime 37 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_41 : Nat.Prime 41 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_43 : Nat.Prime 43 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_47 : Nat.Prime 47 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_53 : Nat.Prime 53 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_59 : Nat.Prime 59 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_61 : Nat.Prime 61 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_67 : Nat.Prime 67 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_71 : Nat.Prime 71 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_73 : Nat.Prime 73 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_79 : Nat.Prime 79 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_83 : Nat.Prime 83 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_89 : Nat.Prime 89 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_97 : Nat.Prime 97 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_101 : Nat.Prime 101 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_103 : Nat.Prime 103 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_107 : Nat.Prime 107 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_109 : Nat.Prime 109 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_113 : Nat.Prime 113 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_127 : Nat.Prime 127 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_131 : Nat.Prime 131 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_137 : Nat.Prime 137 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_139 : Nat.Prime 139 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_149 : Nat.Prime 149 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_151 : Nat.Prime 151 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_157 : Nat.Prime 157 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_163 : Nat.Prime 163 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_167 : Nat.Prime 167 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_173 : Nat.Prime 173 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_179 : Nat.Prime 179 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_181 : Nat.Prime 181 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_191 : Nat.Prime 191 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_193 : Nat.Prime 193 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_197 : Nat.Prime 197 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_199 : Nat.Prime 199 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_211 : Nat.Prime 211 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_223 : Nat.Prime 223 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_227 : Nat.Prime 227 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_239 : Nat.Prime 239 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_251 : Nat.Prime 251 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_257 : Nat.Prime 257 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_263 : Nat.Prime 263 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_269 : Nat.Prime 269 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_271 : Nat.Prime 271 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_277 : Nat.Prime 277 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_281 : Nat.Prime 281 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_283 : Nat.Prime 283 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_293 : Nat.Prime 293 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_307 : Nat.Prime 307 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_311 : Nat.Prime 311 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_313 : Nat.Prime 313 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_317 : Nat.Prime 317 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_337 : Nat.Prime 337 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_347 : Nat.Prime 347 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_349 : Nat.Prime 349 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_353 : Nat.Prime 353 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_359 : Nat.Prime 359 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_367 : Nat.Prime 367 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_383 : Nat.Prime 383 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_389 : Nat.Prime 389 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_397 : Nat.Prime 397 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_409 : Nat.Prime 409 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_421 : Nat.Prime 421 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_431 : Nat.Prime 431 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_433 : Nat.Prime 433 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_439 : Nat.Prime 439 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_443 : Nat.Prime 443 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_449 : Nat.Prime 449 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_457 : Nat.Prime 457 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_461 : Nat.Prime 461 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_463 : Nat.Prime 463 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_467 : Nat.Prime 467 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_479 : Nat.Prime 479 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_487 : Nat.Prime 487 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_521 : Nat.Prime 521 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_557 : Nat.Prime 557 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_563 : Nat.Prime 563 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_569 : Nat.Prime 569 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_599 : Nat.Prime 599 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_607 : Nat.Prime 607 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_613 : Nat.Prime 613 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_617 : Nat.Prime 617 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_619 : Nat.Prime 619 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_641 : Nat.Prime 641 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_643 : Nat.Prime 643 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_653 : Nat.Prime 653 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_659 : Nat.Prime 659 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_673 : Nat.Prime 673 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_709 : Nat.Prime 709 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_743 : Nat.Prime 743 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_757 : Nat.Prime 757 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_769 : Nat.Prime 769 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_811 : Nat.Prime 811 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_829 : Nat.Prime 829 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_839 : Nat.Prime 839 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_853 : Nat.Prime 853 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_919 : Nat.Prime 919 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_953 : Nat.Prime 953 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_971 : Nat.Prime 971 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_991 : Nat.Prime 991 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_997 : Nat.Prime 997 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_1009 : Nat.Prime 1009 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_1013 : Nat.Prime 1013 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_1021 : Nat.Prime 1021 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_1123 : Nat.Prime 1123 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_1171 : Nat.Prime 1171 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_1193 : Nat.Prime 1193 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_1237 : Nat.Prime 1237 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_1249 : Nat.Prime 1249 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_1259 : Nat.Prime 1259 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_1279 : Nat.Prime 1279 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_1289 : Nat.Prime 1289 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_1321 : Nat.Prime 1321 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_1361 : Nat.Prime 1361 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_1367 : Nat.Prime 1367 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_1373 : Nat.Prime 1373 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_1399 : Nat.Prime 1399 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_1447 : Nat.Prime 1447 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_1471 : Nat.Prime 1471 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_1483 : Nat.Prime 1483 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_1493 : Nat.Prime 1493 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_1499 : Nat.Prime 1499 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_1523 : Nat.Prime 1523 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_1553 : Nat.Prime 1553 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_1601 : Nat.Prime 1601 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_1627 : Nat.Prime 1627 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_1697 : Nat.Prime 1697 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_1699 : Nat.Prime 1699 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_1907 : Nat.Prime 1907 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_1949 : Nat.Prime 1949 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_1951 : Nat.Prime 1951 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_1999 : Nat.Prime 1999 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_2063 : Nat.Prime 2063 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_2113 : Nat.Prime 2113 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_2137 : Nat.Prime 2137 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_2143 : Nat.Prime 2143 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_2213 : Nat.Prime 2213 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_2341 : Nat.Prime 2341 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_2477 : Nat.Prime 2477 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_2647 : Nat.Prime 2647 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_2657 : Nat.Prime 2657 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_2677 : Nat.Prime 2677 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_2731 : Nat.Prime 2731 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_2851 : Nat.Prime 2851 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_2857 : Nat.Prime 2857 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_2887 : Nat.Prime 2887 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_2909 : Nat.Prime 2909 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_3037 : Nat.Prime 3037 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_3049 : Nat.Prime 3049 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_3089 : Nat.Prime 3089 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_3119 : Nat.Prime 3119 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_3137 : Nat.Prime 3137 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_3331 : Nat.Prime 3331 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_3389 : Nat.Prime 3389 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_3449 : Nat.Prime 3449 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_3463 : Nat.Prime 3463 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_3499 : Nat.Prime 3499 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_3517 : Nat.Prime 3517 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_3583 : Nat.Prime 3583 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_3617 : Nat.Prime 3617 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_3673 : Nat.Prime 3673 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_3691 : Nat.Prime 3691 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_3701 : Nat.Prime 3701 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_3851 : Nat.Prime 3851 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_4091 : Nat.Prime 4091 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_4241 : Nat.Prime 4241 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_4637 : Nat.Prime 4637 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_4937 : Nat.Prime 4937 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_5233 : Nat.Prime 5233 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_5557 : Nat.Prime 5557 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_5659 : Nat.Prime 5659 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_5783 : Nat.Prime 5783 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_5867 : Nat.Prime 5867 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_5897 : Nat.Prime 5897 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_6011 : Nat.Prime 6011 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_6053 : Nat.Prime 6053 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_6073 : Nat.Prime 6073 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_6089 : Nat.Prime 6089 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_6229 : Nat.Prime 6229 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_6827 : Nat.Prime 6827 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_6959 : Nat.Prime 6959 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_6961 : Nat.Prime 6961 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_7159 : Nat.Prime 7159 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_7307 : Nat.Prime 7307 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_7639 : Nat.Prime 7639 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_8147 : Nat.Prime 8147 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_8171 : Nat.Prime 8171 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_8291 : Nat.Prime 8291 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_8461 : Nat.Prime 8461 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_8753 : Nat.Prime 8753 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_8839 : Nat.Prime 8839 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_8933 : Nat.Prime 8933 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_9203 : Nat.Prime 9203 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_9283 : Nat.Prime 9283 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_9413 : Nat.Prime 9413 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_9587 : Nat.Prime 9587 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_9643 : Nat.Prime 9643 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_9949 : Nat.Prime 9949 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_10177 : Nat.Prime 10177 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_10429 : Nat.Prime 10429 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_10867 : Nat.Prime 10867 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_10949 : Nat.Prime 10949 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_11273 : Nat.Prime 11273 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_11593 : Nat.Prime 11593 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_11681 : Nat.Prime 11681 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_12269 : Nat.Prime 12269 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_12277 : Nat.Prime 12277 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_12539 : Nat.Prime 12539 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_12659 : Nat.Prime 12659 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_13121 : Nat.Prime 13121 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_13187 : Nat.Prime 13187 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_13219 : Nat.Prime 13219 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_14437 : Nat.Prime 14437 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_14867 : Nat.Prime 14867 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_15269 : Nat.Prime 15269 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_15377 : Nat.Prime 15377 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_16007 : Nat.Prime 16007 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_16487 : Nat.Prime 16487 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_16691 : Nat.Prime 16691 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_17011 : Nat.Prime 17011 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_17203 : Nat.Prime 17203 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_17377 : Nat.Prime 17377 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_18131 : Nat.Prime 18131 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_18289 : Nat.Prime 18289 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_19471 : Nat.Prime 19471 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_19541 : Nat.Prime 19541 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_19997 : Nat.Prime 19997 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_20357 : Nat.Prime 20357 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_20543 : Nat.Prime 20543 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_20563 : Nat.Prime 20563 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_20663 : Nat.Prime 20663 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_20753 : Nat.Prime 20753 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_21269 : Nat.Prime 21269 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_21587 : Nat.Prime 21587 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_23071 : Nat.Prime 23071 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_23227 : Nat.Prime 23227 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_25447 : Nat.Prime 25447 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_26189 : Nat.Prime 26189 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_27611 : Nat.Prime 27611 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_27997 : Nat.Prime 27997 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_28109 : Nat.Prime 28109 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_28151 : Nat.Prime 28151 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_28723 : Nat.Prime 28723 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_28933 : Nat.Prime 28933 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_29863 : Nat.Prime 29863 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_30109 : Nat.Prime 30109 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_34141 : Nat.Prime 34141 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_34267 : Nat.Prime 34267 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_34961 : Nat.Prime 34961 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_35059 : Nat.Prime 35059 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_37039 : Nat.Prime 37039 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_38351 : Nat.Prime 38351 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_38861 : Nat.Prime 38861 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_40829 : Nat.Prime 40829 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_41341 : Nat.Prime 41341 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_41761 : Nat.Prime 41761 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_42703 : Nat.Prime 42703 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_42853 : Nat.Prime 42853 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_46559 : Nat.Prime 46559 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_49171 : Nat.Prime 49171 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_50549 : Nat.Prime 50549 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_50969 : Nat.Prime 50969 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_52009 : Nat.Prime 52009 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_52529 : Nat.Prime 52529 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_53923 : Nat.Prime 53923 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_54319 : Nat.Prime 54319 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_55339 : Nat.Prime 55339 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_57457 : Nat.Prime 57457 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_58579 : Nat.Prime 58579 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_64067 : Nat.Prime 64067 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_70459 : Nat.Prime 70459 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_74527 : Nat.Prime 74527 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_74609 : Nat.Prime 74609 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_75703 : Nat.Prime 75703 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_79087 : Nat.Prime 79087 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_86813 : Nat.Prime 86813 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_88499 : Nat.Prime 88499 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_88813 : Nat.Prime 88813 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_90187 : Nat.Prime 90187 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_94651 : Nat.Prime 94651 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_96769 : Nat.Prime 96769 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_98017 : Nat.Prime 98017 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_100391 : Nat.Prime 100391 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_102077 : Nat.Prime 102077 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_105277 : Nat.Prime 105277 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_106747 : Nat.Prime 106747 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_107981 : Nat.Prime 107981 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_109883 : Nat.Prime 109883 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_111211 : Nat.Prime 111211 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_117193 : Nat.Prime 117193 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_122861 : Nat.Prime 122861 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_125183 : Nat.Prime 125183 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_126713 : Nat.Prime 126713 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_131023 : Nat.Prime 131023 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_148609 : Nat.Prime 148609 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_158791 : Nat.Prime 158791 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_163909 : Nat.Prime 163909 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_168281 : Nat.Prime 168281 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_171401 : Nat.Prime 171401 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_178793 : Nat.Prime 178793 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_178921 : Nat.Prime 178921 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_181031 : Nat.Prime 181031 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_185153 : Nat.Prime 185153 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_186379 : Nat.Prime 186379 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_187193 : Nat.Prime 187193 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_200723 : Nat.Prime 200723 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_203317 : Nat.Prime 203317 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_206303 : Nat.Prime 206303 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_209581 : Nat.Prime 209581 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_229267 : Nat.Prime 229267 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_230369 : Nat.Prime 230369 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_236813 : Nat.Prime 236813 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_253871 : Nat.Prime 253871 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_267643 : Nat.Prime 267643 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_269441 : Nat.Prime 269441 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_274069 : Nat.Prime 274069 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_281527 : Nat.Prime 281527 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_294167 : Nat.Prime 294167 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_296627 : Nat.Prime 296627 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_301669 : Nat.Prime 301669 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_321619 : Nat.Prime 321619 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_324529 : Nat.Prime 324529 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_386437 : Nat.Prime 386437 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_397073 : Nat.Prime 397073 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_432587 : Nat.Prime 432587 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_451279 : Nat.Prime 451279 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_454297 : Nat.Prime 454297 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_455881 : Nat.Prime 455881 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_465277 : Nat.Prime 465277 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_488573 : Nat.Prime 488573 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_522947 : Nat.Prime 522947 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_532093 : Nat.Prime 532093 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_542533 : Nat.Prime 542533 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_549977 : Nat.Prime 549977 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_605329 : Nat.Prime 605329 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_607213 : Nat.Prime 607213 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_630613 : Nat.Prime 630613 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_634891 : Nat.Prime 634891 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_669359 : Nat.Prime 669359 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_702239 : Nat.Prime 702239 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_708733 : Nat.Prime 708733 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_738713 : Nat.Prime 738713 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_753527 : Nat.Prime 753527 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_811763 : Nat.Prime 811763 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_813277 : Nat.Prime 813277 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_880337 : Nat.Prime 880337 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_880573 : Nat.Prime 880573 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_903073 : Nat.Prime 903073 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_926099 : Nat.Prime 926099 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_1028213 : Nat.Prime 1028213 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_1046599 : Nat.Prime 1046599 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_1060721 : Nat.Prime 1060721 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_1069267 : Nat.Prime 1069267 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_1176589 : Nat.Prime 1176589 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_1219831 : Nat.Prime 1219831 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_1424021 : Nat.Prime 1424021 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_1425877 : Nat.Prime 1425877 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_1439413 : Nat.Prime 1439413 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_1466177 : Nat.Prime 1466177 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_1529191 : Nat.Prime 1529191 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_1619677 : Nat.Prime 1619677 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_1658617 : Nat.Prime 1658617 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_1805059 : Nat.Prime 1805059 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_1811443 : Nat.Prime 1811443 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_1812089 : Nat.Prime 1812089 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_2011019 : Nat.Prime 2011019 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_2054519 : Nat.Prime 2054519 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_2094109 : Nat.Prime 2094109 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_2147051 : Nat.Prime 2147051 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_2159081 : Nat.Prime 2159081 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_2357969 : Nat.Prime 2357969 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_2566667 : Nat.Prime 2566667 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_2709023 : Nat.Prime 2709023 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_2711351 : Nat.Prime 2711351 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_2727437 : Nat.Prime 2727437 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_2732579 : Nat.Prime 2732579 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_2807017 : Nat.Prime 2807017 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_2872741 : Nat.Prime 2872741 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_2915509 : Nat.Prime 2915509 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_3599009 : Nat.Prime 3599009 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_3763897 : Nat.Prime 3763897 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_4007789 : Nat.Prime 4007789 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_4090049 : Nat.Prime 4090049 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_4201409 : Nat.Prime 4201409 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_5003543 : Nat.Prime 5003543 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_5007637 : Nat.Prime 5007637 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_5255879 : Nat.Prime 5255879 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_5301143 : Nat.Prime 5301143 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_5301337 : Nat.Prime 5301337 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_5824333 : Nat.Prime 5824333 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_5946163 : Nat.Prime 5946163 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_5980267 : Nat.Prime 5980267 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_6663763 : Nat.Prime 6663763 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_6665437 : Nat.Prime 6665437 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_6774191 : Nat.Prime 6774191 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_7306363 : Nat.Prime 7306363 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_7666661 : Nat.Prime 7666661 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_8652389 : Nat.Prime 8652389 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_8712661 : Nat.Prime 8712661 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_9371441 : Nat.Prime 9371441 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_9800207 : Nat.Prime 9800207 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_10820141 : Nat.Prime 10820141 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_11462203 : Nat.Prime 11462203 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_12263611 : Nat.Prime 12263611 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_12279359 : Nat.Prime 12279359 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_12292699 : Nat.Prime 12292699 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_12391007 : Nat.Prime 12391007 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_13066721 : Nat.Prime 13066721 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_13381727 : Nat.Prime 13381727 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_13471147 : Nat.Prime 13471147 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_13617913 : Nat.Prime 13617913 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_14114963 : Nat.Prime 14114963 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_15402547 : Nat.Prime 15402547 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_15629399 : Nat.Prime 15629399 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_19419913 : Nat.Prime 19419913 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_20092183 : Nat.Prime 20092183 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_20150327 : Nat.Prime 20150327 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_20418131 : Nat.Prime 20418131 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_21368801 : Nat.Prime 21368801 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_21731947 : Nat.Prime 21731947 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_22896613 : Nat.Prime 22896613 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_24177523 : Nat.Prime 24177523 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_24669107 : Nat.Prime 24669107 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_28679857 : Nat.Prime 28679857 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_28937567 : Nat.Prime 28937567 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_29655581 : Nat.Prime 29655581 := by norm_num

private theorem prime_oneHundredFiftyFiveEW_30021259 : Nat.Prime 30021259 := by
  apply lucas_primality 30021259 (2 : ZMod 30021259)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5003543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5003543, 1)] : List FactorBlock).map factorBlockValue).prod) = 30021259 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_5003543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 30021259) ^ 15010629 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 30021259) ^ 10007086 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 30021259) ^ 6 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_30830593 : Nat.Prime 30830593 := by
  apply lucas_primality 30830593 (7 : ZMod 30830593)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 12), (3, 1), (13, 1), (193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 12), (3, 1), (13, 1), (193, 1)] : List FactorBlock).map factorBlockValue).prod) = 30830593 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_13
      · exact prime_oneHundredFiftyFiveEW_193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 30830593) ^ 15415296 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (7 : ZMod 30830593) ^ 10276864 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (7 : ZMod 30830593) ^ 2371584 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (7 : ZMod 30830593) ^ 159744 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_31098827 : Nat.Prime 31098827 := by
  apply lucas_primality 31098827 (2 : ZMod 31098827)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (173, 1), (8171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (173, 1), (8171, 1)] : List FactorBlock).map factorBlockValue).prod) = 31098827 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_11
      · exact prime_oneHundredFiftyFiveEW_173
      · exact prime_oneHundredFiftyFiveEW_8171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 31098827) ^ 15549413 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 31098827) ^ 2827166 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 31098827) ^ 179762 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 31098827) ^ 3806 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_34007411 : Nat.Prime 34007411 := by
  apply lucas_primality 34007411 (2 : ZMod 34007411)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (43, 1), (79087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (43, 1), (79087, 1)] : List FactorBlock).map factorBlockValue).prod) = 34007411 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_5
      · exact prime_oneHundredFiftyFiveEW_43
      · exact prime_oneHundredFiftyFiveEW_79087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 34007411) ^ 17003705 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 34007411) ^ 6801482 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 34007411) ^ 790870 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 34007411) ^ 430 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_36314959 : Nat.Prime 36314959 := by
  apply lucas_primality 36314959 (3 : ZMod 36314959)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (439, 1), (811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (439, 1), (811, 1)] : List FactorBlock).map factorBlockValue).prod) = 36314959 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_17
      · exact prime_oneHundredFiftyFiveEW_439
      · exact prime_oneHundredFiftyFiveEW_811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 36314959) ^ 18157479 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 36314959) ^ 12104986 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 36314959) ^ 2136174 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 36314959) ^ 82722 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 36314959) ^ 44778 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_37204703 : Nat.Prime 37204703 := by
  apply lucas_primality 37204703 (5 : ZMod 37204703)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1699, 1), (10949, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1699, 1), (10949, 1)] : List FactorBlock).map factorBlockValue).prod) = 37204703 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_1699
      · exact prime_oneHundredFiftyFiveEW_10949
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 37204703) ^ 18602351 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 37204703) ^ 21898 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 37204703) ^ 3398 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_40024703 : Nat.Prime 40024703 := by
  apply lucas_primality 40024703 (5 : ZMod 40024703)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (467, 1), (42853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (467, 1), (42853, 1)] : List FactorBlock).map factorBlockValue).prod) = 40024703 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_467
      · exact prime_oneHundredFiftyFiveEW_42853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 40024703) ^ 20012351 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 40024703) ^ 85706 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 40024703) ^ 934 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_40440481 : Nat.Prime 40440481 := by
  apply lucas_primality 40440481 (17 : ZMod 40440481)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 1), (173, 1), (487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 1), (173, 1), (487, 1)] : List FactorBlock).map factorBlockValue).prod) = 40440481 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_5
      · exact prime_oneHundredFiftyFiveEW_173
      · exact prime_oneHundredFiftyFiveEW_487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 40440481) ^ 20220240 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (17 : ZMod 40440481) ^ 13480160 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (17 : ZMod 40440481) ^ 8088096 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (17 : ZMod 40440481) ^ 233760 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (17 : ZMod 40440481) ^ 83040 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_40446589 : Nat.Prime 40446589 := by
  apply lucas_primality 40446589 (2 : ZMod 40446589)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (13, 1), (37039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (13, 1), (37039, 1)] : List FactorBlock).map factorBlockValue).prod) = 40446589 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_7
      · exact prime_oneHundredFiftyFiveEW_13
      · exact prime_oneHundredFiftyFiveEW_37039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 40446589) ^ 20223294 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 40446589) ^ 13482196 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 40446589) ^ 5778084 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 40446589) ^ 3111276 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 40446589) ^ 1092 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_41527781 : Nat.Prime 41527781 := by
  apply lucas_primality 41527781 (2 : ZMod 41527781)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (296627, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (296627, 1)] : List FactorBlock).map factorBlockValue).prod) = 41527781 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_5
      · exact prime_oneHundredFiftyFiveEW_7
      · exact prime_oneHundredFiftyFiveEW_296627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 41527781) ^ 20763890 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 41527781) ^ 8305556 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 41527781) ^ 5932540 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 41527781) ^ 140 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_41733689 : Nat.Prime 41733689 := by
  apply lucas_primality 41733689 (3 : ZMod 41733689)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (31, 1), (168281, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (31, 1), (168281, 1)] : List FactorBlock).map factorBlockValue).prod) = 41733689 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_31
      · exact prime_oneHundredFiftyFiveEW_168281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 41733689) ^ 20866844 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 41733689) ^ 1346248 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 41733689) ^ 248 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_44014567 : Nat.Prime 44014567 := by
  apply lucas_primality 44014567 (3 : ZMod 44014567)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (41, 1), (178921, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (41, 1), (178921, 1)] : List FactorBlock).map factorBlockValue).prod) = 44014567 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_41
      · exact prime_oneHundredFiftyFiveEW_178921
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 44014567) ^ 22007283 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 44014567) ^ 14671522 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 44014567) ^ 1073526 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 44014567) ^ 246 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_48425473 : Nat.Prime 48425473 := by
  apply lucas_primality 48425473 (5 : ZMod 48425473)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 9), (3, 3), (31, 1), (113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 9), (3, 3), (31, 1), (113, 1)] : List FactorBlock).map factorBlockValue).prod) = 48425473 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_31
      · exact prime_oneHundredFiftyFiveEW_113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 48425473) ^ 24212736 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 48425473) ^ 16141824 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 48425473) ^ 1562112 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 48425473) ^ 428544 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_52864081 : Nat.Prime 52864081 := by
  apply lucas_primality 52864081 (17 : ZMod 52864081)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (19, 1), (11593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (19, 1), (11593, 1)] : List FactorBlock).map factorBlockValue).prod) = 52864081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_5
      · exact prime_oneHundredFiftyFiveEW_19
      · exact prime_oneHundredFiftyFiveEW_11593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 52864081) ^ 26432040 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (17 : ZMod 52864081) ^ 17621360 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (17 : ZMod 52864081) ^ 10572816 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (17 : ZMod 52864081) ^ 2782320 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (17 : ZMod 52864081) ^ 4560 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_53861347 : Nat.Prime 53861347 := by
  apply lucas_primality 53861347 (5 : ZMod 53861347)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (11, 1), (38861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (11, 1), (38861, 1)] : List FactorBlock).map factorBlockValue).prod) = 53861347 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_7
      · exact prime_oneHundredFiftyFiveEW_11
      · exact prime_oneHundredFiftyFiveEW_38861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 53861347) ^ 26930673 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 53861347) ^ 17953782 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 53861347) ^ 7694478 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 53861347) ^ 4896486 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 53861347) ^ 1386 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_56315333 : Nat.Prime 56315333 := by
  apply lucas_primality 56315333 (2 : ZMod 56315333)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 1), (37, 1), (13121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 1), (37, 1), (13121, 1)] : List FactorBlock).map factorBlockValue).prod) = 56315333 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_29
      · exact prime_oneHundredFiftyFiveEW_37
      · exact prime_oneHundredFiftyFiveEW_13121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 56315333) ^ 28157666 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 56315333) ^ 1941908 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 56315333) ^ 1522036 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 56315333) ^ 4292 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_59210243 : Nat.Prime 59210243 := by
  apply lucas_primality 59210243 (5 : ZMod 59210243)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13, 1), (263, 1), (1237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13, 1), (263, 1), (1237, 1)] : List FactorBlock).map factorBlockValue).prod) = 59210243 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_7
      · exact prime_oneHundredFiftyFiveEW_13
      · exact prime_oneHundredFiftyFiveEW_263
      · exact prime_oneHundredFiftyFiveEW_1237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 59210243) ^ 29605121 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 59210243) ^ 8458606 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 59210243) ^ 4554634 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 59210243) ^ 225134 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 59210243) ^ 47866 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_63027023 : Nat.Prime 63027023 := by
  apply lucas_primality 63027023 (5 : ZMod 63027023)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (157, 1), (200723, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (157, 1), (200723, 1)] : List FactorBlock).map factorBlockValue).prod) = 63027023 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_157
      · exact prime_oneHundredFiftyFiveEW_200723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 63027023) ^ 31513511 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 63027023) ^ 401446 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 63027023) ^ 314 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_63151129 : Nat.Prime 63151129 := by
  apply lucas_primality 63151129 (7 : ZMod 63151129)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (307, 1), (2857, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (307, 1), (2857, 1)] : List FactorBlock).map factorBlockValue).prod) = 63151129 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_307
      · exact prime_oneHundredFiftyFiveEW_2857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 63151129) ^ 31575564 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (7 : ZMod 63151129) ^ 21050376 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (7 : ZMod 63151129) ^ 205704 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (7 : ZMod 63151129) ^ 22104 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_64377031 : Nat.Prime 64377031 := by
  apply lucas_primality 64377031 (3 : ZMod 64377031)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (1447, 1), (1483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (1447, 1), (1483, 1)] : List FactorBlock).map factorBlockValue).prod) = 64377031 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_5
      · exact prime_oneHundredFiftyFiveEW_1447
      · exact prime_oneHundredFiftyFiveEW_1483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 64377031) ^ 32188515 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 64377031) ^ 21459010 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 64377031) ^ 12875406 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 64377031) ^ 44490 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 64377031) ^ 43410 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_67326713 : Nat.Prime 67326713 := by
  apply lucas_primality 67326713 (3 : ZMod 67326713)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (293, 1), (28723, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (293, 1), (28723, 1)] : List FactorBlock).map factorBlockValue).prod) = 67326713 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_293
      · exact prime_oneHundredFiftyFiveEW_28723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 67326713) ^ 33663356 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 67326713) ^ 229784 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 67326713) ^ 2344 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_70423439 : Nat.Prime 70423439 := by
  apply lucas_primality 70423439 (7 : ZMod 70423439)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (653, 1), (53923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (653, 1), (53923, 1)] : List FactorBlock).map factorBlockValue).prod) = 70423439 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_653
      · exact prime_oneHundredFiftyFiveEW_53923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 70423439) ^ 35211719 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (7 : ZMod 70423439) ^ 107846 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (7 : ZMod 70423439) ^ 1306 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_71869657 : Nat.Prime 71869657 := by
  apply lucas_primality 71869657 (5 : ZMod 71869657)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (29, 1), (31, 1), (3331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (29, 1), (31, 1), (3331, 1)] : List FactorBlock).map factorBlockValue).prod) = 71869657 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_29
      · exact prime_oneHundredFiftyFiveEW_31
      · exact prime_oneHundredFiftyFiveEW_3331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 71869657) ^ 35934828 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 71869657) ^ 23956552 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 71869657) ^ 2478264 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 71869657) ^ 2318376 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 71869657) ^ 21576 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_75872317 : Nat.Prime 75872317 := by
  apply lucas_primality 75872317 (5 : ZMod 75872317)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (139, 1), (3499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (139, 1), (3499, 1)] : List FactorBlock).map factorBlockValue).prod) = 75872317 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_13
      · exact prime_oneHundredFiftyFiveEW_139
      · exact prime_oneHundredFiftyFiveEW_3499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 75872317) ^ 37936158 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 75872317) ^ 25290772 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 75872317) ^ 5836332 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 75872317) ^ 545844 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 75872317) ^ 21684 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_76706647 : Nat.Prime 76706647 := by
  apply lucas_primality 76706647 (3 : ZMod 76706647)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (61, 1), (209581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (61, 1), (209581, 1)] : List FactorBlock).map factorBlockValue).prod) = 76706647 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_61
      · exact prime_oneHundredFiftyFiveEW_209581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 76706647) ^ 38353323 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 76706647) ^ 25568882 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 76706647) ^ 1257486 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 76706647) ^ 366 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_80122193 : Nat.Prime 80122193 := by
  apply lucas_primality 80122193 (3 : ZMod 80122193)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5007637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5007637, 1)] : List FactorBlock).map factorBlockValue).prod) = 80122193 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_5007637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 80122193) ^ 40061096 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 80122193) ^ 16 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_86688737 : Nat.Prime 86688737 := by
  apply lucas_primality 86688737 (3 : ZMod 86688737)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (2709023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (2709023, 1)] : List FactorBlock).map factorBlockValue).prod) = 86688737 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_2709023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 86688737) ^ 43344368 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 86688737) ^ 32 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_121891867 : Nat.Prime 121891867 := by
  apply lucas_primality 121891867 (3 : ZMod 121891867)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (109, 1), (186379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (109, 1), (186379, 1)] : List FactorBlock).map factorBlockValue).prod) = 121891867 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_109
      · exact prime_oneHundredFiftyFiveEW_186379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 121891867) ^ 60945933 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 121891867) ^ 40630622 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 121891867) ^ 1118274 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 121891867) ^ 654 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_128099591 : Nat.Prime 128099591 := by
  apply lucas_primality 128099591 (11 : ZMod 128099591)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (753527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (753527, 1)] : List FactorBlock).map factorBlockValue).prod) = 128099591 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_5
      · exact prime_oneHundredFiftyFiveEW_17
      · exact prime_oneHundredFiftyFiveEW_753527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 128099591) ^ 64049795 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (11 : ZMod 128099591) ^ 25619918 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (11 : ZMod 128099591) ^ 7535270 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (11 : ZMod 128099591) ^ 170 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_134653427 : Nat.Prime 134653427 := by
  apply lucas_primality 134653427 (2 : ZMod 134653427)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (67326713, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (67326713, 1)] : List FactorBlock).map factorBlockValue).prod) = 134653427 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_67326713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 134653427) ^ 67326713 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 134653427) ^ 2 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_136942891 : Nat.Prime 136942891 := by
  apply lucas_primality 136942891 (12 : ZMod 136942891)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (73, 1), (8933, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (73, 1), (8933, 1)] : List FactorBlock).map factorBlockValue).prod) = 136942891 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_5
      · exact prime_oneHundredFiftyFiveEW_7
      · exact prime_oneHundredFiftyFiveEW_73
      · exact prime_oneHundredFiftyFiveEW_8933
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (12 : ZMod 136942891) ^ 68471445 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (12 : ZMod 136942891) ^ 45647630 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (12 : ZMod 136942891) ^ 27388578 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (12 : ZMod 136942891) ^ 19563270 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (12 : ZMod 136942891) ^ 1875930 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (12 : ZMod 136942891) ^ 15330 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_170172619 : Nat.Prime 170172619 := by
  apply lucas_primality 170172619 (7 : ZMod 170172619)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (11, 1), (17, 1), (47, 1), (461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (11, 1), (17, 1), (47, 1), (461, 1)] : List FactorBlock).map factorBlockValue).prod) = 170172619 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_7
      · exact prime_oneHundredFiftyFiveEW_11
      · exact prime_oneHundredFiftyFiveEW_17
      · exact prime_oneHundredFiftyFiveEW_47
      · exact prime_oneHundredFiftyFiveEW_461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 170172619) ^ 85086309 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (7 : ZMod 170172619) ^ 56724206 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (7 : ZMod 170172619) ^ 24310374 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (7 : ZMod 170172619) ^ 15470238 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (7 : ZMod 170172619) ^ 10010154 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (7 : ZMod 170172619) ^ 3620694 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (7 : ZMod 170172619) ^ 369138 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_183921583 : Nat.Prime 183921583 := by
  apply lucas_primality 183921583 (5 : ZMod 183921583)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (2357969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (2357969, 1)] : List FactorBlock).map factorBlockValue).prod) = 183921583 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_13
      · exact prime_oneHundredFiftyFiveEW_2357969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 183921583) ^ 91960791 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 183921583) ^ 61307194 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 183921583) ^ 14147814 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 183921583) ^ 78 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_248933107 : Nat.Prime 248933107 := by
  apply lucas_primality 248933107 (2 : ZMod 248933107)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (43, 1), (321619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (43, 1), (321619, 1)] : List FactorBlock).map factorBlockValue).prod) = 248933107 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_43
      · exact prime_oneHundredFiftyFiveEW_321619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 248933107) ^ 124466553 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 248933107) ^ 82977702 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 248933107) ^ 5789142 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 248933107) ^ 774 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_254960869 : Nat.Prime 254960869 := by
  apply lucas_primality 254960869 (6 : ZMod 254960869)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1249, 1), (17011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1249, 1), (17011, 1)] : List FactorBlock).map factorBlockValue).prod) = 254960869 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_1249
      · exact prime_oneHundredFiftyFiveEW_17011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 254960869) ^ 127480434 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (6 : ZMod 254960869) ^ 84986956 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (6 : ZMod 254960869) ^ 204132 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (6 : ZMod 254960869) ^ 14988 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_266087923 : Nat.Prime 266087923 := by
  apply lucas_primality 266087923 (2 : ZMod 266087923)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2657, 1), (16691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2657, 1), (16691, 1)] : List FactorBlock).map factorBlockValue).prod) = 266087923 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_2657
      · exact prime_oneHundredFiftyFiveEW_16691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 266087923) ^ 133043961 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 266087923) ^ 88695974 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 266087923) ^ 100146 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 266087923) ^ 15942 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_292530349 : Nat.Prime 292530349 := by
  apply lucas_primality 292530349 (2 : ZMod 292530349)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (11, 1), (738713, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (11, 1), (738713, 1)] : List FactorBlock).map factorBlockValue).prod) = 292530349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_11
      · exact prime_oneHundredFiftyFiveEW_738713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 292530349) ^ 146265174 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 292530349) ^ 97510116 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 292530349) ^ 26593668 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 292530349) ^ 396 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_313871053 : Nat.Prime 313871053 := by
  apply lucas_primality 313871053 (2 : ZMod 313871053)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (239, 1), (9949, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (239, 1), (9949, 1)] : List FactorBlock).map factorBlockValue).prod) = 313871053 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_11
      · exact prime_oneHundredFiftyFiveEW_239
      · exact prime_oneHundredFiftyFiveEW_9949
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 313871053) ^ 156935526 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 313871053) ^ 104623684 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 313871053) ^ 28533732 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 313871053) ^ 1313268 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 313871053) ^ 31548 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_330684953 : Nat.Prime 330684953 := by
  apply lucas_primality 330684953 (3 : ZMod 330684953)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (17, 1), (359, 1), (521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (17, 1), (359, 1), (521, 1)] : List FactorBlock).map factorBlockValue).prod) = 330684953 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_13
      · exact prime_oneHundredFiftyFiveEW_17
      · exact prime_oneHundredFiftyFiveEW_359
      · exact prime_oneHundredFiftyFiveEW_521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 330684953) ^ 165342476 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 330684953) ^ 25437304 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 330684953) ^ 19452056 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 330684953) ^ 921128 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 330684953) ^ 634712 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_349751209 : Nat.Prime 349751209 := by
  apply lucas_primality 349751209 (7 : ZMod 349751209)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (313, 1), (46559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (313, 1), (46559, 1)] : List FactorBlock).map factorBlockValue).prod) = 349751209 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_313
      · exact prime_oneHundredFiftyFiveEW_46559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 349751209) ^ 174875604 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (7 : ZMod 349751209) ^ 116583736 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (7 : ZMod 349751209) ^ 1117416 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (7 : ZMod 349751209) ^ 7512 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_349875439 : Nat.Prime 349875439 := by
  apply lucas_primality 349875439 (3 : ZMod 349875439)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (5301143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (5301143, 1)] : List FactorBlock).map factorBlockValue).prod) = 349875439 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_11
      · exact prime_oneHundredFiftyFiveEW_5301143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 349875439) ^ 174937719 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 349875439) ^ 116625146 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 349875439) ^ 31806858 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 349875439) ^ 66 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_362051087 : Nat.Prime 362051087 := by
  apply lucas_primality 362051087 (5 : ZMod 362051087)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (12539, 1), (14437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (12539, 1), (14437, 1)] : List FactorBlock).map factorBlockValue).prod) = 362051087 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_12539
      · exact prime_oneHundredFiftyFiveEW_14437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 362051087) ^ 181025543 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 362051087) ^ 28874 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 362051087) ^ 25078 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_416853259 : Nat.Prime 416853259 := by
  apply lucas_primality 416853259 (2 : ZMod 416853259)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5659, 1), (12277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5659, 1), (12277, 1)] : List FactorBlock).map factorBlockValue).prod) = 416853259 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_5659
      · exact prime_oneHundredFiftyFiveEW_12277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 416853259) ^ 208426629 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 416853259) ^ 138951086 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 416853259) ^ 73662 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 416853259) ^ 33954 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_486985013 : Nat.Prime 486985013 := by
  apply lucas_primality 486985013 (2 : ZMod 486985013)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (2851, 1), (42703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (2851, 1), (42703, 1)] : List FactorBlock).map factorBlockValue).prod) = 486985013 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_2851
      · exact prime_oneHundredFiftyFiveEW_42703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 486985013) ^ 243492506 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 486985013) ^ 170812 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 486985013) ^ 11404 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_520132423 : Nat.Prime 520132423 := by
  apply lucas_primality 520132423 (3 : ZMod 520132423)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (86688737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (86688737, 1)] : List FactorBlock).map factorBlockValue).prod) = 520132423 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_86688737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 520132423) ^ 260066211 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 520132423) ^ 173377474 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 520132423) ^ 6 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_530657371 : Nat.Prime 530657371 := by
  apply lucas_primality 530657371 (2 : ZMod 530657371)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (29, 1), (203317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (29, 1), (203317, 1)] : List FactorBlock).map factorBlockValue).prod) = 530657371 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_5
      · exact prime_oneHundredFiftyFiveEW_29
      · exact prime_oneHundredFiftyFiveEW_203317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 530657371) ^ 265328685 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 530657371) ^ 176885790 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 530657371) ^ 106131474 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 530657371) ^ 18298530 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 530657371) ^ 2610 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_544020469 : Nat.Prime 544020469 := by
  apply lucas_primality 544020469 (2 : ZMod 544020469)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (131, 1), (20357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (131, 1), (20357, 1)] : List FactorBlock).map factorBlockValue).prod) = 544020469 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_17
      · exact prime_oneHundredFiftyFiveEW_131
      · exact prime_oneHundredFiftyFiveEW_20357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 544020469) ^ 272010234 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 544020469) ^ 181340156 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 544020469) ^ 32001204 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 544020469) ^ 4152828 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 544020469) ^ 26724 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_584271647 : Nat.Prime 584271647 := by
  apply lucas_primality 584271647 (5 : ZMod 584271647)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (41733689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (41733689, 1)] : List FactorBlock).map factorBlockValue).prod) = 584271647 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_7
      · exact prime_oneHundredFiftyFiveEW_41733689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 584271647) ^ 292135823 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 584271647) ^ 83467378 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 584271647) ^ 14 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_605733413 : Nat.Prime 605733413 := by
  apply lucas_primality 605733413 (2 : ZMod 605733413)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (59, 1), (2566667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (59, 1), (2566667, 1)] : List FactorBlock).map factorBlockValue).prod) = 605733413 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_59
      · exact prime_oneHundredFiftyFiveEW_2566667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 605733413) ^ 302866706 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 605733413) ^ 10266668 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 605733413) ^ 236 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_646860439 : Nat.Prime 646860439 := by
  apply lucas_primality 646860439 (3 : ZMod 646860439)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 1), (17, 1), (43, 1), (2341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 1), (17, 1), (43, 1), (2341, 1)] : List FactorBlock).map factorBlockValue).prod) = 646860439 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_7
      · exact prime_oneHundredFiftyFiveEW_17
      · exact prime_oneHundredFiftyFiveEW_43
      · exact prime_oneHundredFiftyFiveEW_2341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 646860439) ^ 323430219 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 646860439) ^ 215620146 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 646860439) ^ 92408634 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 646860439) ^ 38050614 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 646860439) ^ 15043266 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 646860439) ^ 276318 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_673577423 : Nat.Prime 673577423 := by
  apply lucas_primality 673577423 (7 : ZMod 673577423)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (829, 1), (8291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (829, 1), (8291, 1)] : List FactorBlock).map factorBlockValue).prod) = 673577423 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_7
      · exact prime_oneHundredFiftyFiveEW_829
      · exact prime_oneHundredFiftyFiveEW_8291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 673577423) ^ 336788711 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (7 : ZMod 673577423) ^ 96225346 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (7 : ZMod 673577423) ^ 812518 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (7 : ZMod 673577423) ^ 81242 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_714027719 : Nat.Prime 714027719 := by
  apply lucas_primality 714027719 (11 : ZMod 714027719)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) = 714027719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_17203
      · exact prime_oneHundredFiftyFiveEW_20753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 714027719) ^ 357013859 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 41506 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 34406 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_735686333 : Nat.Prime 735686333 := by
  apply lucas_primality 735686333 (2 : ZMod 735686333)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (183921583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (183921583, 1)] : List FactorBlock).map factorBlockValue).prod) = 735686333 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_183921583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 735686333) ^ 367843166 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 735686333) ^ 4 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_767066471 : Nat.Prime 767066471 := by
  apply lucas_primality 767066471 (13 : ZMod 767066471)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (76706647, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (76706647, 1)] : List FactorBlock).map factorBlockValue).prod) = 767066471 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_5
      · exact prime_oneHundredFiftyFiveEW_76706647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 767066471) ^ 383533235 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (13 : ZMod 767066471) ^ 153413294 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (13 : ZMod 767066471) ^ 10 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_927150877 : Nat.Prime 927150877 := by
  apply lucas_primality 927150877 (2 : ZMod 927150877)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (41, 1), (449, 1), (1399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (41, 1), (449, 1), (1399, 1)] : List FactorBlock).map factorBlockValue).prod) = 927150877 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_41
      · exact prime_oneHundredFiftyFiveEW_449
      · exact prime_oneHundredFiftyFiveEW_1399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 927150877) ^ 463575438 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 927150877) ^ 309050292 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 927150877) ^ 22613436 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 927150877) ^ 2064924 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 927150877) ^ 662724 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_946301827 : Nat.Prime 946301827 := by
  apply lucas_primality 946301827 (2 : ZMod 946301827)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (59, 1), (167, 1), (16007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (59, 1), (167, 1), (16007, 1)] : List FactorBlock).map factorBlockValue).prod) = 946301827 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_59
      · exact prime_oneHundredFiftyFiveEW_167
      · exact prime_oneHundredFiftyFiveEW_16007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 946301827) ^ 473150913 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 946301827) ^ 315433942 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 946301827) ^ 16039014 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 946301827) ^ 5666478 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 946301827) ^ 59118 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_966324071 : Nat.Prime 966324071 := by
  apply lucas_primality 966324071 (11 : ZMod 966324071)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (23, 1), (4201409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (23, 1), (4201409, 1)] : List FactorBlock).map factorBlockValue).prod) = 966324071 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_5
      · exact prime_oneHundredFiftyFiveEW_23
      · exact prime_oneHundredFiftyFiveEW_4201409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 966324071) ^ 483162035 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (11 : ZMod 966324071) ^ 193264814 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (11 : ZMod 966324071) ^ 42014090 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (11 : ZMod 966324071) ^ 230 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_1065360407 : Nat.Prime 1065360407 := by
  apply lucas_primality 1065360407 (5 : ZMod 1065360407)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (48425473, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (48425473, 1)] : List FactorBlock).map factorBlockValue).prod) = 1065360407 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_11
      · exact prime_oneHundredFiftyFiveEW_48425473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1065360407) ^ 532680203 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 1065360407) ^ 96850946 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 1065360407) ^ 22 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_1067600917 : Nat.Prime 1067600917 := by
  apply lucas_primality 1067600917 (2 : ZMod 1067600917)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (29655581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (29655581, 1)] : List FactorBlock).map factorBlockValue).prod) = 1067600917 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_29655581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1067600917) ^ 533800458 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1067600917) ^ 355866972 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1067600917) ^ 36 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_1114172737 : Nat.Prime 1114172737 := by
  apply lucas_primality 1114172737 (7 : ZMod 1114172737)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (31, 1), (187193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (31, 1), (187193, 1)] : List FactorBlock).map factorBlockValue).prod) = 1114172737 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_31
      · exact prime_oneHundredFiftyFiveEW_187193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 1114172737) ^ 557086368 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (7 : ZMod 1114172737) ^ 371390912 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (7 : ZMod 1114172737) ^ 35941056 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (7 : ZMod 1114172737) ^ 5952 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_1170121397 : Nat.Prime 1170121397 := by
  apply lucas_primality 1170121397 (2 : ZMod 1170121397)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (292530349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (292530349, 1)] : List FactorBlock).map factorBlockValue).prod) = 1170121397 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_292530349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 1170121397) ^ 585060698 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1170121397) ^ 4 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_1399501757 : Nat.Prime 1399501757 := by
  apply lucas_primality 1399501757 (2 : ZMod 1399501757)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (349875439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (349875439, 1)] : List FactorBlock).map factorBlockValue).prod) = 1399501757 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_349875439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 1399501757) ^ 699750878 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1399501757) ^ 4 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_1448141729 : Nat.Prime 1448141729 := by
  apply lucas_primality 1448141729 (6 : ZMod 1448141729)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (11, 1), (149, 1), (27611, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (11, 1), (149, 1), (27611, 1)] : List FactorBlock).map factorBlockValue).prod) = 1448141729 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_11
      · exact prime_oneHundredFiftyFiveEW_149
      · exact prime_oneHundredFiftyFiveEW_27611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 1448141729) ^ 724070864 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (6 : ZMod 1448141729) ^ 131649248 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (6 : ZMod 1448141729) ^ 9719072 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (6 : ZMod 1448141729) ^ 52448 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_1596527539 : Nat.Prime 1596527539 := by
  apply lucas_primality 1596527539 (3 : ZMod 1596527539)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (266087923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (266087923, 1)] : List FactorBlock).map factorBlockValue).prod) = 1596527539 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_266087923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1596527539) ^ 798263769 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 1596527539) ^ 532175846 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 1596527539) ^ 6 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_1709400449 : Nat.Prime 1709400449 := by
  apply lucas_primality 1709400449 (3 : ZMod 1709400449)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (7, 1), (199, 1), (9587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (7, 1), (199, 1), (9587, 1)] : List FactorBlock).map factorBlockValue).prod) = 1709400449 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_7
      · exact prime_oneHundredFiftyFiveEW_199
      · exact prime_oneHundredFiftyFiveEW_9587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1709400449) ^ 854700224 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 1709400449) ^ 244200064 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 1709400449) ^ 8589952 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 1709400449) ^ 178304 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_1724456831 : Nat.Prime 1724456831 := by
  apply lucas_primality 1724456831 (11 : ZMod 1724456831)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (101, 1), (1249, 1), (1367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (101, 1), (1249, 1), (1367, 1)] : List FactorBlock).map factorBlockValue).prod) = 1724456831 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_5
      · exact prime_oneHundredFiftyFiveEW_101
      · exact prime_oneHundredFiftyFiveEW_1249
      · exact prime_oneHundredFiftyFiveEW_1367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 1724456831) ^ 862228415 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (11 : ZMod 1724456831) ^ 344891366 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (11 : ZMod 1724456831) ^ 17073830 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (11 : ZMod 1724456831) ^ 1380670 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (11 : ZMod 1724456831) ^ 1261490 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_1790719019 : Nat.Prime 1790719019 := by
  apply lucas_primality 1790719019 (2 : ZMod 1790719019)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (4937, 1), (16487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (4937, 1), (16487, 1)] : List FactorBlock).map factorBlockValue).prod) = 1790719019 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_11
      · exact prime_oneHundredFiftyFiveEW_4937
      · exact prime_oneHundredFiftyFiveEW_16487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1790719019) ^ 895359509 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1790719019) ^ 162792638 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1790719019) ^ 362714 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1790719019) ^ 108614 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_2120463239 : Nat.Prime 2120463239 := by
  apply lucas_primality 2120463239 (11 : ZMod 2120463239)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (1999, 1), (18289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (1999, 1), (18289, 1)] : List FactorBlock).map factorBlockValue).prod) = 2120463239 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_29
      · exact prime_oneHundredFiftyFiveEW_1999
      · exact prime_oneHundredFiftyFiveEW_18289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 2120463239) ^ 1060231619 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (11 : ZMod 2120463239) ^ 73119422 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (11 : ZMod 2120463239) ^ 1060762 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (11 : ZMod 2120463239) ^ 115942 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_2183060261 : Nat.Prime 2183060261 := by
  apply lucas_primality 2183060261 (2 : ZMod 2183060261)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (29, 1), (3763897, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (29, 1), (3763897, 1)] : List FactorBlock).map factorBlockValue).prod) = 2183060261 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_5
      · exact prime_oneHundredFiftyFiveEW_29
      · exact prime_oneHundredFiftyFiveEW_3763897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2183060261) ^ 1091530130 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2183060261) ^ 436612052 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2183060261) ^ 75277940 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2183060261) ^ 580 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_2315802857 : Nat.Prime 2315802857 := by
  apply lucas_primality 2315802857 (3 : ZMod 2315802857)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (14867, 1), (19471, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (14867, 1), (19471, 1)] : List FactorBlock).map factorBlockValue).prod) = 2315802857 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_14867
      · exact prime_oneHundredFiftyFiveEW_19471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2315802857) ^ 1157901428 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 2315802857) ^ 155768 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 2315802857) ^ 118936 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_2499456221 : Nat.Prime 2499456221 := by
  apply lucas_primality 2499456221 (2 : ZMod 2499456221)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (31, 1), (1523, 1), (2647, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (31, 1), (1523, 1), (2647, 1)] : List FactorBlock).map factorBlockValue).prod) = 2499456221 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_5
      · exact prime_oneHundredFiftyFiveEW_31
      · exact prime_oneHundredFiftyFiveEW_1523
      · exact prime_oneHundredFiftyFiveEW_2647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2499456221) ^ 1249728110 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2499456221) ^ 499891244 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2499456221) ^ 80627620 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2499456221) ^ 1641140 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2499456221) ^ 944260 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_3472827529 : Nat.Prime 3472827529 := by
  apply lucas_primality 3472827529 (14 : ZMod 3472827529)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (311, 1), (465277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (311, 1), (465277, 1)] : List FactorBlock).map factorBlockValue).prod) = 3472827529 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_311
      · exact prime_oneHundredFiftyFiveEW_465277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 3472827529) ^ 1736413764 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (14 : ZMod 3472827529) ^ 1157609176 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (14 : ZMod 3472827529) ^ 11166648 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (14 : ZMod 3472827529) ^ 7464 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_3739216211 : Nat.Prime 3739216211 := by
  apply lucas_primality 3739216211 (2 : ZMod 3739216211)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (29, 1), (103, 1), (125183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (29, 1), (103, 1), (125183, 1)] : List FactorBlock).map factorBlockValue).prod) = 3739216211 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_5
      · exact prime_oneHundredFiftyFiveEW_29
      · exact prime_oneHundredFiftyFiveEW_103
      · exact prime_oneHundredFiftyFiveEW_125183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3739216211) ^ 1869608105 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 3739216211) ^ 747843242 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 3739216211) ^ 128938490 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 3739216211) ^ 36303070 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 3739216211) ^ 29870 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_4224182269 : Nat.Prime 4224182269 := by
  apply lucas_primality 4224182269 (2 : ZMod 4224182269)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7159, 1), (49171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7159, 1), (49171, 1)] : List FactorBlock).map factorBlockValue).prod) = 4224182269 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_7159
      · exact prime_oneHundredFiftyFiveEW_49171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4224182269) ^ 2112091134 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 4224182269) ^ 1408060756 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 4224182269) ^ 590052 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 4224182269) ^ 85908 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_4240926479 : Nat.Prime 4240926479 := by
  apply lucas_primality 4240926479 (11 : ZMod 4240926479)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2120463239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2120463239, 1)] : List FactorBlock).map factorBlockValue).prod) = 4240926479 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_2120463239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (11 : ZMod 4240926479) ^ 2120463239 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (11 : ZMod 4240926479) ^ 2 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_4516788161 : Nat.Prime 4516788161 := by
  apply lucas_primality 4516788161 (3 : ZMod 4516788161)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (5, 1), (14114963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (5, 1), (14114963, 1)] : List FactorBlock).map factorBlockValue).prod) = 4516788161 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_5
      · exact prime_oneHundredFiftyFiveEW_14114963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 4516788161) ^ 2258394080 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 4516788161) ^ 903357632 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 4516788161) ^ 320 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_4736598421 : Nat.Prime 4736598421 := by
  apply lucas_primality 4736598421 (2 : ZMod 4736598421)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (29, 1), (311, 1), (8753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (29, 1), (311, 1), (8753, 1)] : List FactorBlock).map factorBlockValue).prod) = 4736598421 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_5
      · exact prime_oneHundredFiftyFiveEW_29
      · exact prime_oneHundredFiftyFiveEW_311
      · exact prime_oneHundredFiftyFiveEW_8753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4736598421) ^ 2368299210 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 4736598421) ^ 1578866140 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 4736598421) ^ 947319684 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 4736598421) ^ 163330980 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 4736598421) ^ 15230220 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 4736598421) ^ 541140 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_4914987577 : Nat.Prime 4914987577 := by
  apply lucas_primality 4914987577 (5 : ZMod 4914987577)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (23, 1), (1471, 1), (6053, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (23, 1), (1471, 1), (6053, 1)] : List FactorBlock).map factorBlockValue).prod) = 4914987577 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_23
      · exact prime_oneHundredFiftyFiveEW_1471
      · exact prime_oneHundredFiftyFiveEW_6053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 4914987577) ^ 2457493788 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 4914987577) ^ 1638329192 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 4914987577) ^ 213695112 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 4914987577) ^ 3341256 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 4914987577) ^ 811992 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_5127911323 : Nat.Prime 5127911323 := by
  apply lucas_primality 5127911323 (3 : ZMod 5127911323)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (109, 1), (271, 1), (28933, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (109, 1), (271, 1), (28933, 1)] : List FactorBlock).map factorBlockValue).prod) = 5127911323 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_109
      · exact prime_oneHundredFiftyFiveEW_271
      · exact prime_oneHundredFiftyFiveEW_28933
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 5127911323) ^ 2563955661 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 5127911323) ^ 1709303774 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 5127911323) ^ 47045058 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 5127911323) ^ 18922182 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 5127911323) ^ 177234 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_5422144757 : Nat.Prime 5422144757 := by
  apply lucas_primality 5422144757 (2 : ZMod 5422144757)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (71, 1), (2727437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (71, 1), (2727437, 1)] : List FactorBlock).map factorBlockValue).prod) = 5422144757 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_7
      · exact prime_oneHundredFiftyFiveEW_71
      · exact prime_oneHundredFiftyFiveEW_2727437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5422144757) ^ 2711072378 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 5422144757) ^ 774592108 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 5422144757) ^ 76368236 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 5422144757) ^ 1988 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_6037638679 : Nat.Prime 6037638679 := by
  apply lucas_primality 6037638679 (3 : ZMod 6037638679)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) = 6037638679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_31
      · exact prime_oneHundredFiftyFiveEW_10820141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6037638679) ^ 3018819339 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 2012546226 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 194762538 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 558 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_6100455703 : Nat.Prime 6100455703 := by
  apply lucas_primality 6100455703 (6 : ZMod 6100455703)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (6011, 1), (15377, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (6011, 1), (15377, 1)] : List FactorBlock).map factorBlockValue).prod) = 6100455703 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_11
      · exact prime_oneHundredFiftyFiveEW_6011
      · exact prime_oneHundredFiftyFiveEW_15377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 6100455703) ^ 3050227851 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (6 : ZMod 6100455703) ^ 2033485234 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (6 : ZMod 6100455703) ^ 554586882 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (6 : ZMod 6100455703) ^ 1014882 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (6 : ZMod 6100455703) ^ 396726 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_7553699507 : Nat.Prime 7553699507 := by
  apply lucas_primality 7553699507 (2 : ZMod 7553699507)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (673, 1), (181031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (673, 1), (181031, 1)] : List FactorBlock).map factorBlockValue).prod) = 7553699507 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_31
      · exact prime_oneHundredFiftyFiveEW_673
      · exact prime_oneHundredFiftyFiveEW_181031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7553699507) ^ 3776849753 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 7553699507) ^ 243667726 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 7553699507) ^ 11223922 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 7553699507) ^ 41726 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_8184194567 : Nat.Prime 8184194567 := by
  apply lucas_primality 8184194567 (5 : ZMod 8184194567)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (71, 2), (811763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (71, 2), (811763, 1)] : List FactorBlock).map factorBlockValue).prod) = 8184194567 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_71
      · exact prime_oneHundredFiftyFiveEW_811763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 8184194567) ^ 4092097283 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 8184194567) ^ 115270346 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 8184194567) ^ 10082 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_8325551827 : Nat.Prime 8325551827 := by
  apply lucas_primality 8325551827 (3 : ZMod 8325551827)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (29, 2), (549977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (29, 2), (549977, 1)] : List FactorBlock).map factorBlockValue).prod) = 8325551827 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_29
      · exact prime_oneHundredFiftyFiveEW_549977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 8325551827) ^ 4162775913 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 8325551827) ^ 2775183942 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 8325551827) ^ 287087994 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 8325551827) ^ 15138 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_8556762187 : Nat.Prime 8556762187 := by
  apply lucas_primality 8556762187 (2 : ZMod 8556762187)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 1), (251, 1), (90187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 1), (251, 1), (90187, 1)] : List FactorBlock).map factorBlockValue).prod) = 8556762187 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_7
      · exact prime_oneHundredFiftyFiveEW_251
      · exact prime_oneHundredFiftyFiveEW_90187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8556762187) ^ 4278381093 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 8556762187) ^ 2852254062 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 8556762187) ^ 1222394598 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 8556762187) ^ 34090686 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 8556762187) ^ 94878 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_8719229287 : Nat.Prime 8719229287 := by
  apply lucas_primality 8719229287 (3 : ZMod 8719229287)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 6), (5980267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 6), (5980267, 1)] : List FactorBlock).map factorBlockValue).prod) = 8719229287 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_5980267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 8719229287) ^ 4359614643 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 8719229287) ^ 2906409762 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 8719229287) ^ 1458 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_9672156961 : Nat.Prime 9672156961 := by
  apply lucas_primality 9672156961 (7 : ZMod 9672156961)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 1), (20150327, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 1), (20150327, 1)] : List FactorBlock).map factorBlockValue).prod) = 9672156961 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_5
      · exact prime_oneHundredFiftyFiveEW_20150327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 9672156961) ^ 4836078480 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (7 : ZMod 9672156961) ^ 3224052320 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (7 : ZMod 9672156961) ^ 1934431392 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (7 : ZMod 9672156961) ^ 480 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_9720384403 : Nat.Prime 9720384403 := by
  apply lucas_primality 9720384403 (2 : ZMod 9720384403)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (59, 1), (269, 1), (102077, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (59, 1), (269, 1), (102077, 1)] : List FactorBlock).map factorBlockValue).prod) = 9720384403 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_59
      · exact prime_oneHundredFiftyFiveEW_269
      · exact prime_oneHundredFiftyFiveEW_102077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9720384403) ^ 4860192201 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 9720384403) ^ 3240128134 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 9720384403) ^ 164752278 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 9720384403) ^ 36135258 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 9720384403) ^ 95226 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_10019466463 : Nat.Prime 10019466463 := by
  apply lucas_primality 10019466463 (3 : ZMod 10019466463)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (193, 1), (8652389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (193, 1), (8652389, 1)] : List FactorBlock).map factorBlockValue).prod) = 10019466463 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_193
      · exact prime_oneHundredFiftyFiveEW_8652389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 10019466463) ^ 5009733231 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 10019466463) ^ 3339822154 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 10019466463) ^ 51914334 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 10019466463) ^ 1158 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_10158208721 : Nat.Prime 10158208721 := by
  apply lucas_primality 10158208721 (3 : ZMod 10158208721)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (11, 1), (3119, 1), (3701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (11, 1), (3119, 1), (3701, 1)] : List FactorBlock).map factorBlockValue).prod) = 10158208721 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_5
      · exact prime_oneHundredFiftyFiveEW_11
      · exact prime_oneHundredFiftyFiveEW_3119
      · exact prime_oneHundredFiftyFiveEW_3701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 10158208721) ^ 5079104360 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 10158208721) ^ 2031641744 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 10158208721) ^ 923473520 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 10158208721) ^ 3256880 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 10158208721) ^ 2744720 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_10309963273 : Nat.Prime 10309963273 := by
  apply lucas_primality 10309963273 (5 : ZMod 10309963273)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (37, 1), (1658617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (37, 1), (1658617, 1)] : List FactorBlock).map factorBlockValue).prod) = 10309963273 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_7
      · exact prime_oneHundredFiftyFiveEW_37
      · exact prime_oneHundredFiftyFiveEW_1658617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 10309963273) ^ 5154981636 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 10309963273) ^ 3436654424 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 10309963273) ^ 1472851896 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 10309963273) ^ 278647656 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 10309963273) ^ 6216 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_11907887471 : Nat.Prime 11907887471 := by
  apply lucas_primality 11907887471 (7 : ZMod 11907887471)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (61, 1), (383, 1), (50969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (61, 1), (383, 1), (50969, 1)] : List FactorBlock).map factorBlockValue).prod) = 11907887471 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_5
      · exact prime_oneHundredFiftyFiveEW_61
      · exact prime_oneHundredFiftyFiveEW_383
      · exact prime_oneHundredFiftyFiveEW_50969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 11907887471) ^ 5953943735 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (7 : ZMod 11907887471) ^ 2381577494 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (7 : ZMod 11907887471) ^ 195211270 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (7 : ZMod 11907887471) ^ 31091090 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (7 : ZMod 11907887471) ^ 233630 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_12132144301 : Nat.Prime 12132144301 := by
  apply lucas_primality 12132144301 (2 : ZMod 12132144301)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (40440481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (40440481, 1)] : List FactorBlock).map factorBlockValue).prod) = 12132144301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_5
      · exact prime_oneHundredFiftyFiveEW_40440481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 12132144301) ^ 6066072150 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 12132144301) ^ 4044048100 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 12132144301) ^ 2426428860 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 12132144301) ^ 300 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_12669926383 : Nat.Prime 12669926383 := by
  apply lucas_primality 12669926383 (3 : ZMod 12669926383)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (103, 1), (557, 1), (12269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (103, 1), (557, 1), (12269, 1)] : List FactorBlock).map factorBlockValue).prod) = 12669926383 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_103
      · exact prime_oneHundredFiftyFiveEW_557
      · exact prime_oneHundredFiftyFiveEW_12269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 12669926383) ^ 6334963191 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 12669926383) ^ 4223308794 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 12669926383) ^ 123008994 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 12669926383) ^ 22746726 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 12669926383) ^ 1032678 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_14696942957 : Nat.Prime 14696942957 := by
  apply lucas_primality 14696942957 (2 : ZMod 14696942957)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1279, 1), (2872741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1279, 1), (2872741, 1)] : List FactorBlock).map factorBlockValue).prod) = 14696942957 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_1279
      · exact prime_oneHundredFiftyFiveEW_2872741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 14696942957) ^ 7348471478 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 14696942957) ^ 11490964 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 14696942957) ^ 5116 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_15383461057 : Nat.Prime 15383461057 := by
  apply lucas_primality 15383461057 (5 : ZMod 15383461057)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (80122193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (80122193, 1)] : List FactorBlock).map factorBlockValue).prod) = 15383461057 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_80122193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 15383461057) ^ 7691730528 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 15383461057) ^ 5127820352 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 15383461057) ^ 192 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_19329914629 : Nat.Prime 19329914629 := by
  apply lucas_primality 19329914629 (6 : ZMod 19329914629)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (89, 1), (2011019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (89, 1), (2011019, 1)] : List FactorBlock).map factorBlockValue).prod) = 19329914629 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_89
      · exact prime_oneHundredFiftyFiveEW_2011019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 19329914629) ^ 9664957314 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (6 : ZMod 19329914629) ^ 6443304876 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (6 : ZMod 19329914629) ^ 217190052 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (6 : ZMod 19329914629) ^ 9612 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_23242647853 : Nat.Prime 23242647853 := by
  apply lucas_primality 23242647853 (2 : ZMod 23242647853)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (277, 1), (743, 1), (3137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (277, 1), (743, 1), (3137, 1)] : List FactorBlock).map factorBlockValue).prod) = 23242647853 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_277
      · exact prime_oneHundredFiftyFiveEW_743
      · exact prime_oneHundredFiftyFiveEW_3137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 23242647853) ^ 11621323926 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 23242647853) ^ 7747549284 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 23242647853) ^ 83908476 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 23242647853) ^ 31282164 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 23242647853) ^ 7409196 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_24401822813 : Nat.Prime 24401822813 := by
  apply lucas_primality 24401822813 (2 : ZMod 24401822813)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (6100455703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (6100455703, 1)] : List FactorBlock).map factorBlockValue).prod) = 24401822813 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_6100455703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 24401822813) ^ 12200911406 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 24401822813) ^ 4 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_26334580033 : Nat.Prime 26334580033 := by
  apply lucas_primality 26334580033 (7 : ZMod 26334580033)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 4), (19, 1), (167, 1), (1601, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 4), (19, 1), (167, 1), (1601, 1)] : List FactorBlock).map factorBlockValue).prod) = 26334580033 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_19
      · exact prime_oneHundredFiftyFiveEW_167
      · exact prime_oneHundredFiftyFiveEW_1601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 26334580033) ^ 13167290016 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (7 : ZMod 26334580033) ^ 8778193344 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (7 : ZMod 26334580033) ^ 1386030528 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (7 : ZMod 26334580033) ^ 157692096 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (7 : ZMod 26334580033) ^ 16448832 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_27585443707 : Nat.Prime 27585443707 := by
  apply lucas_primality 27585443707 (2 : ZMod 27585443707)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (41341, 1), (111211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (41341, 1), (111211, 1)] : List FactorBlock).map factorBlockValue).prod) = 27585443707 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_41341
      · exact prime_oneHundredFiftyFiveEW_111211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 27585443707) ^ 13792721853 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 27585443707) ^ 9195147902 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 27585443707) ^ 667266 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 27585443707) ^ 248046 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_29180663749 : Nat.Prime 29180663749 := by
  apply lucas_primality 29180663749 (2 : ZMod 29180663749)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 5), (30021259, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 5), (30021259, 1)] : List FactorBlock).map factorBlockValue).prod) = 29180663749 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_30021259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 29180663749) ^ 14590331874 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 29180663749) ^ 9726887916 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 29180663749) ^ 972 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_35864414309 : Nat.Prime 35864414309 := by
  apply lucas_primality 35864414309 (2 : ZMod 35864414309)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (6229, 1), (1439413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (6229, 1), (1439413, 1)] : List FactorBlock).map factorBlockValue).prod) = 35864414309 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_6229
      · exact prime_oneHundredFiftyFiveEW_1439413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 35864414309) ^ 17932207154 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 35864414309) ^ 5757652 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 35864414309) ^ 24916 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_37724809081 : Nat.Prime 37724809081 := by
  apply lucas_primality 37724809081 (19 : ZMod 37724809081)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (7, 1), (2477, 1), (18131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (7, 1), (2477, 1), (18131, 1)] : List FactorBlock).map factorBlockValue).prod) = 37724809081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_5
      · exact prime_oneHundredFiftyFiveEW_7
      · exact prime_oneHundredFiftyFiveEW_2477
      · exact prime_oneHundredFiftyFiveEW_18131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 37724809081) ^ 18862404540 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (19 : ZMod 37724809081) ^ 12574936360 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (19 : ZMod 37724809081) ^ 7544961816 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (19 : ZMod 37724809081) ^ 5389258440 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (19 : ZMod 37724809081) ^ 15230040 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (19 : ZMod 37724809081) ^ 2080680 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_38527480421 : Nat.Prime 38527480421 := by
  apply lucas_primality 38527480421 (7 : ZMod 38527480421)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (11, 1), (13, 1), (13471147, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (11, 1), (13, 1), (13471147, 1)] : List FactorBlock).map factorBlockValue).prod) = 38527480421 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_5
      · exact prime_oneHundredFiftyFiveEW_11
      · exact prime_oneHundredFiftyFiveEW_13
      · exact prime_oneHundredFiftyFiveEW_13471147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 38527480421) ^ 19263740210 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (7 : ZMod 38527480421) ^ 7705496084 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (7 : ZMod 38527480421) ^ 3502498220 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (7 : ZMod 38527480421) ^ 2963652340 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (7 : ZMod 38527480421) ^ 2860 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_52886288569 : Nat.Prime 52886288569 := by
  apply lucas_primality 52886288569 (23 : ZMod 52886288569)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (19, 1), (257, 1), (451279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (19, 1), (257, 1), (451279, 1)] : List FactorBlock).map factorBlockValue).prod) = 52886288569 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_19
      · exact prime_oneHundredFiftyFiveEW_257
      · exact prime_oneHundredFiftyFiveEW_451279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 52886288569) ^ 26443144284 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (23 : ZMod 52886288569) ^ 17628762856 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (23 : ZMod 52886288569) ^ 2783488872 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (23 : ZMod 52886288569) ^ 205783224 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (23 : ZMod 52886288569) ^ 117192 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_94595042561 : Nat.Prime 94595042561 := by
  apply lucas_primality 94595042561 (3 : ZMod 94595042561)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (5, 1), (41, 1), (47, 1), (38351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (5, 1), (41, 1), (47, 1), (38351, 1)] : List FactorBlock).map factorBlockValue).prod) = 94595042561 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_5
      · exact prime_oneHundredFiftyFiveEW_41
      · exact prime_oneHundredFiftyFiveEW_47
      · exact prime_oneHundredFiftyFiveEW_38351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 94595042561) ^ 47297521280 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 94595042561) ^ 18919008512 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 94595042561) ^ 2307196160 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 94595042561) ^ 2012660480 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 94595042561) ^ 2466560 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_97393251023 : Nat.Prime 97393251023 := by
  apply lucas_primality 97393251023 (5 : ZMod 97393251023)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (463, 1), (2143, 1), (2887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (463, 1), (2143, 1), (2887, 1)] : List FactorBlock).map factorBlockValue).prod) = 97393251023 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_17
      · exact prime_oneHundredFiftyFiveEW_463
      · exact prime_oneHundredFiftyFiveEW_2143
      · exact prime_oneHundredFiftyFiveEW_2887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 97393251023) ^ 48696625511 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 97393251023) ^ 5729014766 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 97393251023) ^ 210352594 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 97393251023) ^ 45447154 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 97393251023) ^ 33735106 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_105211804913 : Nat.Prime 105211804913 := by
  apply lucas_primality 105211804913 (3 : ZMod 105211804913)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (52529, 1), (125183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (52529, 1), (125183, 1)] : List FactorBlock).map factorBlockValue).prod) = 105211804913 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_52529
      · exact prime_oneHundredFiftyFiveEW_125183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 105211804913) ^ 52605902456 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 105211804913) ^ 2002928 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 105211804913) ^ 840464 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_117938908511 : Nat.Prime 117938908511 := by
  apply lucas_primality 117938908511 (7 : ZMod 117938908511)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (317, 1), (37204703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (317, 1), (37204703, 1)] : List FactorBlock).map factorBlockValue).prod) = 117938908511 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_5
      · exact prime_oneHundredFiftyFiveEW_317
      · exact prime_oneHundredFiftyFiveEW_37204703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 117938908511) ^ 58969454255 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (7 : ZMod 117938908511) ^ 23587781702 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (7 : ZMod 117938908511) ^ 372047030 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (7 : ZMod 117938908511) ^ 3170 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_132659164751 : Nat.Prime 132659164751 := by
  apply lucas_primality 132659164751 (7 : ZMod 132659164751)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 3), (7, 1), (617, 1), (122861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 3), (7, 1), (617, 1), (122861, 1)] : List FactorBlock).map factorBlockValue).prod) = 132659164751 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_5
      · exact prime_oneHundredFiftyFiveEW_7
      · exact prime_oneHundredFiftyFiveEW_617
      · exact prime_oneHundredFiftyFiveEW_122861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 132659164751) ^ 66329582375 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (7 : ZMod 132659164751) ^ 26531832950 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (7 : ZMod 132659164751) ^ 18951309250 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (7 : ZMod 132659164751) ^ 215006750 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (7 : ZMod 132659164751) ^ 1079750 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_138184461083 : Nat.Prime 138184461083 := by
  apply lucas_primality 138184461083 (2 : ZMod 138184461083)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (178793, 1), (386437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (178793, 1), (386437, 1)] : List FactorBlock).map factorBlockValue).prod) = 138184461083 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_178793
      · exact prime_oneHundredFiftyFiveEW_386437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 138184461083) ^ 69092230541 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 138184461083) ^ 772874 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 138184461083) ^ 357586 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_140168308879 : Nat.Prime 140168308879 := by
  apply lucas_primality 140168308879 (3 : ZMod 140168308879)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (853, 1), (702239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (853, 1), (702239, 1)] : List FactorBlock).map factorBlockValue).prod) = 140168308879 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_13
      · exact prime_oneHundredFiftyFiveEW_853
      · exact prime_oneHundredFiftyFiveEW_702239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 140168308879) ^ 70084154439 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 140168308879) ^ 46722769626 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 140168308879) ^ 10782177606 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 140168308879) ^ 164323926 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 140168308879) ^ 199602 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_142036641083 : Nat.Prime 142036641083 := by
  apply lucas_primality 142036641083 (2 : ZMod 142036641083)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (23, 1), (659, 1), (669359, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (23, 1), (659, 1), (669359, 1)] : List FactorBlock).map factorBlockValue).prod) = 142036641083 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_7
      · exact prime_oneHundredFiftyFiveEW_23
      · exact prime_oneHundredFiftyFiveEW_659
      · exact prime_oneHundredFiftyFiveEW_669359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 142036641083) ^ 71018320541 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 142036641083) ^ 20290948726 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 142036641083) ^ 6175506134 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 142036641083) ^ 215533598 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 142036641083) ^ 212198 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_160311463409 : Nat.Prime 160311463409 := by
  apply lucas_primality 160311463409 (3 : ZMod 160311463409)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (10019466463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (10019466463, 1)] : List FactorBlock).map factorBlockValue).prod) = 160311463409 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_10019466463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 160311463409) ^ 80155731704 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 160311463409) ^ 16 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_175130129981 : Nat.Prime 175130129981 := by
  apply lucas_primality 175130129981 (2 : ZMod 175130129981)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (13, 1), (673577423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (13, 1), (673577423, 1)] : List FactorBlock).map factorBlockValue).prod) = 175130129981 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_5
      · exact prime_oneHundredFiftyFiveEW_13
      · exact prime_oneHundredFiftyFiveEW_673577423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 175130129981) ^ 87565064990 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 175130129981) ^ 35026025996 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 175130129981) ^ 13471548460 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 175130129981) ^ 260 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_176714430539 : Nat.Prime 176714430539 := by
  apply lucas_primality 176714430539 (6 : ZMod 176714430539)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 2), (67, 1), (107, 1), (34141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 2), (67, 1), (107, 1), (34141, 1)] : List FactorBlock).map factorBlockValue).prod) = 176714430539 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_19
      · exact prime_oneHundredFiftyFiveEW_67
      · exact prime_oneHundredFiftyFiveEW_107
      · exact prime_oneHundredFiftyFiveEW_34141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 176714430539) ^ 88357215269 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (6 : ZMod 176714430539) ^ 9300759502 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (6 : ZMod 176714430539) ^ 2637528814 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (6 : ZMod 176714430539) ^ 1651536734 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (6 : ZMod 176714430539) ^ 5176018 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_178847081891 : Nat.Prime 178847081891 := by
  apply lucas_primality 178847081891 (2 : ZMod 178847081891)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (19, 1), (3517, 1), (267643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (19, 1), (3517, 1), (267643, 1)] : List FactorBlock).map factorBlockValue).prod) = 178847081891 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_5
      · exact prime_oneHundredFiftyFiveEW_19
      · exact prime_oneHundredFiftyFiveEW_3517
      · exact prime_oneHundredFiftyFiveEW_267643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 178847081891) ^ 89423540945 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 178847081891) ^ 35769416378 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 178847081891) ^ 9413004310 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 178847081891) ^ 50852170 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 178847081891) ^ 668230 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_209261502889 : Nat.Prime 209261502889 := by
  apply lucas_primality 209261502889 (7 : ZMod 209261502889)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (8719229287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (8719229287, 1)] : List FactorBlock).map factorBlockValue).prod) = 209261502889 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_8719229287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 209261502889) ^ 104630751444 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (7 : ZMod 209261502889) ^ 69753834296 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (7 : ZMod 209261502889) ^ 24 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_252599319787 : Nat.Prime 252599319787 := by
  apply lucas_primality 252599319787 (11 : ZMod 252599319787)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (54319, 1), (70459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (54319, 1), (70459, 1)] : List FactorBlock).map factorBlockValue).prod) = 252599319787 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_11
      · exact prime_oneHundredFiftyFiveEW_54319
      · exact prime_oneHundredFiftyFiveEW_70459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 252599319787) ^ 126299659893 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (11 : ZMod 252599319787) ^ 84199773262 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (11 : ZMod 252599319787) ^ 22963574526 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (11 : ZMod 252599319787) ^ 4650294 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (11 : ZMod 252599319787) ^ 3585054 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_261758733737 : Nat.Prime 261758733737 := by
  apply lucas_primality 261758733737 (3 : ZMod 261758733737)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (409, 1), (2657, 1), (30109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (409, 1), (2657, 1), (30109, 1)] : List FactorBlock).map factorBlockValue).prod) = 261758733737 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_409
      · exact prime_oneHundredFiftyFiveEW_2657
      · exact prime_oneHundredFiftyFiveEW_30109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 261758733737) ^ 130879366868 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 261758733737) ^ 639996904 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 261758733737) ^ 98516648 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 261758733737) ^ 8693704 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_267072507463 : Nat.Prime 267072507463 := by
  apply lucas_primality 267072507463 (5 : ZMod 267072507463)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (50549, 1), (880573, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (50549, 1), (880573, 1)] : List FactorBlock).map factorBlockValue).prod) = 267072507463 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_50549
      · exact prime_oneHundredFiftyFiveEW_880573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 267072507463) ^ 133536253731 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 267072507463) ^ 89024169154 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 267072507463) ^ 5283438 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 267072507463) ^ 303294 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_416739303481 : Nat.Prime 416739303481 := by
  apply lucas_primality 416739303481 (11 : ZMod 416739303481)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (3472827529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (3472827529, 1)] : List FactorBlock).map factorBlockValue).prod) = 416739303481 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_5
      · exact prime_oneHundredFiftyFiveEW_3472827529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 416739303481) ^ 208369651740 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (11 : ZMod 416739303481) ^ 138913101160 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (11 : ZMod 416739303481) ^ 83347860696 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (11 : ZMod 416739303481) ^ 120 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_430631084717 : Nat.Prime 430631084717 := by
  apply lucas_primality 430631084717 (2 : ZMod 430631084717)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 3), (313871053, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 3), (313871053, 1)] : List FactorBlock).map factorBlockValue).prod) = 430631084717 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_7
      · exact prime_oneHundredFiftyFiveEW_313871053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 430631084717) ^ 215315542358 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 430631084717) ^ 61518726388 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 430631084717) ^ 1372 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_456117349789 : Nat.Prime 456117349789 := by
  apply lucas_primality 456117349789 (2 : ZMod 456117349789)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (12669926383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (12669926383, 1)] : List FactorBlock).map factorBlockValue).prod) = 456117349789 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_12669926383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 456117349789) ^ 228058674894 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 456117349789) ^ 152039116596 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 456117349789) ^ 36 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_528325673479 : Nat.Prime 528325673479 := by
  apply lucas_primality 528325673479 (6 : ZMod 528325673479)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (643, 1), (136942891, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (643, 1), (136942891, 1)] : List FactorBlock).map factorBlockValue).prod) = 528325673479 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_643
      · exact prime_oneHundredFiftyFiveEW_136942891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 528325673479) ^ 264162836739 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (6 : ZMod 528325673479) ^ 176108557826 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (6 : ZMod 528325673479) ^ 821657346 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (6 : ZMod 528325673479) ^ 3858 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_662117699701 : Nat.Prime 662117699701 := by
  apply lucas_primality 662117699701 (2 : ZMod 662117699701)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 2), (735686333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 2), (735686333, 1)] : List FactorBlock).map factorBlockValue).prod) = 662117699701 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_5
      · exact prime_oneHundredFiftyFiveEW_735686333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 662117699701) ^ 331058849850 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 662117699701) ^ 220705899900 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 662117699701) ^ 132423539940 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 662117699701) ^ 900 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_877547463371 : Nat.Prime 877547463371 := by
  apply lucas_primality 877547463371 (2 : ZMod 877547463371)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (37, 1), (173, 1), (487, 1), (28151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (37, 1), (173, 1), (487, 1), (28151, 1)] : List FactorBlock).map factorBlockValue).prod) = 877547463371 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_5
      · exact prime_oneHundredFiftyFiveEW_37
      · exact prime_oneHundredFiftyFiveEW_173
      · exact prime_oneHundredFiftyFiveEW_487
      · exact prime_oneHundredFiftyFiveEW_28151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 877547463371) ^ 438773731685 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 877547463371) ^ 175509492674 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 877547463371) ^ 23717499010 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 877547463371) ^ 5072528690 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 877547463371) ^ 1801945510 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 877547463371) ^ 31172870 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_894479506643 : Nat.Prime 894479506643 := by
  apply lucas_primality 894479506643 (5 : ZMod 894479506643)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (151, 1), (239, 1), (487, 1), (25447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (151, 1), (239, 1), (487, 1), (25447, 1)] : List FactorBlock).map factorBlockValue).prod) = 894479506643 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_151
      · exact prime_oneHundredFiftyFiveEW_239
      · exact prime_oneHundredFiftyFiveEW_487
      · exact prime_oneHundredFiftyFiveEW_25447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 894479506643) ^ 447239753321 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 894479506643) ^ 5923705342 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 894479506643) ^ 3742592078 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 894479506643) ^ 1836713566 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 894479506643) ^ 35150686 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_920027503337 : Nat.Prime 920027503337 := by
  apply lucas_primality 920027503337 (3 : ZMod 920027503337)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (109883, 1), (1046599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (109883, 1), (1046599, 1)] : List FactorBlock).map factorBlockValue).prod) = 920027503337 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_109883
      · exact prime_oneHundredFiftyFiveEW_1046599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 920027503337) ^ 460013751668 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 920027503337) ^ 8372792 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 920027503337) ^ 879064 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_944400024157 : Nat.Prime 944400024157 := by
  apply lucas_primality 944400024157 (2 : ZMod 944400024157)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (96769, 1), (813277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (96769, 1), (813277, 1)] : List FactorBlock).map factorBlockValue).prod) = 944400024157 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_96769
      · exact prime_oneHundredFiftyFiveEW_813277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 944400024157) ^ 472200012078 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 944400024157) ^ 314800008052 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 944400024157) ^ 9759324 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 944400024157) ^ 1161228 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_1039013926961 : Nat.Prime 1039013926961 := by
  apply lucas_primality 1039013926961 (6 : ZMod 1039013926961)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (1949, 1), (6663763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (1949, 1), (6663763, 1)] : List FactorBlock).map factorBlockValue).prod) = 1039013926961 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_5
      · exact prime_oneHundredFiftyFiveEW_1949
      · exact prime_oneHundredFiftyFiveEW_6663763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 1039013926961) ^ 519506963480 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (6 : ZMod 1039013926961) ^ 207802785392 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (6 : ZMod 1039013926961) ^ 533101040 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (6 : ZMod 1039013926961) ^ 155920 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_1196372512243 : Nat.Prime 1196372512243 := by
  apply lucas_primality 1196372512243 (2 : ZMod 1196372512243)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (89, 1), (248933107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (89, 1), (248933107, 1)] : List FactorBlock).map factorBlockValue).prod) = 1196372512243 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_89
      · exact prime_oneHundredFiftyFiveEW_248933107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1196372512243) ^ 598186256121 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1196372512243) ^ 398790837414 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1196372512243) ^ 13442387778 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1196372512243) ^ 4806 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_1261190340353 : Nat.Prime 1261190340353 := by
  apply lucas_primality 1261190340353 (3 : ZMod 1261190340353)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (23, 1), (79, 1), (2711351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (23, 1), (79, 1), (2711351, 1)] : List FactorBlock).map factorBlockValue).prod) = 1261190340353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_23
      · exact prime_oneHundredFiftyFiveEW_79
      · exact prime_oneHundredFiftyFiveEW_2711351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1261190340353) ^ 630595170176 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 1261190340353) ^ 54834362624 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 1261190340353) ^ 15964434688 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 1261190340353) ^ 465152 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_1610443463141 : Nat.Prime 1610443463141 := by
  apply lucas_primality 1610443463141 (2 : ZMod 1610443463141)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (17, 1), (4736598421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (17, 1), (4736598421, 1)] : List FactorBlock).map factorBlockValue).prod) = 1610443463141 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_5
      · exact prime_oneHundredFiftyFiveEW_17
      · exact prime_oneHundredFiftyFiveEW_4736598421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1610443463141) ^ 805221731570 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1610443463141) ^ 322088692628 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1610443463141) ^ 94731968420 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1610443463141) ^ 340 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_1880954544613 : Nat.Prime 1880954544613 := by
  apply lucas_primality 1880954544613 (2 : ZMod 1880954544613)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (13, 2), (31, 1), (293, 1), (9283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (13, 2), (31, 1), (293, 1), (9283, 1)] : List FactorBlock).map factorBlockValue).prod) = 1880954544613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_11
      · exact prime_oneHundredFiftyFiveEW_13
      · exact prime_oneHundredFiftyFiveEW_31
      · exact prime_oneHundredFiftyFiveEW_293
      · exact prime_oneHundredFiftyFiveEW_9283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1880954544613) ^ 940477272306 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1880954544613) ^ 626984848204 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1880954544613) ^ 170995867692 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1880954544613) ^ 144688811124 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1880954544613) ^ 60675953052 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1880954544613) ^ 6419640084 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1880954544613) ^ 202623564 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_1933828254263 : Nat.Prime 1933828254263 := by
  apply lucas_primality 1933828254263 (5 : ZMod 1933828254263)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (113, 1), (8556762187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (113, 1), (8556762187, 1)] : List FactorBlock).map factorBlockValue).prod) = 1933828254263 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_113
      · exact prime_oneHundredFiftyFiveEW_8556762187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1933828254263) ^ 966914127131 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 1933828254263) ^ 17113524374 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 1933828254263) ^ 226 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_2928612849443 : Nat.Prime 2928612849443 := by
  apply lucas_primality 2928612849443 (2 : ZMod 2928612849443)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (23, 1), (71, 1), (128099591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (23, 1), (71, 1), (128099591, 1)] : List FactorBlock).map factorBlockValue).prod) = 2928612849443 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_7
      · exact prime_oneHundredFiftyFiveEW_23
      · exact prime_oneHundredFiftyFiveEW_71
      · exact prime_oneHundredFiftyFiveEW_128099591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2928612849443) ^ 1464306424721 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2928612849443) ^ 418373264206 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2928612849443) ^ 127330993454 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2928612849443) ^ 41248068302 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2928612849443) ^ 22862 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_3487470611201 : Nat.Prime 3487470611201 := by
  apply lucas_primality 3487470611201 (3 : ZMod 3487470611201)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (5, 2), (19, 1), (28679857, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (5, 2), (19, 1), (28679857, 1)] : List FactorBlock).map factorBlockValue).prod) = 3487470611201 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_5
      · exact prime_oneHundredFiftyFiveEW_19
      · exact prime_oneHundredFiftyFiveEW_28679857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3487470611201) ^ 1743735305600 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 3487470611201) ^ 697494122240 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 3487470611201) ^ 183551084800 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 3487470611201) ^ 121600 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_4195008883981 : Nat.Prime 4195008883981 := by
  apply lucas_primality 4195008883981 (6 : ZMod 4195008883981)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (131, 1), (197, 1), (903073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (131, 1), (197, 1), (903073, 1)] : List FactorBlock).map factorBlockValue).prod) = 4195008883981 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_5
      · exact prime_oneHundredFiftyFiveEW_131
      · exact prime_oneHundredFiftyFiveEW_197
      · exact prime_oneHundredFiftyFiveEW_903073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 4195008883981) ^ 2097504441990 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (6 : ZMod 4195008883981) ^ 1398336294660 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (6 : ZMod 4195008883981) ^ 839001776796 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (6 : ZMod 4195008883981) ^ 32022968580 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (6 : ZMod 4195008883981) ^ 21294461340 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (6 : ZMod 4195008883981) ^ 4645260 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_4439648997587 : Nat.Prime 4439648997587 := by
  apply lucas_primality 4439648997587 (2 : ZMod 4439648997587)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (5557, 1), (36314959, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (5557, 1), (36314959, 1)] : List FactorBlock).map factorBlockValue).prod) = 4439648997587 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_11
      · exact prime_oneHundredFiftyFiveEW_5557
      · exact prime_oneHundredFiftyFiveEW_36314959
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4439648997587) ^ 2219824498793 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 4439648997587) ^ 403604454326 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 4439648997587) ^ 798929098 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 4439648997587) ^ 122254 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_4785490048973 : Nat.Prime 4785490048973 := by
  apply lucas_primality 4785490048973 (2 : ZMod 4785490048973)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1196372512243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1196372512243, 1)] : List FactorBlock).map factorBlockValue).prod) = 4785490048973 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_1196372512243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 4785490048973) ^ 2392745024486 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 4785490048973) ^ 4 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_5520165020023 : Nat.Prime 5520165020023 := by
  apply lucas_primality 5520165020023 (3 : ZMod 5520165020023)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (920027503337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (920027503337, 1)] : List FactorBlock).map factorBlockValue).prod) = 5520165020023 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_920027503337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 5520165020023) ^ 2760082510011 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 5520165020023) ^ 1840055006674 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 5520165020023) ^ 6 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_5652348850381 : Nat.Prime 5652348850381 := by
  apply lucas_primality 5652348850381 (6 : ZMod 5652348850381)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (88813, 1), (1060721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (88813, 1), (1060721, 1)] : List FactorBlock).map factorBlockValue).prod) = 5652348850381 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_5
      · exact prime_oneHundredFiftyFiveEW_88813
      · exact prime_oneHundredFiftyFiveEW_1060721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 5652348850381) ^ 2826174425190 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (6 : ZMod 5652348850381) ^ 1884116283460 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (6 : ZMod 5652348850381) ^ 1130469770076 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (6 : ZMod 5652348850381) ^ 63643260 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (6 : ZMod 5652348850381) ^ 5328780 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_5742223874797 : Nat.Prime 5742223874797 := by
  apply lucas_primality 5742223874797 (2 : ZMod 5742223874797)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 2), (3389, 1), (488573, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 2), (3389, 1), (488573, 1)] : List FactorBlock).map factorBlockValue).prod) = 5742223874797 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_17
      · exact prime_oneHundredFiftyFiveEW_3389
      · exact prime_oneHundredFiftyFiveEW_488573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5742223874797) ^ 2871111937398 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 5742223874797) ^ 1914074624932 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 5742223874797) ^ 337777874988 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 5742223874797) ^ 1694371164 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 5742223874797) ^ 11753052 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_6143585213707 : Nat.Prime 6143585213707 := by
  apply lucas_primality 6143585213707 (2 : ZMod 6143585213707)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (599, 1), (1709400449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (599, 1), (1709400449, 1)] : List FactorBlock).map factorBlockValue).prod) = 6143585213707 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_599
      · exact prime_oneHundredFiftyFiveEW_1709400449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 6143585213707) ^ 3071792606853 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 6143585213707) ^ 2047861737902 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 6143585213707) ^ 10256402694 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 6143585213707) ^ 3594 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_6621176997011 : Nat.Prime 6621176997011 := by
  apply lucas_primality 6621176997011 (2 : ZMod 6621176997011)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (662117699701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (662117699701, 1)] : List FactorBlock).map factorBlockValue).prod) = 6621176997011 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_5
      · exact prime_oneHundredFiftyFiveEW_662117699701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 6621176997011) ^ 3310588498505 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 6621176997011) ^ 1324235399402 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 6621176997011) ^ 10 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_6806167501039 : Nat.Prime 6806167501039 := by
  apply lucas_primality 6806167501039 (6 : ZMod 6806167501039)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (86813, 1), (13066721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (86813, 1), (13066721, 1)] : List FactorBlock).map factorBlockValue).prod) = 6806167501039 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_86813
      · exact prime_oneHundredFiftyFiveEW_13066721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 6806167501039) ^ 3403083750519 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (6 : ZMod 6806167501039) ^ 2268722500346 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (6 : ZMod 6806167501039) ^ 78400326 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (6 : ZMod 6806167501039) ^ 520878 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_8865429861271 : Nat.Prime 8865429861271 := by
  apply lucas_primality 8865429861271 (3 : ZMod 8865429861271)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (105277, 1), (2807017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (105277, 1), (2807017, 1)] : List FactorBlock).map factorBlockValue).prod) = 8865429861271 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_5
      · exact prime_oneHundredFiftyFiveEW_105277
      · exact prime_oneHundredFiftyFiveEW_2807017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 8865429861271) ^ 4432714930635 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 8865429861271) ^ 2955143287090 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 8865429861271) ^ 1773085972254 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 8865429861271) ^ 84210510 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 8865429861271) ^ 3158310 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_13217372915987 : Nat.Prime 13217372915987 := by
  apply lucas_primality 13217372915987 (2 : ZMod 13217372915987)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (641, 1), (10309963273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (641, 1), (10309963273, 1)] : List FactorBlock).map factorBlockValue).prod) = 13217372915987 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_641
      · exact prime_oneHundredFiftyFiveEW_10309963273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 13217372915987) ^ 6608686457993 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 13217372915987) ^ 20619926546 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 13217372915987) ^ 1282 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_15928074143053 : Nat.Prime 15928074143053 := by
  apply lucas_primality 15928074143053 (2 : ZMod 15928074143053)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (324529, 1), (4090049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (324529, 1), (4090049, 1)] : List FactorBlock).map factorBlockValue).prod) = 15928074143053 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_324529
      · exact prime_oneHundredFiftyFiveEW_4090049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 15928074143053) ^ 7964037071526 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 15928074143053) ^ 5309358047684 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 15928074143053) ^ 49080588 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 15928074143053) ^ 3894348 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_28970749284089 : Nat.Prime 28970749284089 := by
  apply lucas_primality 28970749284089 (3 : ZMod 28970749284089)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (57457, 1), (63027023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (57457, 1), (63027023, 1)] : List FactorBlock).map factorBlockValue).prod) = 28970749284089 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_57457
      · exact prime_oneHundredFiftyFiveEW_63027023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 28970749284089) ^ 14485374642044 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 28970749284089) ^ 504216184 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 28970749284089) ^ 459656 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_32790948849179 : Nat.Prime 32790948849179 := by
  apply lucas_primality 32790948849179 (2 : ZMod 32790948849179)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (1261190340353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (1261190340353, 1)] : List FactorBlock).map factorBlockValue).prod) = 32790948849179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_13
      · exact prime_oneHundredFiftyFiveEW_1261190340353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 32790948849179) ^ 16395474424589 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 32790948849179) ^ 2522380680706 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 32790948849179) ^ 26 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_35509041075533 : Nat.Prime 35509041075533 := by
  apply lucas_primality 35509041075533 (2 : ZMod 35509041075533)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (71, 1), (163, 1), (767066471, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (71, 1), (163, 1), (767066471, 1)] : List FactorBlock).map factorBlockValue).prod) = 35509041075533 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_71
      · exact prime_oneHundredFiftyFiveEW_163
      · exact prime_oneHundredFiftyFiveEW_767066471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 35509041075533) ^ 17754520537766 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 35509041075533) ^ 500127339092 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 35509041075533) ^ 217846877764 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 35509041075533) ^ 46292 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_35574519037801 : Nat.Prime 35574519037801 := by
  apply lucas_primality 35574519037801 (19 : ZMod 35574519037801)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 2), (73, 1), (829, 1), (971, 1), (1009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 2), (73, 1), (829, 1), (971, 1), (1009, 1)] : List FactorBlock).map factorBlockValue).prod) = 35574519037801 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_5
      · exact prime_oneHundredFiftyFiveEW_73
      · exact prime_oneHundredFiftyFiveEW_829
      · exact prime_oneHundredFiftyFiveEW_971
      · exact prime_oneHundredFiftyFiveEW_1009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 35574519037801) ^ 17787259518900 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (19 : ZMod 35574519037801) ^ 11858173012600 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (19 : ZMod 35574519037801) ^ 7114903807560 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (19 : ZMod 35574519037801) ^ 487322178600 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (19 : ZMod 35574519037801) ^ 42912568200 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (19 : ZMod 35574519037801) ^ 36636991800 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (19 : ZMod 35574519037801) ^ 35257204200 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_37582392935323 : Nat.Prime 37582392935323 := by
  apply lucas_primality 37582392935323 (3 : ZMod 37582392935323)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (52009, 1), (13381727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (52009, 1), (13381727, 1)] : List FactorBlock).map factorBlockValue).prod) = 37582392935323 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_52009
      · exact prime_oneHundredFiftyFiveEW_13381727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 37582392935323) ^ 18791196467661 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 37582392935323) ^ 12527464311774 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 37582392935323) ^ 722613258 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 37582392935323) ^ 2808486 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_40916184207103 : Nat.Prime 40916184207103 := by
  apply lucas_primality 40916184207103 (3 : ZMod 40916184207103)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (59, 1), (38527480421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (59, 1), (38527480421, 1)] : List FactorBlock).map factorBlockValue).prod) = 40916184207103 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_59
      · exact prime_oneHundredFiftyFiveEW_38527480421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 40916184207103) ^ 20458092103551 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 40916184207103) ^ 13638728069034 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 40916184207103) ^ 693494647578 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 40916184207103) ^ 1062 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_64360559390279 : Nat.Prime 64360559390279 := by
  apply lucas_primality 64360559390279 (17 : ZMod 64360559390279)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (67, 1), (149, 1), (1493, 1), (2159081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (67, 1), (149, 1), (1493, 1), (2159081, 1)] : List FactorBlock).map factorBlockValue).prod) = 64360559390279 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_67
      · exact prime_oneHundredFiftyFiveEW_149
      · exact prime_oneHundredFiftyFiveEW_1493
      · exact prime_oneHundredFiftyFiveEW_2159081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 64360559390279) ^ 32180279695139 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (17 : ZMod 64360559390279) ^ 960605364034 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (17 : ZMod 64360559390279) ^ 431950063022 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (17 : ZMod 64360559390279) ^ 43108211246 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (17 : ZMod 64360559390279) ^ 29809238 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_98398592508329 : Nat.Prime 98398592508329 := by
  apply lucas_primality 98398592508329 (3 : ZMod 98398592508329)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (19, 1), (37, 1), (2499456221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (19, 1), (37, 1), (2499456221, 1)] : List FactorBlock).map factorBlockValue).prod) = 98398592508329 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_7
      · exact prime_oneHundredFiftyFiveEW_19
      · exact prime_oneHundredFiftyFiveEW_37
      · exact prime_oneHundredFiftyFiveEW_2499456221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 98398592508329) ^ 49199296254164 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 98398592508329) ^ 14056941786904 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 98398592508329) ^ 5178873289912 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 98398592508329) ^ 2659421419144 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 98398592508329) ^ 39368 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_100257985466497 : Nat.Prime 100257985466497 := by
  apply lucas_primality 100257985466497 (5 : ZMod 100257985466497)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 2), (11, 1), (13, 1), (19, 1), (173, 1), (185153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 2), (11, 1), (13, 1), (19, 1), (173, 1), (185153, 1)] : List FactorBlock).map factorBlockValue).prod) = 100257985466497 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_11
      · exact prime_oneHundredFiftyFiveEW_13
      · exact prime_oneHundredFiftyFiveEW_19
      · exact prime_oneHundredFiftyFiveEW_173
      · exact prime_oneHundredFiftyFiveEW_185153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 100257985466497) ^ 50128992733248 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 100257985466497) ^ 33419328488832 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 100257985466497) ^ 9114362315136 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 100257985466497) ^ 7712152728192 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 100257985466497) ^ 5276736077184 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 100257985466497) ^ 579525927552 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 100257985466497) ^ 541487232 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_112846402628291 : Nat.Prime 112846402628291 := by
  apply lucas_primality 112846402628291 (2 : ZMod 112846402628291)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (2147051, 1), (5255879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (2147051, 1), (5255879, 1)] : List FactorBlock).map factorBlockValue).prod) = 112846402628291 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_5
      · exact prime_oneHundredFiftyFiveEW_2147051
      · exact prime_oneHundredFiftyFiveEW_5255879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 112846402628291) ^ 56423201314145 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 112846402628291) ^ 22569280525658 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 112846402628291) ^ 52558790 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 112846402628291) ^ 21470510 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_142363093773557 : Nat.Prime 142363093773557 := by
  apply lucas_primality 142363093773557 (2 : ZMod 142363093773557)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1697, 1), (5233, 1), (4007789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1697, 1), (5233, 1), (4007789, 1)] : List FactorBlock).map factorBlockValue).prod) = 142363093773557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_1697
      · exact prime_oneHundredFiftyFiveEW_5233
      · exact prime_oneHundredFiftyFiveEW_4007789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 142363093773557) ^ 71181546886778 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 142363093773557) ^ 83891039348 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 142363093773557) ^ 27204871732 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 142363093773557) ^ 35521604 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_191136889716637 : Nat.Prime 191136889716637 := by
  apply lucas_primality 191136889716637 (6 : ZMod 191136889716637)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (15928074143053, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (15928074143053, 1)] : List FactorBlock).map factorBlockValue).prod) = 191136889716637 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_15928074143053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 191136889716637) ^ 95568444858318 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (6 : ZMod 191136889716637) ^ 63712296572212 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (6 : ZMod 191136889716637) ^ 12 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_213315936919609 : Nat.Prime 213315936919609 := by
  apply lucas_primality 213315936919609 (14 : ZMod 213315936919609)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (67, 1), (132659164751, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (67, 1), (132659164751, 1)] : List FactorBlock).map factorBlockValue).prod) = 213315936919609 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_67
      · exact prime_oneHundredFiftyFiveEW_132659164751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 213315936919609) ^ 106657968459804 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (14 : ZMod 213315936919609) ^ 71105312306536 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (14 : ZMod 213315936919609) ^ 3183819954024 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (14 : ZMod 213315936919609) ^ 1608 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_220109419994249 : Nat.Prime 220109419994249 := by
  apply lucas_primality 220109419994249 (3 : ZMod 220109419994249)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (467, 1), (8839, 1), (6665437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (467, 1), (8839, 1), (6665437, 1)] : List FactorBlock).map factorBlockValue).prod) = 220109419994249 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_467
      · exact prime_oneHundredFiftyFiveEW_8839
      · exact prime_oneHundredFiftyFiveEW_6665437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 220109419994249) ^ 110054709997124 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 220109419994249) ^ 471326381144 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 220109419994249) ^ 24902072632 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 220109419994249) ^ 33022504 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_228654674135581 : Nat.Prime 228654674135581 := by
  apply lucas_primality 228654674135581 (6 : ZMod 228654674135581)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (11, 1), (31, 1), (1596527539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (11, 1), (31, 1), (1596527539, 1)] : List FactorBlock).map factorBlockValue).prod) = 228654674135581 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_5
      · exact prime_oneHundredFiftyFiveEW_7
      · exact prime_oneHundredFiftyFiveEW_11
      · exact prime_oneHundredFiftyFiveEW_31
      · exact prime_oneHundredFiftyFiveEW_1596527539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 228654674135581) ^ 114327337067790 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (6 : ZMod 228654674135581) ^ 76218224711860 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (6 : ZMod 228654674135581) ^ 45730934827116 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (6 : ZMod 228654674135581) ^ 32664953447940 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (6 : ZMod 228654674135581) ^ 20786788557780 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (6 : ZMod 228654674135581) ^ 7375957230180 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (6 : ZMod 228654674135581) ^ 143220 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_245497105242619 : Nat.Prime 245497105242619 := by
  apply lucas_primality 245497105242619 (2 : ZMod 245497105242619)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (40916184207103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (40916184207103, 1)] : List FactorBlock).map factorBlockValue).prod) = 245497105242619 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_40916184207103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 245497105242619) ^ 122748552621309 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 245497105242619) ^ 81832368414206 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 245497105242619) ^ 6 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_287963224557181 : Nat.Prime 287963224557181 := by
  apply lucas_primality 287963224557181 (6 : ZMod 287963224557181)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (19, 1), (252599319787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (19, 1), (252599319787, 1)] : List FactorBlock).map factorBlockValue).prod) = 287963224557181 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_5
      · exact prime_oneHundredFiftyFiveEW_19
      · exact prime_oneHundredFiftyFiveEW_252599319787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 287963224557181) ^ 143981612278590 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (6 : ZMod 287963224557181) ^ 95987741519060 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (6 : ZMod 287963224557181) ^ 57592644911436 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (6 : ZMod 287963224557181) ^ 15155959187220 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (6 : ZMod 287963224557181) ^ 1140 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_406110667980943 : Nat.Prime 406110667980943 := by
  apply lucas_primality 406110667980943 (3 : ZMod 406110667980943)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 6), (3617, 1), (3851, 1), (19997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 6), (3617, 1), (3851, 1), (19997, 1)] : List FactorBlock).map factorBlockValue).prod) = 406110667980943 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_3617
      · exact prime_oneHundredFiftyFiveEW_3851
      · exact prime_oneHundredFiftyFiveEW_19997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 406110667980943) ^ 203055333990471 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 406110667980943) ^ 135370222660314 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 406110667980943) ^ 112278315726 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 406110667980943) ^ 105455899242 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 406110667980943) ^ 20308579686 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_451989040489319 : Nat.Prime 451989040489319 := by
  apply lucas_primality 451989040489319 (7 : ZMod 451989040489319)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (181, 1), (2137, 1), (584271647, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (181, 1), (2137, 1), (584271647, 1)] : List FactorBlock).map factorBlockValue).prod) = 451989040489319 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_181
      · exact prime_oneHundredFiftyFiveEW_2137
      · exact prime_oneHundredFiftyFiveEW_584271647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 451989040489319) ^ 225994520244659 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (7 : ZMod 451989040489319) ^ 2497177019278 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (7 : ZMod 451989040489319) ^ 211506336214 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (7 : ZMod 451989040489319) ^ 773594 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_507296309771731 : Nat.Prime 507296309771731 := by
  apply lucas_primality 507296309771731 (2 : ZMod 507296309771731)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (613, 1), (27585443707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (613, 1), (27585443707, 1)] : List FactorBlock).map factorBlockValue).prod) = 507296309771731 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_5
      · exact prime_oneHundredFiftyFiveEW_613
      · exact prime_oneHundredFiftyFiveEW_27585443707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 507296309771731) ^ 253648154885865 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 507296309771731) ^ 169098769923910 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 507296309771731) ^ 101459261954346 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 507296309771731) ^ 827563311210 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 507296309771731) ^ 18390 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_1456698734350081 : Nat.Prime 1456698734350081 := by
  apply lucas_primality 1456698734350081 (11 : ZMod 1456698734350081)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 1), (5, 1), (13, 1), (29180663749, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 1), (5, 1), (13, 1), (29180663749, 1)] : List FactorBlock).map factorBlockValue).prod) = 1456698734350081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_5
      · exact prime_oneHundredFiftyFiveEW_13
      · exact prime_oneHundredFiftyFiveEW_29180663749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 1456698734350081) ^ 728349367175040 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (11 : ZMod 1456698734350081) ^ 485566244783360 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (11 : ZMod 1456698734350081) ^ 291339746870016 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (11 : ZMod 1456698734350081) ^ 112053748796160 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (11 : ZMod 1456698734350081) ^ 49920 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_1514000198503267 : Nat.Prime 1514000198503267 := by
  apply lucas_primality 1514000198503267 (2 : ZMod 1514000198503267)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (605329, 1), (416853259, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (605329, 1), (416853259, 1)] : List FactorBlock).map factorBlockValue).prod) = 1514000198503267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_605329
      · exact prime_oneHundredFiftyFiveEW_416853259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1514000198503267) ^ 757000099251633 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1514000198503267) ^ 504666732834422 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1514000198503267) ^ 2501119554 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1514000198503267) ^ 3631974 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_2279752948297301 : Nat.Prime 2279752948297301 := by
  apply lucas_primality 2279752948297301 (10 : ZMod 2279752948297301)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (7, 1), (149, 1), (2851, 1), (7666661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (7, 1), (149, 1), (2851, 1), (7666661, 1)] : List FactorBlock).map factorBlockValue).prod) = 2279752948297301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_5
      · exact prime_oneHundredFiftyFiveEW_7
      · exact prime_oneHundredFiftyFiveEW_149
      · exact prime_oneHundredFiftyFiveEW_2851
      · exact prime_oneHundredFiftyFiveEW_7666661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 2279752948297301) ^ 1139876474148650 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (10 : ZMod 2279752948297301) ^ 455950589659460 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (10 : ZMod 2279752948297301) ^ 325678992613900 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (10 : ZMod 2279752948297301) ^ 15300355357700 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (10 : ZMod 2279752948297301) ^ 799632742300 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (10 : ZMod 2279752948297301) ^ 297359300 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_2337532415679887 : Nat.Prime 2337532415679887 := by
  apply lucas_primality 2337532415679887 (5 : ZMod 2337532415679887)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (347, 1), (6089, 1), (7307, 1), (75703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (347, 1), (6089, 1), (7307, 1), (75703, 1)] : List FactorBlock).map factorBlockValue).prod) = 2337532415679887 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_347
      · exact prime_oneHundredFiftyFiveEW_6089
      · exact prime_oneHundredFiftyFiveEW_7307
      · exact prime_oneHundredFiftyFiveEW_75703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2337532415679887) ^ 1168766207839943 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 2337532415679887) ^ 6736404656138 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 2337532415679887) ^ 383894303774 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 2337532415679887) ^ 319903163498 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 2337532415679887) ^ 30877672162 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_2380941909280307 : Nat.Prime 2380941909280307 := by
  apply lucas_primality 2380941909280307 (2 : ZMod 2380941909280307)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (117193, 1), (10158208721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (117193, 1), (10158208721, 1)] : List FactorBlock).map factorBlockValue).prod) = 2380941909280307 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_117193
      · exact prime_oneHundredFiftyFiveEW_10158208721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2380941909280307) ^ 1190470954640153 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2380941909280307) ^ 20316417442 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2380941909280307) ^ 234386 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_3767362811129249 : Nat.Prime 3767362811129249 := by
  apply lucas_primality 3767362811129249 (3 : ZMod 3767362811129249)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (23, 2), (457, 1), (486985013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (23, 2), (457, 1), (486985013, 1)] : List FactorBlock).map factorBlockValue).prod) = 3767362811129249 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_23
      · exact prime_oneHundredFiftyFiveEW_457
      · exact prime_oneHundredFiftyFiveEW_486985013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3767362811129249) ^ 1883681405564624 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 3767362811129249) ^ 163798383092576 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 3767362811129249) ^ 8243682300064 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 3767362811129249) ^ 7736096 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_4864848303665491 : Nat.Prime 4864848303665491 := by
  apply lucas_primality 4864848303665491 (7 : ZMod 4864848303665491)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (23, 1), (40829, 1), (24669107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (23, 1), (40829, 1), (24669107, 1)] : List FactorBlock).map factorBlockValue).prod) = 4864848303665491 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_5
      · exact prime_oneHundredFiftyFiveEW_7
      · exact prime_oneHundredFiftyFiveEW_23
      · exact prime_oneHundredFiftyFiveEW_40829
      · exact prime_oneHundredFiftyFiveEW_24669107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 4864848303665491) ^ 2432424151832745 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (7 : ZMod 4864848303665491) ^ 1621616101221830 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (7 : ZMod 4864848303665491) ^ 972969660733098 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (7 : ZMod 4864848303665491) ^ 694978329095070 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (7 : ZMod 4864848303665491) ^ 211515143637630 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (7 : ZMod 4864848303665491) ^ 119151786810 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (7 : ZMod 4864848303665491) ^ 197204070 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_5538694287583363 : Nat.Prime 5538694287583363 := by
  apply lucas_primality 5538694287583363 (3 : ZMod 5538694287583363)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7639, 1), (74609, 1), (1619677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7639, 1), (74609, 1), (1619677, 1)] : List FactorBlock).map factorBlockValue).prod) = 5538694287583363 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_7639
      · exact prime_oneHundredFiftyFiveEW_74609
      · exact prime_oneHundredFiftyFiveEW_1619677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 5538694287583363) ^ 2769347143791681 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 5538694287583363) ^ 1846231429194454 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 5538694287583363) ^ 725054887758 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 5538694287583363) ^ 74236275618 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 5538694287583363) ^ 3419628906 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_5846751333379997 : Nat.Prime 5846751333379997 := by
  apply lucas_primality 5846751333379997 (2 : ZMod 5846751333379997)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (421, 1), (267072507463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (421, 1), (267072507463, 1)] : List FactorBlock).map factorBlockValue).prod) = 5846751333379997 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_13
      · exact prime_oneHundredFiftyFiveEW_421
      · exact prime_oneHundredFiftyFiveEW_267072507463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5846751333379997) ^ 2923375666689998 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 5846751333379997) ^ 449750102567692 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 5846751333379997) ^ 13887770388076 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 5846751333379997) ^ 21892 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_8047653949077857 : Nat.Prime 8047653949077857 := by
  apply lucas_primality 8047653949077857 (5 : ZMod 8047653949077857)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (37, 1), (113, 1), (1951, 1), (30830593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (37, 1), (113, 1), (1951, 1), (30830593, 1)] : List FactorBlock).map factorBlockValue).prod) = 8047653949077857 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_37
      · exact prime_oneHundredFiftyFiveEW_113
      · exact prime_oneHundredFiftyFiveEW_1951
      · exact prime_oneHundredFiftyFiveEW_30830593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 8047653949077857) ^ 4023826974538928 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 8047653949077857) ^ 217504160785888 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 8047653949077857) ^ 71218176540512 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 8047653949077857) ^ 4124886698656 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 8047653949077857) ^ 261028192 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_9225518218219243 : Nat.Prime 9225518218219243 := by
  apply lucas_primality 9225518218219243 (2 : ZMod 9225518218219243)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (41, 1), (59, 1), (757, 1), (31098827, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (41, 1), (59, 1), (757, 1), (31098827, 1)] : List FactorBlock).map factorBlockValue).prod) = 9225518218219243 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_41
      · exact prime_oneHundredFiftyFiveEW_59
      · exact prime_oneHundredFiftyFiveEW_757
      · exact prime_oneHundredFiftyFiveEW_31098827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9225518218219243) ^ 4612759109109621 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 9225518218219243) ^ 3075172739406414 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 9225518218219243) ^ 225012639468762 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 9225518218219243) ^ 156364715563038 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 9225518218219243) ^ 12186946127106 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 9225518218219243) ^ 296651646 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_11513662460653469 : Nat.Prime 11513662460653469 := by
  apply lucas_primality 11513662460653469 (2 : ZMod 11513662460653469)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (103, 1), (229267, 1), (121891867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (103, 1), (229267, 1), (121891867, 1)] : List FactorBlock).map factorBlockValue).prod) = 11513662460653469 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_103
      · exact prime_oneHundredFiftyFiveEW_229267
      · exact prime_oneHundredFiftyFiveEW_121891867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 11513662460653469) ^ 5756831230326734 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 11513662460653469) ^ 111783130685956 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 11513662460653469) ^ 50219449204 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 11513662460653469) ^ 94458004 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_12764374888855567 : Nat.Prime 12764374888855567 := by
  apply lucas_primality 12764374888855567 (3 : ZMod 12764374888855567)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1321, 1), (1610443463141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1321, 1), (1610443463141, 1)] : List FactorBlock).map factorBlockValue).prod) = 12764374888855567 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_1321
      · exact prime_oneHundredFiftyFiveEW_1610443463141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 12764374888855567) ^ 6382187444427783 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 12764374888855567) ^ 4254791629618522 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 12764374888855567) ^ 9662660778846 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 12764374888855567) ^ 7926 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_16700168648734409 : Nat.Prime 16700168648734409 := by
  apply lucas_primality 16700168648734409 (3 : ZMod 16700168648734409)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (19, 1), (6961, 1), (58579, 1), (269441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (19, 1), (6961, 1), (58579, 1), (269441, 1)] : List FactorBlock).map factorBlockValue).prod) = 16700168648734409 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_19
      · exact prime_oneHundredFiftyFiveEW_6961
      · exact prime_oneHundredFiftyFiveEW_58579
      · exact prime_oneHundredFiftyFiveEW_269441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 16700168648734409) ^ 8350084324367204 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 16700168648734409) ^ 878956244670232 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 16700168648734409) ^ 2399104819528 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 16700168648734409) ^ 285087977752 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 16700168648734409) ^ 61980799688 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_23633155335071453 : Nat.Prime 23633155335071453 := by
  apply lucas_primality 23633155335071453 (2 : ZMod 23633155335071453)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (113, 1), (9643, 1), (5422144757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (113, 1), (9643, 1), (5422144757, 1)] : List FactorBlock).map factorBlockValue).prod) = 23633155335071453 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_113
      · exact prime_oneHundredFiftyFiveEW_9643
      · exact prime_oneHundredFiftyFiveEW_5422144757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 23633155335071453) ^ 11816577667535726 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 23633155335071453) ^ 209142967567004 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 23633155335071453) ^ 2450809430164 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 23633155335071453) ^ 4358636 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_29322038063668213 : Nat.Prime 29322038063668213 := by
  apply lucas_primality 29322038063668213 (6 : ZMod 29322038063668213)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (37, 1), (20663, 1), (1065360407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (37, 1), (20663, 1), (1065360407, 1)] : List FactorBlock).map factorBlockValue).prod) = 29322038063668213 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_37
      · exact prime_oneHundredFiftyFiveEW_20663
      · exact prime_oneHundredFiftyFiveEW_1065360407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 29322038063668213) ^ 14661019031834106 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (6 : ZMod 29322038063668213) ^ 9774012687889404 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (6 : ZMod 29322038063668213) ^ 792487515234276 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (6 : ZMod 29322038063668213) ^ 1419060062124 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (6 : ZMod 29322038063668213) ^ 27523116 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_35558509254562747 : Nat.Prime 35558509254562747 := by
  apply lucas_primality 35558509254562747 (2 : ZMod 35558509254562747)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (37, 1), (71, 1), (11681, 1), (64377031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (37, 1), (71, 1), (11681, 1), (64377031, 1)] : List FactorBlock).map factorBlockValue).prod) = 35558509254562747 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_37
      · exact prime_oneHundredFiftyFiveEW_71
      · exact prime_oneHundredFiftyFiveEW_11681
      · exact prime_oneHundredFiftyFiveEW_64377031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 35558509254562747) ^ 17779254627281373 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 35558509254562747) ^ 11852836418187582 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 35558509254562747) ^ 961040790663858 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 35558509254562747) ^ 500824074007926 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 35558509254562747) ^ 3044132287866 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 35558509254562747) ^ 552347766 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_39569112162195019 : Nat.Prime 39569112162195019 := by
  apply lucas_primality 39569112162195019 (10 : ZMod 39569112162195019)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (507296309771731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (507296309771731, 1)] : List FactorBlock).map factorBlockValue).prod) = 39569112162195019 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_13
      · exact prime_oneHundredFiftyFiveEW_507296309771731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 39569112162195019) ^ 19784556081097509 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (10 : ZMod 39569112162195019) ^ 13189704054065006 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (10 : ZMod 39569112162195019) ^ 3043777858630386 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (10 : ZMod 39569112162195019) ^ 78 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_45165990193828187 : Nat.Prime 45165990193828187 := by
  apply lucas_primality 45165990193828187 (2 : ZMod 45165990193828187)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (4091, 1), (5520165020023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (4091, 1), (5520165020023, 1)] : List FactorBlock).map factorBlockValue).prod) = 45165990193828187 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_4091
      · exact prime_oneHundredFiftyFiveEW_5520165020023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 45165990193828187) ^ 22582995096914093 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 45165990193828187) ^ 11040330040046 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 45165990193828187) ^ 8182 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_119321908939495919 : Nat.Prime 119321908939495919 := by
  apply lucas_primality 119321908939495919 (13 : ZMod 119321908939495919)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (22896613, 1), (70423439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (22896613, 1), (70423439, 1)] : List FactorBlock).map factorBlockValue).prod) = 119321908939495919 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_37
      · exact prime_oneHundredFiftyFiveEW_22896613
      · exact prime_oneHundredFiftyFiveEW_70423439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 119321908939495919) ^ 59660954469747959 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (13 : ZMod 119321908939495919) ^ 3224916457824214 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (13 : ZMod 119321908939495919) ^ 5211334486 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (13 : ZMod 119321908939495919) ^ 1694349362 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_126079869173764313 : Nat.Prime 126079869173764313 := by
  apply lucas_primality 126079869173764313 (3 : ZMod 126079869173764313)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (67, 1), (1361, 1), (274069, 1), (630613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (67, 1), (1361, 1), (274069, 1), (630613, 1)] : List FactorBlock).map factorBlockValue).prod) = 126079869173764313 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_67
      · exact prime_oneHundredFiftyFiveEW_1361
      · exact prime_oneHundredFiftyFiveEW_274069
      · exact prime_oneHundredFiftyFiveEW_630613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 126079869173764313) ^ 63039934586882156 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 126079869173764313) ^ 1881789092145736 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 126079869173764313) ^ 92637670223192 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 126079869173764313) ^ 460029661048 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 126079869173764313) ^ 199932239224 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_158229238067428459 : Nat.Prime 158229238067428459 := by
  apply lucas_primality 158229238067428459 (2 : ZMod 158229238067428459)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (3767362811129249, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (3767362811129249, 1)] : List FactorBlock).map factorBlockValue).prod) = 158229238067428459 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_7
      · exact prime_oneHundredFiftyFiveEW_3767362811129249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 158229238067428459) ^ 79114619033714229 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 158229238067428459) ^ 52743079355809486 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 158229238067428459) ^ 22604176866775494 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 158229238067428459) ^ 42 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_181789245833427689 : Nat.Prime 181789245833427689 := by
  apply lucas_primality 181789245833427689 (3 : ZMod 181789245833427689)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (19419913, 1), (1170121397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (19419913, 1), (1170121397, 1)] : List FactorBlock).map factorBlockValue).prod) = 181789245833427689 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_19419913
      · exact prime_oneHundredFiftyFiveEW_1170121397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 181789245833427689) ^ 90894622916713844 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 181789245833427689) ^ 9360971176 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 181789245833427689) ^ 155359304 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_238643817878991839 : Nat.Prime 238643817878991839 := by
  apply lucas_primality 238643817878991839 (13 : ZMod 238643817878991839)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (119321908939495919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (119321908939495919, 1)] : List FactorBlock).map factorBlockValue).prod) = 238643817878991839 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_119321908939495919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (13 : ZMod 238643817878991839) ^ 119321908939495919 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (13 : ZMod 238643817878991839) ^ 2 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_374104373566082329 : Nat.Prime 374104373566082329 := by
  apply lucas_primality 374104373566082329 (19 : ZMod 374104373566082329)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (13, 1), (3583, 1), (126713, 1), (880337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (13, 1), (3583, 1), (126713, 1), (880337, 1)] : List FactorBlock).map factorBlockValue).prod) = 374104373566082329 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_13
      · exact prime_oneHundredFiftyFiveEW_3583
      · exact prime_oneHundredFiftyFiveEW_126713
      · exact prime_oneHundredFiftyFiveEW_880337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 374104373566082329) ^ 187052186783041164 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (19 : ZMod 374104373566082329) ^ 124701457855360776 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (19 : ZMod 374104373566082329) ^ 28777259505083256 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (19 : ZMod 374104373566082329) ^ 104410933175016 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (19 : ZMod 374104373566082329) ^ 2952375632856 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (19 : ZMod 374104373566082329) ^ 424955867544 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_556042234571677409 : Nat.Prime 556042234571677409 := by
  apply lucas_primality 556042234571677409 (3 : ZMod 556042234571677409)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (107, 1), (1013, 1), (160311463409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (107, 1), (1013, 1), (160311463409, 1)] : List FactorBlock).map factorBlockValue).prod) = 556042234571677409 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_107
      · exact prime_oneHundredFiftyFiveEW_1013
      · exact prime_oneHundredFiftyFiveEW_160311463409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 556042234571677409) ^ 278021117285838704 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 556042234571677409) ^ 5196656397866144 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 556042234571677409) ^ 548906450712416 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 556042234571677409) ^ 3468512 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_645084837400700687 : Nat.Prime 645084837400700687 := by
  apply lucas_primality 645084837400700687 (5 : ZMod 645084837400700687)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (29322038063668213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (29322038063668213, 1)] : List FactorBlock).map factorBlockValue).prod) = 645084837400700687 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_11
      · exact prime_oneHundredFiftyFiveEW_29322038063668213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 645084837400700687) ^ 322542418700350343 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 645084837400700687) ^ 58644076127336426 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 645084837400700687) ^ 22 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_718627833483094957 : Nat.Prime 718627833483094957 := by
  apply lucas_primality 718627833483094957 (2 : ZMod 718627833483094957)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (10429, 1), (5742223874797, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (10429, 1), (5742223874797, 1)] : List FactorBlock).map factorBlockValue).prod) = 718627833483094957 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_10429
      · exact prime_oneHundredFiftyFiveEW_5742223874797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 718627833483094957) ^ 359313916741547478 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 718627833483094957) ^ 239542611161031652 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 718627833483094957) ^ 68906686497564 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 718627833483094957) ^ 125148 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_727408625826681937 : Nat.Prime 727408625826681937 := by
  apply lucas_primality 727408625826681937 (5 : ZMod 727408625826681937)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (23, 1), (43, 1), (421, 1), (12132144301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (23, 1), (43, 1), (421, 1), (12132144301, 1)] : List FactorBlock).map factorBlockValue).prod) = 727408625826681937 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_23
      · exact prime_oneHundredFiftyFiveEW_43
      · exact prime_oneHundredFiftyFiveEW_421
      · exact prime_oneHundredFiftyFiveEW_12132144301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 727408625826681937) ^ 363704312913340968 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 727408625826681937) ^ 242469541942227312 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 727408625826681937) ^ 31626461992464432 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 727408625826681937) ^ 16916479670387952 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 727408625826681937) ^ 1727811462771216 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 727408625826681937) ^ 59957136 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_1391716646373735443 : Nat.Prime 1391716646373735443 := by
  apply lucas_primality 1391716646373735443 (2 : ZMod 1391716646373735443)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (283, 1), (1425877, 1), (1724456831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (283, 1), (1425877, 1), (1724456831, 1)] : List FactorBlock).map factorBlockValue).prod) = 1391716646373735443 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_283
      · exact prime_oneHundredFiftyFiveEW_1425877
      · exact prime_oneHundredFiftyFiveEW_1724456831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1391716646373735443) ^ 695858323186867721 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1391716646373735443) ^ 4917726665631574 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1391716646373735443) ^ 976042566346 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1391716646373735443) ^ 807046382 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_2031361023205031267 : Nat.Prime 2031361023205031267 := by
  apply lucas_primality 2031361023205031267 (2 : ZMod 2031361023205031267)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (5946163, 1), (24401822813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (5946163, 1), (24401822813, 1)] : List FactorBlock).map factorBlockValue).prod) = 2031361023205031267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_7
      · exact prime_oneHundredFiftyFiveEW_5946163
      · exact prime_oneHundredFiftyFiveEW_24401822813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2031361023205031267) ^ 1015680511602515633 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2031361023205031267) ^ 290194431886433038 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2031361023205031267) ^ 341625519382 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2031361023205031267) ^ 83246282 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_2234905640739533401 : Nat.Prime 2234905640739533401 := by
  apply lucas_primality 2234905640739533401 (7 : ZMod 2234905640739533401)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 2), (21269, 1), (175130129981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 2), (21269, 1), (175130129981, 1)] : List FactorBlock).map factorBlockValue).prod) = 2234905640739533401 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_5
      · exact prime_oneHundredFiftyFiveEW_21269
      · exact prime_oneHundredFiftyFiveEW_175130129981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 2234905640739533401) ^ 1117452820369766700 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (7 : ZMod 2234905640739533401) ^ 744968546913177800 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (7 : ZMod 2234905640739533401) ^ 446981128147906680 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (7 : ZMod 2234905640739533401) ^ 105078077988600 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (7 : ZMod 2234905640739533401) ^ 12761400 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_2901461851911455687 : Nat.Prime 2901461851911455687 := by
  apply lucas_primality 2901461851911455687 (5 : ZMod 2901461851911455687)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (167, 1), (439, 1), (3049, 1), (927150877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (167, 1), (439, 1), (3049, 1), (927150877, 1)] : List FactorBlock).map factorBlockValue).prod) = 2901461851911455687 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_7
      · exact prime_oneHundredFiftyFiveEW_167
      · exact prime_oneHundredFiftyFiveEW_439
      · exact prime_oneHundredFiftyFiveEW_3049
      · exact prime_oneHundredFiftyFiveEW_927150877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2901461851911455687) ^ 1450730925955727843 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 2901461851911455687) ^ 414494550273065098 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 2901461851911455687) ^ 17374023065338058 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 2901461851911455687) ^ 6609252510048874 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 2901461851911455687) ^ 951610971437014 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 2901461851911455687) ^ 3129438718 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_3470538621123665339 : Nat.Prime 3470538621123665339 := by
  apply lucas_primality 3470538621123665339 (2 : ZMod 3470538621123665339)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (41, 1), (634891, 1), (5127911323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (41, 1), (634891, 1), (5127911323, 1)] : List FactorBlock).map factorBlockValue).prod) = 3470538621123665339 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_13
      · exact prime_oneHundredFiftyFiveEW_41
      · exact prime_oneHundredFiftyFiveEW_634891
      · exact prime_oneHundredFiftyFiveEW_5127911323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3470538621123665339) ^ 1735269310561832669 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 3470538621123665339) ^ 266964509317205026 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 3470538621123665339) ^ 84647283442040618 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 3470538621123665339) ^ 5466353470318 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 3470538621123665339) ^ 676793806 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_4044403826121991187 : Nat.Prime 4044403826121991187 := by
  apply lucas_primality 4044403826121991187 (2 : ZMod 4044403826121991187)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (61, 1), (3691, 1), (528325673479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (61, 1), (3691, 1), (528325673479, 1)] : List FactorBlock).map factorBlockValue).prod) = 4044403826121991187 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_17
      · exact prime_oneHundredFiftyFiveEW_61
      · exact prime_oneHundredFiftyFiveEW_3691
      · exact prime_oneHundredFiftyFiveEW_528325673479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4044403826121991187) ^ 2022201913060995593 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 4044403826121991187) ^ 237906107418940658 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 4044403826121991187) ^ 66301702067573626 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 4044403826121991187) ^ 1095747446795446 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 4044403826121991187) ^ 7655134 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_4321298704489309187 : Nat.Prime 4321298704489309187 := by
  apply lucas_primality 4321298704489309187 (5 : ZMod 4321298704489309187)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (43, 1), (191, 1), (37582392935323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (43, 1), (191, 1), (37582392935323, 1)] : List FactorBlock).map factorBlockValue).prod) = 4321298704489309187 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_7
      · exact prime_oneHundredFiftyFiveEW_43
      · exact prime_oneHundredFiftyFiveEW_191
      · exact prime_oneHundredFiftyFiveEW_37582392935323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 4321298704489309187) ^ 2160649352244654593 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 4321298704489309187) ^ 617328386355615598 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 4321298704489309187) ^ 100495318709053702 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 4321298704489309187) ^ 22624600547064446 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 4321298704489309187) ^ 114982 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_4382602193503262191 : Nat.Prime 4382602193503262191 := by
  apply lucas_primality 4382602193503262191 (3 : ZMod 4382602193503262191)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 2), (11, 1), (253871, 1), (1067600917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 2), (11, 1), (253871, 1), (1067600917, 1)] : List FactorBlock).map factorBlockValue).prod) = 4382602193503262191 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_5
      · exact prime_oneHundredFiftyFiveEW_7
      · exact prime_oneHundredFiftyFiveEW_11
      · exact prime_oneHundredFiftyFiveEW_253871
      · exact prime_oneHundredFiftyFiveEW_1067600917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4382602193503262191) ^ 2191301096751631095 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 4382602193503262191) ^ 1460867397834420730 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 4382602193503262191) ^ 876520438700652438 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 4382602193503262191) ^ 626086027643323170 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 4382602193503262191) ^ 398418381227569290 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 4382602193503262191) ^ 17263106827890 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 4382602193503262191) ^ 4105094070 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_6594234568298915303 : Nat.Prime 6594234568298915303 := by
  apply lucas_primality 6594234568298915303 (5 : ZMod 6594234568298915303)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (73, 1), (45165990193828187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (73, 1), (45165990193828187, 1)] : List FactorBlock).map factorBlockValue).prod) = 6594234568298915303 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_73
      · exact prime_oneHundredFiftyFiveEW_45165990193828187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 6594234568298915303) ^ 3297117284149457651 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 6594234568298915303) ^ 90331980387656374 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 6594234568298915303) ^ 146 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_7596680508025691879 : Nat.Prime 7596680508025691879 := by
  apply lucas_primality 7596680508025691879 (11 : ZMod 7596680508025691879)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (64067, 1), (3487470611201, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (64067, 1), (3487470611201, 1)] : List FactorBlock).map factorBlockValue).prod) = 7596680508025691879 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_17
      · exact prime_oneHundredFiftyFiveEW_64067
      · exact prime_oneHundredFiftyFiveEW_3487470611201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 7596680508025691879) ^ 3798340254012845939 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (11 : ZMod 7596680508025691879) ^ 446863559295628934 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (11 : ZMod 7596680508025691879) ^ 118574000780834 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (11 : ZMod 7596680508025691879) ^ 2178278 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_16250888185640250137 : Nat.Prime 16250888185640250137 := by
  apply lucas_primality 16250888185640250137 (3 : ZMod 16250888185640250137)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (2031361023205031267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (2031361023205031267, 1)] : List FactorBlock).map factorBlockValue).prod) = 16250888185640250137 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_2031361023205031267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 16250888185640250137) ^ 8125444092820125068 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 16250888185640250137) ^ 8 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_16283179359033735613 : Nat.Prime 16283179359033735613 := by
  apply lucas_primality 16283179359033735613 (2 : ZMod 16283179359033735613)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (269, 1), (443, 1), (281527, 1), (40446589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (269, 1), (443, 1), (281527, 1), (40446589, 1)] : List FactorBlock).map factorBlockValue).prod) = 16283179359033735613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_269
      · exact prime_oneHundredFiftyFiveEW_443
      · exact prime_oneHundredFiftyFiveEW_281527
      · exact prime_oneHundredFiftyFiveEW_40446589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 16283179359033735613) ^ 8141589679516867806 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 16283179359033735613) ^ 5427726453011245204 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 16283179359033735613) ^ 60532265275218348 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 16283179359033735613) ^ 36756612548608884 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 16283179359033735613) ^ 57838784056356 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 16283179359033735613) ^ 402584736108 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_16776988296189872059 : Nat.Prime 16776988296189872059 := by
  apply lucas_primality 16776988296189872059 (2 : ZMod 16776988296189872059)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (11, 1), (28109, 1), (430631084717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (11, 1), (28109, 1), (430631084717, 1)] : List FactorBlock).map factorBlockValue).prod) = 16776988296189872059 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_7
      · exact prime_oneHundredFiftyFiveEW_11
      · exact prime_oneHundredFiftyFiveEW_28109
      · exact prime_oneHundredFiftyFiveEW_430631084717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 16776988296189872059) ^ 8388494148094936029 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 16776988296189872059) ^ 5592329432063290686 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 16776988296189872059) ^ 2396712613741410294 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 16776988296189872059) ^ 1525180754199079278 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 16776988296189872059) ^ 596854683417762 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 16776988296189872059) ^ 38959074 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_18642098699646161513 : Nat.Prime 18642098699646161513 := by
  apply lucas_primality 18642098699646161513 (3 : ZMod 18642098699646161513)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (479, 1), (4864848303665491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (479, 1), (4864848303665491, 1)] : List FactorBlock).map factorBlockValue).prod) = 18642098699646161513 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_479
      · exact prime_oneHundredFiftyFiveEW_4864848303665491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 18642098699646161513) ^ 9321049349823080756 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 18642098699646161513) ^ 38918786429323928 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 18642098699646161513) ^ 3832 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_21506763405413311873 : Nat.Prime 21506763405413311873 := by
  apply lucas_primality 21506763405413311873 (19 : ZMod 21506763405413311873)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (7, 1), (11, 1), (17, 1), (1193, 1), (35864414309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (7, 1), (11, 1), (17, 1), (1193, 1), (35864414309, 1)] : List FactorBlock).map factorBlockValue).prod) = 21506763405413311873 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_7
      · exact prime_oneHundredFiftyFiveEW_11
      · exact prime_oneHundredFiftyFiveEW_17
      · exact prime_oneHundredFiftyFiveEW_1193
      · exact prime_oneHundredFiftyFiveEW_35864414309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 21506763405413311873) ^ 10753381702706655936 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (19 : ZMod 21506763405413311873) ^ 7168921135137770624 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (19 : ZMod 21506763405413311873) ^ 3072394772201901696 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (19 : ZMod 21506763405413311873) ^ 1955160309583028352 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (19 : ZMod 21506763405413311873) ^ 1265103729730194816 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (19 : ZMod 21506763405413311873) ^ 18027463038904704 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (19 : ZMod 21506763405413311873) ^ 599668608 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_36126846442247975693 : Nat.Prime 36126846442247975693 := by
  apply lucas_primality 36126846442247975693 (2 : ZMod 36126846442247975693)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (263, 1), (349, 1), (98398592508329, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (263, 1), (349, 1), (98398592508329, 1)] : List FactorBlock).map factorBlockValue).prod) = 36126846442247975693 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_263
      · exact prime_oneHundredFiftyFiveEW_349
      · exact prime_oneHundredFiftyFiveEW_98398592508329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 36126846442247975693) ^ 18063423221123987846 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 36126846442247975693) ^ 137364435141627284 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 36126846442247975693) ^ 103515319318762108 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 36126846442247975693) ^ 367148 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_52983531609217552957 : Nat.Prime 52983531609217552957 := by
  apply lucas_primality 52983531609217552957 (5 : ZMod 52983531609217552957)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (2063, 1), (15269, 1), (140168308879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (2063, 1), (15269, 1), (140168308879, 1)] : List FactorBlock).map factorBlockValue).prod) = 52983531609217552957 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_2063
      · exact prime_oneHundredFiftyFiveEW_15269
      · exact prime_oneHundredFiftyFiveEW_140168308879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 52983531609217552957) ^ 26491765804608776478 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 52983531609217552957) ^ 17661177203072517652 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 52983531609217552957) ^ 25682758899281412 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 52983531609217552957) ^ 3470006654608524 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 52983531609217552957) ^ 377999364 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_125802652891956842959 : Nat.Prime 125802652891956842959 := by
  apply lucas_primality 125802652891956842959 (3 : ZMod 125802652891956842959)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (31, 1), (2731, 1), (301669, 1), (63151129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (31, 1), (2731, 1), (301669, 1), (63151129, 1)] : List FactorBlock).map factorBlockValue).prod) = 125802652891956842959 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_13
      · exact prime_oneHundredFiftyFiveEW_31
      · exact prime_oneHundredFiftyFiveEW_2731
      · exact prime_oneHundredFiftyFiveEW_301669
      · exact prime_oneHundredFiftyFiveEW_63151129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 125802652891956842959) ^ 62901326445978421479 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 125802652891956842959) ^ 41934217630652280986 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 125802652891956842959) ^ 9677127145535141766 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 125802652891956842959) ^ 4058150093288930418 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 125802652891956842959) ^ 46064684325139818 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 125802652891956842959) ^ 417022143116982 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 125802652891956842959) ^ 1992088738302 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_126433709300525004223 : Nat.Prime 126433709300525004223 := by
  apply lucas_primality 126433709300525004223 (3 : ZMod 126433709300525004223)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 2), (433, 1), (287963224557181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 2), (433, 1), (287963224557181, 1)] : List FactorBlock).map factorBlockValue).prod) = 126433709300525004223 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_13
      · exact prime_oneHundredFiftyFiveEW_433
      · exact prime_oneHundredFiftyFiveEW_287963224557181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 126433709300525004223) ^ 63216854650262502111 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 126433709300525004223) ^ 42144569766841668074 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 126433709300525004223) ^ 9725669946194231094 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 126433709300525004223) ^ 291994709700981534 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 126433709300525004223) ^ 439062 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_313357880006437214197 : Nat.Prime 313357880006437214197 := by
  apply lucas_primality 313357880006437214197 (2 : ZMod 313357880006437214197)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (2901461851911455687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (2901461851911455687, 1)] : List FactorBlock).map factorBlockValue).prod) = 313357880006437214197 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_2901461851911455687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 313357880006437214197) ^ 156678940003218607098 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 313357880006437214197) ^ 104452626668812404732 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 313357880006437214197) ^ 108 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_324424537986589273537 : Nat.Prime 324424537986589273537 := by
  apply lucas_primality 324424537986589273537 (5 : ZMod 324424537986589273537)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (17, 2), (5846751333379997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (17, 2), (5846751333379997, 1)] : List FactorBlock).map factorBlockValue).prod) = 324424537986589273537 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_17
      · exact prime_oneHundredFiftyFiveEW_5846751333379997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 324424537986589273537) ^ 162212268993294636768 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 324424537986589273537) ^ 108141512662196424512 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 324424537986589273537) ^ 19083796352152310208 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 324424537986589273537) ^ 55488 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_654168474773429417159 : Nat.Prime 654168474773429417159 := by
  apply lucas_primality 654168474773429417159 (7 : ZMod 654168474773429417159)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (109, 1), (113, 1), (227, 1), (443, 1), (37724809081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (109, 1), (113, 1), (227, 1), (443, 1), (37724809081, 1)] : List FactorBlock).map factorBlockValue).prod) = 654168474773429417159 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_7
      · exact prime_oneHundredFiftyFiveEW_109
      · exact prime_oneHundredFiftyFiveEW_113
      · exact prime_oneHundredFiftyFiveEW_227
      · exact prime_oneHundredFiftyFiveEW_443
      · exact prime_oneHundredFiftyFiveEW_37724809081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 654168474773429417159) ^ 327084237386714708579 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (7 : ZMod 654168474773429417159) ^ 93452639253347059594 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (7 : ZMod 654168474773429417159) ^ 6001545640123205662 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (7 : ZMod 654168474773429417159) ^ 5789101546667516966 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (7 : ZMod 654168474773429417159) ^ 2881799448341098754 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (7 : ZMod 654168474773429417159) ^ 1476678272626251506 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (7 : ZMod 654168474773429417159) ^ 17340537718 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_1081687868363620552253 : Nat.Prime 1081687868363620552253 := by
  apply lucas_primality 1081687868363620552253 (2 : ZMod 1081687868363620552253)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (71, 1), (199, 1), (52864081, 1), (362051087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (71, 1), (199, 1), (52864081, 1), (362051087, 1)] : List FactorBlock).map factorBlockValue).prod) = 1081687868363620552253 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_71
      · exact prime_oneHundredFiftyFiveEW_199
      · exact prime_oneHundredFiftyFiveEW_52864081
      · exact prime_oneHundredFiftyFiveEW_362051087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1081687868363620552253) ^ 540843934181810276126 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1081687868363620552253) ^ 15235040399487613412 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1081687868363620552253) ^ 5435617428962917348 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1081687868363620552253) ^ 20461679232892 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1081687868363620552253) ^ 2987666401796 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_1342356728613354717491 : Nat.Prime 1342356728613354717491 := by
  apply lucas_primality 1342356728613354717491 (2 : ZMod 1342356728613354717491)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1289, 1), (1069267, 1), (97393251023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1289, 1), (1069267, 1), (97393251023, 1)] : List FactorBlock).map factorBlockValue).prod) = 1342356728613354717491 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_5
      · exact prime_oneHundredFiftyFiveEW_1289
      · exact prime_oneHundredFiftyFiveEW_1069267
      · exact prime_oneHundredFiftyFiveEW_97393251023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1342356728613354717491) ^ 671178364306677358745 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1342356728613354717491) ^ 268471345722670943498 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1342356728613354717491) ^ 1041393893416101410 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1342356728613354717491) ^ 1255399005686470 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1342356728613354717491) ^ 13782851630 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_2841846270956172113957 : Nat.Prime 2841846270956172113957 := by
  apply lucas_primality 2841846270956172113957 (2 : ZMod 2841846270956172113957)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (23, 1), (113, 1), (353, 1), (26189, 1), (4224182269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (23, 1), (113, 1), (353, 1), (26189, 1), (4224182269, 1)] : List FactorBlock).map factorBlockValue).prod) = 2841846270956172113957 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_7
      · exact prime_oneHundredFiftyFiveEW_23
      · exact prime_oneHundredFiftyFiveEW_113
      · exact prime_oneHundredFiftyFiveEW_353
      · exact prime_oneHundredFiftyFiveEW_26189
      · exact prime_oneHundredFiftyFiveEW_4224182269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2841846270956172113957) ^ 1420923135478086056978 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2841846270956172113957) ^ 405978038708024587708 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2841846270956172113957) ^ 123558533519833570172 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2841846270956172113957) ^ 25149082043859930212 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2841846270956172113957) ^ 8050556008374425252 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2841846270956172113957) ^ 108512973804122804 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2841846270956172113957) ^ 672756545524 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_4120462932770454404731 : Nat.Prime 4120462932770454404731 := by
  apply lucas_primality 4120462932770454404731 (10 : ZMod 4120462932770454404731)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (67, 1), (11462203, 1), (178847081891, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (67, 1), (11462203, 1), (178847081891, 1)] : List FactorBlock).map factorBlockValue).prod) = 4120462932770454404731 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_5
      · exact prime_oneHundredFiftyFiveEW_67
      · exact prime_oneHundredFiftyFiveEW_11462203
      · exact prime_oneHundredFiftyFiveEW_178847081891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 4120462932770454404731) ^ 2060231466385227202365 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (10 : ZMod 4120462932770454404731) ^ 1373487644256818134910 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (10 : ZMod 4120462932770454404731) ^ 824092586554090880946 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (10 : ZMod 4120462932770454404731) ^ 61499446757767976190 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (10 : ZMod 4120462932770454404731) ^ 359482634600910 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (10 : ZMod 4120462932770454404731) ^ 23039028030 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_4296526812951097689683 : Nat.Prime 4296526812951097689683 := by
  apply lucas_primality 4296526812951097689683 (2 : ZMod 4296526812951097689683)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (619, 1), (3470538621123665339, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (619, 1), (3470538621123665339, 1)] : List FactorBlock).map factorBlockValue).prod) = 4296526812951097689683 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_619
      · exact prime_oneHundredFiftyFiveEW_3470538621123665339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4296526812951097689683) ^ 2148263406475548844841 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 4296526812951097689683) ^ 6941077242247330678 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 4296526812951097689683) ^ 1238 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_4316628346582495505717 : Nat.Prime 4316628346582495505717 := by
  apply lucas_primality 4316628346582495505717 (2 : ZMod 4316628346582495505717)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (11, 1), (41, 1), (1553, 1), (220109419994249, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (11, 1), (41, 1), (1553, 1), (220109419994249, 1)] : List FactorBlock).map factorBlockValue).prod) = 4316628346582495505717 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_7
      · exact prime_oneHundredFiftyFiveEW_11
      · exact prime_oneHundredFiftyFiveEW_41
      · exact prime_oneHundredFiftyFiveEW_1553
      · exact prime_oneHundredFiftyFiveEW_220109419994249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4316628346582495505717) ^ 2158314173291247752858 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 4316628346582495505717) ^ 616661192368927929388 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 4316628346582495505717) ^ 392420758780226864156 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 4316628346582495505717) ^ 105283618209329158676 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 4316628346582495505717) ^ 2779541755687376372 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 4316628346582495505717) ^ 19611284 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_5233347798187435337273 : Nat.Prime 5233347798187435337273 := by
  apply lucas_primality 5233347798187435337273 (3 : ZMod 5233347798187435337273)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (654168474773429417159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (654168474773429417159, 1)] : List FactorBlock).map factorBlockValue).prod) = 5233347798187435337273 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_654168474773429417159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 5233347798187435337273) ^ 2616673899093717668636 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 5233347798187435337273) ^ 8 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_5265222190745853492881 : Nat.Prime 5265222190745853492881 := by
  apply lucas_primality 5265222190745853492881 (3 : ZMod 5265222190745853492881)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (1237, 1), (9413, 1), (5652348850381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (1237, 1), (9413, 1), (5652348850381, 1)] : List FactorBlock).map factorBlockValue).prod) = 5265222190745853492881 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_5
      · exact prime_oneHundredFiftyFiveEW_1237
      · exact prime_oneHundredFiftyFiveEW_9413
      · exact prime_oneHundredFiftyFiveEW_5652348850381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 5265222190745853492881) ^ 2632611095372926746440 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 5265222190745853492881) ^ 1053044438149170698576 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 5265222190745853492881) ^ 4256444778290908240 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 5265222190745853492881) ^ 559356442233703760 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 5265222190745853492881) ^ 931510480 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_10516383400888515934699 : Nat.Prime 10516383400888515934699 := by
  apply lucas_primality 10516383400888515934699 (10 : ZMod 10516383400888515934699)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (455881, 1), (1028213, 1), (3739216211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (455881, 1), (1028213, 1), (3739216211, 1)] : List FactorBlock).map factorBlockValue).prod) = 10516383400888515934699 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_455881
      · exact prime_oneHundredFiftyFiveEW_1028213
      · exact prime_oneHundredFiftyFiveEW_3739216211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 10516383400888515934699) ^ 5258191700444257967349 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (10 : ZMod 10516383400888515934699) ^ 3505461133629505311566 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (10 : ZMod 10516383400888515934699) ^ 23068264307765658 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (10 : ZMod 10516383400888515934699) ^ 10227825752921346 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (10 : ZMod 10516383400888515934699) ^ 2812456623918 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_12861244179825976646419 : Nat.Prime 12861244179825976646419 := by
  apply lucas_primality 12861244179825976646419 (3 : ZMod 12861244179825976646419)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (179, 1), (1811443, 1), (944400024157, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (179, 1), (1811443, 1), (944400024157, 1)] : List FactorBlock).map factorBlockValue).prod) = 12861244179825976646419 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_7
      · exact prime_oneHundredFiftyFiveEW_179
      · exact prime_oneHundredFiftyFiveEW_1811443
      · exact prime_oneHundredFiftyFiveEW_944400024157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 12861244179825976646419) ^ 6430622089912988323209 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 12861244179825976646419) ^ 4287081393275325548806 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 12861244179825976646419) ^ 1837320597117996663774 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 12861244179825976646419) ^ 71850526144279199142 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 12861244179825976646419) ^ 7099999381612326 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 12861244179825976646419) ^ 13618428474 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_12904058043247987123801 : Nat.Prime 12904058043247987123801 := by
  apply lucas_primality 12904058043247987123801 (11 : ZMod 12904058043247987123801)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 2), (21506763405413311873, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 2), (21506763405413311873, 1)] : List FactorBlock).map factorBlockValue).prod) = 12904058043247987123801 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_5
      · exact prime_oneHundredFiftyFiveEW_21506763405413311873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 12904058043247987123801) ^ 6452029021623993561900 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (11 : ZMod 12904058043247987123801) ^ 4301352681082662374600 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (11 : ZMod 12904058043247987123801) ^ 2580811608649597424760 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (11 : ZMod 12904058043247987123801) ^ 600 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_22951075064915360481269 : Nat.Prime 22951075064915360481269 := by
  apply lucas_primality 22951075064915360481269 (2 : ZMod 22951075064915360481269)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (2677, 1), (126079869173764313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (2677, 1), (126079869173764313, 1)] : List FactorBlock).map factorBlockValue).prod) = 22951075064915360481269 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_17
      · exact prime_oneHundredFiftyFiveEW_2677
      · exact prime_oneHundredFiftyFiveEW_126079869173764313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 22951075064915360481269) ^ 11475537532457680240634 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 22951075064915360481269) ^ 1350063239112668263604 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 22951075064915360481269) ^ 8573431103815973284 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 22951075064915360481269) ^ 182036 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_52456181034144060706237 : Nat.Prime 52456181034144060706237 := by
  apply lucas_primality 52456181034144060706237 (5 : ZMod 52456181034144060706237)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 2), (36126846442247975693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 2), (36126846442247975693, 1)] : List FactorBlock).map factorBlockValue).prod) = 52456181034144060706237 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_11
      · exact prime_oneHundredFiftyFiveEW_36126846442247975693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 52456181034144060706237) ^ 26228090517072030353118 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 52456181034144060706237) ^ 17485393678048020235412 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 52456181034144060706237) ^ 4768743730376732791476 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 52456181034144060706237) ^ 1452 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_77528386827565240238587 : Nat.Prime 77528386827565240238587 := by
  apply lucas_primality 77528386827565240238587 (2 : ZMod 77528386827565240238587)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (19, 1), (29, 1), (43, 1), (181789245833427689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (19, 1), (29, 1), (43, 1), (181789245833427689, 1)] : List FactorBlock).map factorBlockValue).prod) = 77528386827565240238587 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_19
      · exact prime_oneHundredFiftyFiveEW_29
      · exact prime_oneHundredFiftyFiveEW_43
      · exact prime_oneHundredFiftyFiveEW_181789245833427689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 77528386827565240238587) ^ 38764193413782620119293 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 77528386827565240238587) ^ 25842795609188413412862 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 77528386827565240238587) ^ 4080441411977117907294 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 77528386827565240238587) ^ 2673392649226387594434 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 77528386827565240238587) ^ 1802985740175935819502 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 77528386827565240238587) ^ 426474 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_141211992130668839939047 : Nat.Prime 141211992130668839939047 := by
  apply lucas_primality 141211992130668839939047 (3 : ZMod 141211992130668839939047)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (55339, 1), (28937567, 1), (14696942957, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (55339, 1), (28937567, 1), (14696942957, 1)] : List FactorBlock).map factorBlockValue).prod) = 141211992130668839939047 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_55339
      · exact prime_oneHundredFiftyFiveEW_28937567
      · exact prime_oneHundredFiftyFiveEW_14696942957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 141211992130668839939047) ^ 70605996065334419969523 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 141211992130668839939047) ^ 47070664043556279979682 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 141211992130668839939047) ^ 2551762629080193714 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 141211992130668839939047) ^ 4879884757784538 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 141211992130668839939047) ^ 9608256121278 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_189541294907440902617627 : Nat.Prime 189541294907440902617627 := by
  apply lucas_primality 189541294907440902617627 (2 : ZMod 189541294907440902617627)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (4120462932770454404731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (4120462932770454404731, 1)] : List FactorBlock).map factorBlockValue).prod) = 189541294907440902617627 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_23
      · exact prime_oneHundredFiftyFiveEW_4120462932770454404731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 189541294907440902617627) ^ 94770647453720451308813 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 189541294907440902617627) ^ 8240925865540908809462 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 189541294907440902617627) ^ 46 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_310113547310260960954349 : Nat.Prime 310113547310260960954349 := by
  apply lucas_primality 310113547310260960954349 (2 : ZMod 310113547310260960954349)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (77528386827565240238587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (77528386827565240238587, 1)] : List FactorBlock).map factorBlockValue).prod) = 310113547310260960954349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_77528386827565240238587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 310113547310260960954349) ^ 155056773655130480477174 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 310113547310260960954349) ^ 4 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_668766439072227974717573 : Nat.Prime 668766439072227974717573 := by
  apply lucas_primality 668766439072227974717573 (2 : ZMod 668766439072227974717573)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (67, 1), (617, 1), (4044403826121991187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (67, 1), (617, 1), (4044403826121991187, 1)] : List FactorBlock).map factorBlockValue).prod) = 668766439072227974717573 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_67
      · exact prime_oneHundredFiftyFiveEW_617
      · exact prime_oneHundredFiftyFiveEW_4044403826121991187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 668766439072227974717573) ^ 334383219536113987358786 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 668766439072227974717573) ^ 9981588642869074249516 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 668766439072227974717573) ^ 1083900225400693638116 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 668766439072227974717573) ^ 165356 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_1314930662848821603193561 : Nat.Prime 1314930662848821603193561 := by
  apply lucas_primality 1314930662848821603193561 (11 : ZMod 1314930662848821603193561)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (7, 1), (13187, 1), (39569112162195019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (7, 1), (13187, 1), (39569112162195019, 1)] : List FactorBlock).map factorBlockValue).prod) = 1314930662848821603193561 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_5
      · exact prime_oneHundredFiftyFiveEW_7
      · exact prime_oneHundredFiftyFiveEW_13187
      · exact prime_oneHundredFiftyFiveEW_39569112162195019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 1314930662848821603193561) ^ 657465331424410801596780 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (11 : ZMod 1314930662848821603193561) ^ 438310220949607201064520 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (11 : ZMod 1314930662848821603193561) ^ 262986132569764320638712 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (11 : ZMod 1314930662848821603193561) ^ 187847237549831657599080 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (11 : ZMod 1314930662848821603193561) ^ 99714162648731447880 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (11 : ZMod 1314930662848821603193561) ^ 33231240 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_4063944092875398657506011 : Nat.Prime 4063944092875398657506011 := by
  apply lucas_primality 4063944092875398657506011 (7 : ZMod 4063944092875398657506011)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (17, 2), (1790719019, 1), (261758733737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (17, 2), (1790719019, 1), (261758733737, 1)] : List FactorBlock).map factorBlockValue).prod) = 4063944092875398657506011 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_5
      · exact prime_oneHundredFiftyFiveEW_17
      · exact prime_oneHundredFiftyFiveEW_1790719019
      · exact prime_oneHundredFiftyFiveEW_261758733737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 4063944092875398657506011) ^ 2031972046437699328753005 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (7 : ZMod 4063944092875398657506011) ^ 1354648030958466219168670 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (7 : ZMod 4063944092875398657506011) ^ 812788818575079731501202 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (7 : ZMod 4063944092875398657506011) ^ 239055534875023450441530 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (7 : ZMod 4063944092875398657506011) ^ 2269448221499790 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (7 : ZMod 4063944092875398657506011) ^ 15525533894730 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_5010701275181490655809391 : Nat.Prime 5010701275181490655809391 := by
  apply lucas_primality 5010701275181490655809391 (13 : ZMod 5010701275181490655809391)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (17, 1), (23, 1), (29, 1), (3089, 1), (8147, 1), (10867, 1), (53861347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (17, 1), (23, 1), (29, 1), (3089, 1), (8147, 1), (10867, 1), (53861347, 1)] : List FactorBlock).map factorBlockValue).prod) = 5010701275181490655809391 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_5
      · exact prime_oneHundredFiftyFiveEW_17
      · exact prime_oneHundredFiftyFiveEW_23
      · exact prime_oneHundredFiftyFiveEW_29
      · exact prime_oneHundredFiftyFiveEW_3089
      · exact prime_oneHundredFiftyFiveEW_8147
      · exact prime_oneHundredFiftyFiveEW_10867
      · exact prime_oneHundredFiftyFiveEW_53861347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 5010701275181490655809391) ^ 2505350637590745327904695 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (13 : ZMod 5010701275181490655809391) ^ 1670233758393830218603130 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (13 : ZMod 5010701275181490655809391) ^ 1002140255036298131161878 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (13 : ZMod 5010701275181490655809391) ^ 294747133834205332694670 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (13 : ZMod 5010701275181490655809391) ^ 217856577181803941556930 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (13 : ZMod 5010701275181490655809391) ^ 172782802592465195027910 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (13 : ZMod 5010701275181490655809391) ^ 1622111128255581306510 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (13 : ZMod 5010701275181490655809391) ^ 615036366169324985370 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (13 : ZMod 5010701275181490655809391) ^ 461093335343838286170 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (13 : ZMod 5010701275181490655809391) ^ 93029631716813370 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_5725889483687585185110019 : Nat.Prime 5725889483687585185110019 := by
  apply lucas_primality 5725889483687585185110019 (2 : ZMod 5725889483687585185110019)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (43, 1), (2094109, 1), (1514000198503267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (43, 1), (2094109, 1), (1514000198503267, 1)] : List FactorBlock).map factorBlockValue).prod) = 5725889483687585185110019 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_7
      · exact prime_oneHundredFiftyFiveEW_43
      · exact prime_oneHundredFiftyFiveEW_2094109
      · exact prime_oneHundredFiftyFiveEW_1514000198503267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5725889483687585185110019) ^ 2862944741843792592555009 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 5725889483687585185110019) ^ 1908629827895861728370006 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 5725889483687585185110019) ^ 817984211955369312158574 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 5725889483687585185110019) ^ 133160220550874074072326 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 5725889483687585185110019) ^ 2734284358496900202 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 5725889483687585185110019) ^ 3781960854 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_7942931257246650611775001 : Nat.Prime 7942931257246650611775001 := by
  apply lucas_primality 7942931257246650611775001 (21 : ZMod 7942931257246650611775001)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 5), (29, 1), (269, 1), (294167, 1), (15383461057, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 5), (29, 1), (269, 1), (294167, 1), (15383461057, 1)] : List FactorBlock).map factorBlockValue).prod) = 7942931257246650611775001 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_5
      · exact prime_oneHundredFiftyFiveEW_29
      · exact prime_oneHundredFiftyFiveEW_269
      · exact prime_oneHundredFiftyFiveEW_294167
      · exact prime_oneHundredFiftyFiveEW_15383461057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (21 : ZMod 7942931257246650611775001) ^ 3971465628623325305887500 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (21 : ZMod 7942931257246650611775001) ^ 2647643752415550203925000 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (21 : ZMod 7942931257246650611775001) ^ 1588586251449330122355000 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (21 : ZMod 7942931257246650611775001) ^ 273894181284367262475000 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (21 : ZMod 7942931257246650611775001) ^ 29527625491623236475000 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (21 : ZMod 7942931257246650611775001) ^ 27001435433772825000 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (21 : ZMod 7942931257246650611775001) ^ 516329272575000 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_16950454817864903918625571 : Nat.Prime 16950454817864903918625571 := by
  apply lucas_primality 16950454817864903918625571 (10 : ZMod 16950454817864903918625571)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 2), (73, 1), (34007411, 1), (1880954544613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 2), (73, 1), (34007411, 1), (1880954544613, 1)] : List FactorBlock).map factorBlockValue).prod) = 16950454817864903918625571 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_5
      · exact prime_oneHundredFiftyFiveEW_11
      · exact prime_oneHundredFiftyFiveEW_73
      · exact prime_oneHundredFiftyFiveEW_34007411
      · exact prime_oneHundredFiftyFiveEW_1880954544613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 16950454817864903918625571) ^ 8475227408932451959312785 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (10 : ZMod 16950454817864903918625571) ^ 5650151605954967972875190 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (10 : ZMod 16950454817864903918625571) ^ 3390090963572980783725114 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (10 : ZMod 16950454817864903918625571) ^ 1540950437987718538056870 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (10 : ZMod 16950454817864903918625571) ^ 232198011203628820803090 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (10 : ZMod 16950454817864903918625571) ^ 498434144776998870 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (10 : ZMod 16950454817864903918625571) ^ 9011623840890 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_238919644114651207645711927 : Nat.Prime 238919644114651207645711927 := by
  apply lucas_primality 238919644114651207645711927 (3 : ZMod 238919644114651207645711927)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (41, 1), (148609, 1), (7306363, 1), (894479506643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (41, 1), (148609, 1), (7306363, 1), (894479506643, 1)] : List FactorBlock).map factorBlockValue).prod) = 238919644114651207645711927 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_41
      · exact prime_oneHundredFiftyFiveEW_148609
      · exact prime_oneHundredFiftyFiveEW_7306363
      · exact prime_oneHundredFiftyFiveEW_894479506643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 238919644114651207645711927) ^ 119459822057325603822855963 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 238919644114651207645711927) ^ 79639881371550402548570642 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 238919644114651207645711927) ^ 5827308393040273357212486 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 238919644114651207645711927) ^ 1607706425012288674614 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 238919644114651207645711927) ^ 32700215430666558402 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 238919644114651207645711927) ^ 267104659570482 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_292733813156449642594666211 : Nat.Prime 292733813156449642594666211 := by
  apply lucas_primality 292733813156449642594666211 (2 : ZMod 292733813156449642594666211)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (17, 1), (605733413, 1), (406110667980943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (17, 1), (605733413, 1), (406110667980943, 1)] : List FactorBlock).map factorBlockValue).prod) = 292733813156449642594666211 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_5
      · exact prime_oneHundredFiftyFiveEW_7
      · exact prime_oneHundredFiftyFiveEW_17
      · exact prime_oneHundredFiftyFiveEW_605733413
      · exact prime_oneHundredFiftyFiveEW_406110667980943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 292733813156449642594666211) ^ 146366906578224821297333105 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 292733813156449642594666211) ^ 58546762631289928518933242 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 292733813156449642594666211) ^ 41819116165207091799238030 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 292733813156449642594666211) ^ 17219636068026449564392130 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 292733813156449642594666211) ^ 483271694897322170 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 292733813156449642594666211) ^ 720822761470 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_374747171852632875796034863 : Nat.Prime 374747171852632875796034863 := by
  apply lucas_primality 374747171852632875796034863 (3 : ZMod 374747171852632875796034863)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (138184461083, 1), (451989040489319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (138184461083, 1), (451989040489319, 1)] : List FactorBlock).map factorBlockValue).prod) = 374747171852632875796034863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_138184461083
      · exact prime_oneHundredFiftyFiveEW_451989040489319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 374747171852632875796034863) ^ 187373585926316437898017431 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 374747171852632875796034863) ^ 124915723950877625265344954 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 374747171852632875796034863) ^ 2711934242935914 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 374747171852632875796034863) ^ 829106766498 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_382570703624086589278206781 : Nat.Prime 382570703624086589278206781 := by
  apply lucas_primality 382570703624086589278206781 (6 : ZMod 382570703624086589278206781)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (29, 1), (37, 1), (47, 1), (126433709300525004223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (29, 1), (37, 1), (47, 1), (126433709300525004223, 1)] : List FactorBlock).map factorBlockValue).prod) = 382570703624086589278206781 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_5
      · exact prime_oneHundredFiftyFiveEW_29
      · exact prime_oneHundredFiftyFiveEW_37
      · exact prime_oneHundredFiftyFiveEW_47
      · exact prime_oneHundredFiftyFiveEW_126433709300525004223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 382570703624086589278206781) ^ 191285351812043294639103390 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (6 : ZMod 382570703624086589278206781) ^ 127523567874695529759402260 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (6 : ZMod 382570703624086589278206781) ^ 76514140724817317855641356 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (6 : ZMod 382570703624086589278206781) ^ 13192093228416778940627820 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (6 : ZMod 382570703624086589278206781) ^ 10339748746596934845356940 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (6 : ZMod 382570703624086589278206781) ^ 8139802204767799771876740 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (6 : ZMod 382570703624086589278206781) ^ 3025860 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_409958315516638649360762971 : Nat.Prime 409958315516638649360762971 := by
  apply lucas_primality 409958315516638649360762971 (2 : ZMod 409958315516638649360762971)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (416739303481, 1), (32790948849179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (416739303481, 1), (32790948849179, 1)] : List FactorBlock).map factorBlockValue).prod) = 409958315516638649360762971 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_5
      · exact prime_oneHundredFiftyFiveEW_416739303481
      · exact prime_oneHundredFiftyFiveEW_32790948849179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 409958315516638649360762971) ^ 204979157758319324680381485 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 409958315516638649360762971) ^ 136652771838879549786920990 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 409958315516638649360762971) ^ 81991663103327729872152594 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 409958315516638649360762971) ^ 983728465475370 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 409958315516638649360762971) ^ 12502179104430 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_410877504564882233776370063 : Nat.Prime 410877504564882233776370063 := by
  apply lucas_primality 410877504564882233776370063 (5 : ZMod 410877504564882233776370063)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (5010701275181490655809391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (5010701275181490655809391, 1)] : List FactorBlock).map factorBlockValue).prod) = 410877504564882233776370063 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_41
      · exact prime_oneHundredFiftyFiveEW_5010701275181490655809391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 410877504564882233776370063) ^ 205438752282441116888185031 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 410877504564882233776370063) ^ 10021402550362981311618782 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 410877504564882233776370063) ^ 82 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_2290642087949218453303263101 : Nat.Prime 2290642087949218453303263101 := by
  apply lucas_primality 2290642087949218453303263101 (2 : ZMod 2290642087949218453303263101)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (31, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (31, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 2290642087949218453303263101 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_5
      · exact prime_oneHundredFiftyFiveEW_31
      · exact prime_oneHundredFiftyFiveEW_171401
      · exact prime_oneHundredFiftyFiveEW_714027719
      · exact prime_oneHundredFiftyFiveEW_6037638679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2290642087949218453303263101) ^ 1145321043974609226651631550 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2290642087949218453303263101) ^ 458128417589843690660652620 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2290642087949218453303263101) ^ 73891680256426401719460100 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2290642087949218453303263101) ^ 13364228259748883923100 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2290642087949218453303263101) ^ 3208057652379764900 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2290642087949218453303263101) ^ 379393701699388900 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_2379887883583603587847546079 : Nat.Prime 2379887883583603587847546079 := by
  apply lucas_primality 2379887883583603587847546079 (7 : ZMod 2379887883583603587847546079)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (53, 1), (211, 1), (263, 1), (563, 1), (718627833483094957, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (53, 1), (211, 1), (263, 1), (563, 1), (718627833483094957, 1)] : List FactorBlock).map factorBlockValue).prod) = 2379887883583603587847546079 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_53
      · exact prime_oneHundredFiftyFiveEW_211
      · exact prime_oneHundredFiftyFiveEW_263
      · exact prime_oneHundredFiftyFiveEW_563
      · exact prime_oneHundredFiftyFiveEW_718627833483094957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 2379887883583603587847546079) ^ 1189943941791801793923773039 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (7 : ZMod 2379887883583603587847546079) ^ 44903544973275539393349926 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (7 : ZMod 2379887883583603587847546079) ^ 11279089495656889041931498 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (7 : ZMod 2379887883583603587847546079) ^ 9049003359633473718051506 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (7 : ZMod 2379887883583603587847546079) ^ 4227154322528603175572906 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (7 : ZMod 2379887883583603587847546079) ^ 3311711254 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_3457572962942216533287944303 : Nat.Prime 3457572962942216533287944303 := by
  apply lucas_primality 3457572962942216533287944303 (5 : ZMod 3457572962942216533287944303)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 1), (211, 1), (263, 1), (563, 1), (718627833483094957, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 1), (211, 1), (263, 1), (563, 1), (718627833483094957, 1)] : List FactorBlock).map factorBlockValue).prod) = 3457572962942216533287944303 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_7
      · exact prime_oneHundredFiftyFiveEW_11
      · exact prime_oneHundredFiftyFiveEW_211
      · exact prime_oneHundredFiftyFiveEW_263
      · exact prime_oneHundredFiftyFiveEW_563
      · exact prime_oneHundredFiftyFiveEW_718627833483094957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 3457572962942216533287944303) ^ 1728786481471108266643972151 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 3457572962942216533287944303) ^ 493938994706030933326849186 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 3457572962942216533287944303) ^ 314324814812928775753449482 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 3457572962942216533287944303) ^ 16386601720105291626957082 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 3457572962942216533287944303) ^ 13146665258335424080942754 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 3457572962942216533287944303) ^ 6141337411975517821115354 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 3457572962942216533287944303) ^ 4811354086 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_16659215185085225114932822547 : Nat.Prime 16659215185085225114932822547 := by
  apply lucas_primality 16659215185085225114932822547 (2 : ZMod 16659215185085225114932822547)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (53, 1), (211, 1), (263, 1), (563, 1), (718627833483094957, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (53, 1), (211, 1), (263, 1), (563, 1), (718627833483094957, 1)] : List FactorBlock).map factorBlockValue).prod) = 16659215185085225114932822547 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_7
      · exact prime_oneHundredFiftyFiveEW_53
      · exact prime_oneHundredFiftyFiveEW_211
      · exact prime_oneHundredFiftyFiveEW_263
      · exact prime_oneHundredFiftyFiveEW_563
      · exact prime_oneHundredFiftyFiveEW_718627833483094957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 16659215185085225114932822547) ^ 8329607592542612557466411273 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 16659215185085225114932822547) ^ 2379887883583603587847546078 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 16659215185085225114932822547) ^ 314324814812928775753449482 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 16659215185085225114932822547) ^ 78953626469598223293520486 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 16659215185085225114932822547) ^ 63343023517434316026360542 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 16659215185085225114932822547) ^ 29590080257700222229010342 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 16659215185085225114932822547) ^ 23181978778 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_18325136703593747626426104803 : Nat.Prime 18325136703593747626426104803 := by
  apply lucas_primality 18325136703593747626426104803 (2 : ZMod 18325136703593747626426104803)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (353, 1), (431, 1), (106747, 1), (11513662460653469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (353, 1), (431, 1), (106747, 1), (11513662460653469, 1)] : List FactorBlock).map factorBlockValue).prod) = 18325136703593747626426104803 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_7
      · exact prime_oneHundredFiftyFiveEW_353
      · exact prime_oneHundredFiftyFiveEW_431
      · exact prime_oneHundredFiftyFiveEW_106747
      · exact prime_oneHundredFiftyFiveEW_11513662460653469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 18325136703593747626426104803) ^ 9162568351796873813213052401 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 18325136703593747626426104803) ^ 2617876671941963946632300686 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 18325136703593747626426104803) ^ 51912568565421381377977634 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 18325136703593747626426104803) ^ 42517718569823080339735742 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 18325136703593747626426104803) ^ 171668868479617671938566 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 18325136703593747626426104803) ^ 1591599264458 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_36650273407187495252852209609 : Nat.Prime 36650273407187495252852209609 := by
  apply lucas_primality 36650273407187495252852209609 (11 : ZMod 36650273407187495252852209609)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (193, 1), (1021, 1), (8184194567, 1), (105211804913, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (193, 1), (1021, 1), (8184194567, 1), (105211804913, 1)] : List FactorBlock).map factorBlockValue).prod) = 36650273407187495252852209609 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_3
      · exact prime_oneHundredFiftyFiveEW_193
      · exact prime_oneHundredFiftyFiveEW_1021
      · exact prime_oneHundredFiftyFiveEW_8184194567
      · exact prime_oneHundredFiftyFiveEW_105211804913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 36650273407187495252852209609) ^ 18325136703593747626426104804 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (11 : ZMod 36650273407187495252852209609) ^ 12216757802395831750950736536 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (11 : ZMod 36650273407187495252852209609) ^ 189897789674546607527731656 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (11 : ZMod 36650273407187495252852209609) ^ 35896447999204206907788648 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (11 : ZMod 36650273407187495252852209609) ^ 4478177187400620024 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (11 : ZMod 36650273407187495252852209609) ^ 348347539874387016 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_91625683517968738132130524007 : Nat.Prime 91625683517968738132130524007 := by
  apply lucas_primality 91625683517968738132130524007 (5 : ZMod 91625683517968738132130524007)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11273, 1), (4063944092875398657506011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11273, 1), (4063944092875398657506011, 1)] : List FactorBlock).map factorBlockValue).prod) = 91625683517968738132130524007 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_11273
      · exact prime_oneHundredFiftyFiveEW_4063944092875398657506011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 91625683517968738132130524007) ^ 45812841758984369066065262003 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 91625683517968738132130524007) ^ 8127888185750797315012022 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (5 : ZMod 91625683517968738132130524007) ^ 22546 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_183251367035937476264261048003 : Nat.Prime 183251367035937476264261048003 := by
  apply lucas_primality 183251367035937476264261048003 (2 : ZMod 183251367035937476264261048003)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (4914987577, 1), (18642098699646161513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (4914987577, 1), (18642098699646161513, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048003 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_4914987577
      · exact prime_oneHundredFiftyFiveEW_18642098699646161513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 183251367035937476264261048003) ^ 91625683517968738132130524001 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 183251367035937476264261048003) ^ 37284197399292323026 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (2 : ZMod 183251367035937476264261048003) ^ 9829975154 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyFiveEW_183251367035937476264261048057 : Nat.Prime 183251367035937476264261048057 := by
  apply lucas_primality 183251367035937476264261048057 (3 : ZMod 183251367035937476264261048057)
  · rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (137, 1), (2213, 1), (1466177, 1), (5301337, 1), (9720384403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (137, 1), (2213, 1), (1466177, 1), (5301337, 1), (9720384403, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048057 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyFiveEW_2
      · exact prime_oneHundredFiftyFiveEW_137
      · exact prime_oneHundredFiftyFiveEW_2213
      · exact prime_oneHundredFiftyFiveEW_1466177
      · exact prime_oneHundredFiftyFiveEW_5301337
      · exact prime_oneHundredFiftyFiveEW_9720384403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 183251367035937476264261048057) ^ 91625683517968738132130524028 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 183251367035937476264261048057) ^ 1337601219240419534775628088 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 183251367035937476264261048057) ^ 82806763233591268081455512 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 183251367035937476264261048057) ^ 124985842115881968046328 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 183251367035937476264261048057) ^ 34567009612091718799288 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide
    · change (3 : ZMod 183251367035937476264261048057) ^ 18852275737097459752 ≠ 1
      rw [← oneHundredFiftyFiveEWFastPow_eq_pow]
      decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048000 : Nat.totient 183251367035937476264261048000 = 70935599075102811283737600000 := by
  rw [← show ((([(2, 6), (5, 3), (31, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048000 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_2, prime_oneHundredFiftyFiveEW_5, prime_oneHundredFiftyFiveEW_31, prime_oneHundredFiftyFiveEW_171401, prime_oneHundredFiftyFiveEW_714027719, prime_oneHundredFiftyFiveEW_6037638679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048001 : Nat.totient 183251367035937476264261048001 = 120399737650862710239698300928 := by
  rw [← show ((([(3, 1), (73, 1), (1279, 1), (1176589, 1), (556042234571677409, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048001 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_3, prime_oneHundredFiftyFiveEW_73, prime_oneHundredFiftyFiveEW_1279, prime_oneHundredFiftyFiveEW_1176589, prime_oneHundredFiftyFiveEW_556042234571677409]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048002 : Nat.totient 183251367035937476264261048002 = 91625683499326639427569374912 := by
  rw [← show ((([(2, 1), (4914987577, 1), (18642098699646161513, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048002 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_2, prime_oneHundredFiftyFiveEW_4914987577, prime_oneHundredFiftyFiveEW_18642098699646161513]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048003 : Nat.totient 183251367035937476264261048003 = 183251367035937476264261048002 := by
  rw [← show ((([(183251367035937476264261048003, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048003 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_183251367035937476264261048003]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048004 : Nat.totient 183251367035937476264261048004 = 57488836684294804023322214400 := by
  rw [← show ((([(2, 2), (3, 2), (17, 2), (35059, 1), (397073, 1), (21368801, 1), (59210243, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048004 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_2, prime_oneHundredFiftyFiveEW_3, prime_oneHundredFiftyFiveEW_17, prime_oneHundredFiftyFiveEW_35059, prime_oneHundredFiftyFiveEW_397073, prime_oneHundredFiftyFiveEW_21368801, prime_oneHundredFiftyFiveEW_59210243]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048005 : Nat.totient 183251367035937476264261048005 = 138871599622424541002661276672 := by
  rw [← show ((([(5, 1), (19, 1), (10177, 1), (189541294907440902617627, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048005 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_5, prime_oneHundredFiftyFiveEW_19, prime_oneHundredFiftyFiveEW_10177, prime_oneHundredFiftyFiveEW_189541294907440902617627]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048006 : Nat.totient 183251367035937476264261048006 = 69329094774609743041068172800 := by
  rw [← show ((([(2, 1), (7, 1), (11, 1), (53, 1), (211, 1), (263, 1), (563, 1), (718627833483094957, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048006 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_2, prime_oneHundredFiftyFiveEW_7, prime_oneHundredFiftyFiveEW_11, prime_oneHundredFiftyFiveEW_53, prime_oneHundredFiftyFiveEW_211, prime_oneHundredFiftyFiveEW_263, prime_oneHundredFiftyFiveEW_563, prime_oneHundredFiftyFiveEW_718627833483094957]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048007 : Nat.totient 183251367035937476264261048007 = 121418083680253051757915295288 := by
  rw [← show ((([(3, 1), (163, 1), (374747171852632875796034863, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048007 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_3, prime_oneHundredFiftyFiveEW_163, prime_oneHundredFiftyFiveEW_374747171852632875796034863]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048008 : Nat.totient 183251367035937476264261048008 = 90521749309593822829416532800 := by
  rw [← show ((([(2, 3), (83, 1), (15402547, 1), (20418131, 1), (877547463371, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048008 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_2, prime_oneHundredFiftyFiveEW_83, prime_oneHundredFiftyFiveEW_15402547, prime_oneHundredFiftyFiveEW_20418131, prime_oneHundredFiftyFiveEW_877547463371]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048009 : Nat.totient 183251367035937476264261048009 = 166288072303797240521415500496 := by
  rw [← show ((([(13, 1), (59, 1), (238919644114651207645711927, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048009 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_13, prime_oneHundredFiftyFiveEW_59, prime_oneHundredFiftyFiveEW_238919644114651207645711927]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048010 : Nat.totient 183251367035937476264261048010 = 48867031113276876450109337600 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (966324071, 1), (1399501757, 1), (4516788161, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048010 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_2, prime_oneHundredFiftyFiveEW_3, prime_oneHundredFiftyFiveEW_5, prime_oneHundredFiftyFiveEW_966324071, prime_oneHundredFiftyFiveEW_1399501757, prime_oneHundredFiftyFiveEW_4516788161]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048011 : Nat.totient 183251367035937476264261048011 = 182955322802272591113378253128 := by
  rw [← show ((([(619, 1), (8325551827, 1), (35558509254562747, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048011 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_619, prime_oneHundredFiftyFiveEW_8325551827, prime_oneHundredFiftyFiveEW_35558509254562747]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048012 : Nat.totient 183251367035937476264261048012 = 91617555629782987334815489440 := by
  rw [← show ((([(2, 2), (11273, 1), (4063944092875398657506011, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048012 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_2, prime_oneHundredFiftyFiveEW_11273, prime_oneHundredFiftyFiveEW_4063944092875398657506011]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048013 : Nat.totient 183251367035937476264261048013 = 103629492969558383942412443712 := by
  rw [← show ((([(3, 5), (7, 1), (167, 1), (227, 1), (2841846270956172113957, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048013 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_3, prime_oneHundredFiftyFiveEW_7, prime_oneHundredFiftyFiveEW_167, prime_oneHundredFiftyFiveEW_227, prime_oneHundredFiftyFiveEW_2841846270956172113957]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048014 : Nat.totient 183251367035937476264261048014 = 91625683517968738132130524006 := by
  rw [← show ((([(2, 1), (91625683517968738132130524007, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048014 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_2, prime_oneHundredFiftyFiveEW_91625683517968738132130524007]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048015 : Nat.totient 183251367035937476264261048015 = 146242047010434445112033494272 := by
  rw [← show ((([(5, 1), (463, 1), (3449, 1), (22951075064915360481269, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048015 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_5, prime_oneHundredFiftyFiveEW_463, prime_oneHundredFiftyFiveEW_3449, prime_oneHundredFiftyFiveEW_22951075064915360481269]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048016 : Nat.totient 183251367035937476264261048016 = 61081566856366939972052520960 := by
  rw [← show ((([(2, 4), (3, 1), (27997, 1), (1529191, 1), (254960869, 1), (349751209, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048016 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_2, prime_oneHundredFiftyFiveEW_3, prime_oneHundredFiftyFiveEW_27997, prime_oneHundredFiftyFiveEW_1529191, prime_oneHundredFiftyFiveEW_254960869, prime_oneHundredFiftyFiveEW_349751209]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048017 : Nat.totient 183251367035937476264261048017 = 166592151850852251149328225460 := by
  rw [← show ((([(11, 1), (16659215185085225114932822547, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048017 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_11, prime_oneHundredFiftyFiveEW_16659215185085225114932822547]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048018 : Nat.totient 183251367035937476264261048018 = 87641951010282435551586337536 := by
  rw [← show ((([(2, 1), (23, 1), (12279359, 1), (324424537986589273537, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048018 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_2, prime_oneHundredFiftyFiveEW_23, prime_oneHundredFiftyFiveEW_12279359, prime_oneHundredFiftyFiveEW_324424537986589273537]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048019 : Nat.totient 183251367035937476264261048019 = 122167578023939853230716932840 := by
  rw [← show ((([(3, 1), (6621176997011, 1), (9225518218219243, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048019 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_3, prime_oneHundredFiftyFiveEW_6621176997011, prime_oneHundredFiftyFiveEW_9225518218219243]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048020 : Nat.totient 183251367035937476264261048020 = 62505106552711585996320890880 := by
  rw [← show ((([(2, 2), (5, 1), (7, 2), (353, 1), (431, 1), (106747, 1), (11513662460653469, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048020 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_2, prime_oneHundredFiftyFiveEW_5, prime_oneHundredFiftyFiveEW_7, prime_oneHundredFiftyFiveEW_353, prime_oneHundredFiftyFiveEW_431, prime_oneHundredFiftyFiveEW_106747, prime_oneHundredFiftyFiveEW_11513662460653469]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048021 : Nat.totient 183251367035937476264261048021 = 164315889100739729371235696640 := by
  rw [← show ((([(17, 1), (41, 1), (43, 1), (5783, 1), (21587, 1), (926099, 1), (52886288569, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048021 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_17, prime_oneHundredFiftyFiveEW_41, prime_oneHundredFiftyFiveEW_43, prime_oneHundredFiftyFiveEW_5783, prime_oneHundredFiftyFiveEW_21587, prime_oneHundredFiftyFiveEW_926099, prime_oneHundredFiftyFiveEW_52886288569]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048022 : Nat.totient 183251367035937476264261048022 = 56336884827444484590208265280 := by
  rw [← show ((([(2, 1), (3, 2), (13, 1), (1171, 1), (668766439072227974717573, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048022 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_2, prime_oneHundredFiftyFiveEW_3, prime_oneHundredFiftyFiveEW_13, prime_oneHundredFiftyFiveEW_1171, prime_oneHundredFiftyFiveEW_668766439072227974717573]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048023 : Nat.totient 183251367035937476264261048023 = 183195807455376937359756979200 := by
  rw [← show ((([(3463, 1), (98017, 1), (236813, 1), (2279752948297301, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048023 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_3463, prime_oneHundredFiftyFiveEW_98017, prime_oneHundredFiftyFiveEW_236813, prime_oneHundredFiftyFiveEW_2279752948297301]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048024 : Nat.totient 183251367035937476264261048024 = 86802902321244703471920678912 := by
  rw [← show ((([(2, 3), (19, 1), (230369, 1), (5233347798187435337273, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048024 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_2, prime_oneHundredFiftyFiveEW_19, prime_oneHundredFiftyFiveEW_230369, prime_oneHundredFiftyFiveEW_5233347798187435337273]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048025 : Nat.totient 183251367035937476264261048025 = 97640349627542898106300423680 := by
  rw [← show ((([(3, 1), (5, 2), (1259, 1), (6073, 1), (24177523, 1), (13217372915987, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048025 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_3, prime_oneHundredFiftyFiveEW_5, prime_oneHundredFiftyFiveEW_1259, prime_oneHundredFiftyFiveEW_6073, prime_oneHundredFiftyFiveEW_24177523, prime_oneHundredFiftyFiveEW_13217372915987]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048026 : Nat.totient 183251367035937476264261048026 = 88463214788892619775408972208 := by
  rw [← show ((([(2, 1), (29, 3), (29863, 1), (125802652891956842959, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048026 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_2, prime_oneHundredFiftyFiveEW_29, prime_oneHundredFiftyFiveEW_29863, prime_oneHundredFiftyFiveEW_125802652891956842959]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048027 : Nat.totient 183251367035937476264261048027 = 152826462510835033443793995648 := by
  rw [← show ((([(7, 1), (37, 1), (163909, 1), (4316628346582495505717, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048027 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_7, prime_oneHundredFiftyFiveEW_37, prime_oneHundredFiftyFiveEW_163909, prime_oneHundredFiftyFiveEW_4316628346582495505717]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048028 : Nat.totient 183251367035937476264261048028 = 55039295006739331392111436800 := by
  rw [← show ((([(2, 2), (3, 1), (11, 1), (113, 1), (2928612849443, 1), (4195008883981, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048028 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_2, prime_oneHundredFiftyFiveEW_3, prime_oneHundredFiftyFiveEW_11, prime_oneHundredFiftyFiveEW_113, prime_oneHundredFiftyFiveEW_2928612849443, prime_oneHundredFiftyFiveEW_4195008883981]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048029 : Nat.totient 183251367035937476264261048029 = 182856512228186872473234694080 := by
  rw [← show ((([(467, 1), (74527, 1), (5265222190745853492881, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048029 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_467, prime_oneHundredFiftyFiveEW_74527, prime_oneHundredFiftyFiveEW_5265222190745853492881]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048030 : Nat.totient 183251367035937476264261048030 = 73300546814374990505704419208 := by
  rw [← show ((([(2, 1), (5, 1), (18325136703593747626426104803, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048030 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_2, prime_oneHundredFiftyFiveEW_5, prime_oneHundredFiftyFiveEW_18325136703593747626426104803]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048031 : Nat.totient 183251367035937476264261048031 = 118226493706465937299327456320 := by
  rw [← show ((([(3, 2), (31, 1), (607213, 1), (1081687868363620552253, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048031 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_3, prime_oneHundredFiftyFiveEW_31, prime_oneHundredFiftyFiveEW_607213, prime_oneHundredFiftyFiveEW_1081687868363620552253]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048032 : Nat.totient 183251367035937476264261048032 = 91625667689523122117885675520 := by
  rw [← show ((([(2, 5), (5824333, 1), (946301827, 1), (1039013926961, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048032 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_2, prime_oneHundredFiftyFiveEW_5824333, prime_oneHundredFiftyFiveEW_946301827, prime_oneHundredFiftyFiveEW_1039013926961]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048033 : Nat.totient 183251367035937476264261048033 = 182767279788586158904210719888 := by
  rw [← show ((([(643, 1), (919, 1), (310113547310260960954349, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048033 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_643, prime_oneHundredFiftyFiveEW_919, prime_oneHundredFiftyFiveEW_310113547310260960954349]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048034 : Nat.totient 183251367035937476264261048034 = 51694778998606869424013045760 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (79, 1), (71869657, 1), (530657371, 1), (1448141729, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048034 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_2, prime_oneHundredFiftyFiveEW_3, prime_oneHundredFiftyFiveEW_7, prime_oneHundredFiftyFiveEW_79, prime_oneHundredFiftyFiveEW_71869657, prime_oneHundredFiftyFiveEW_530657371, prime_oneHundredFiftyFiveEW_1448141729]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048035 : Nat.totient 183251367035937476264261048035 = 135083630856193679353896566784 := by
  rw [← show ((([(5, 1), (13, 1), (953, 1), (1373, 1), (1114172737, 1), (1933828254263, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048035 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_5, prime_oneHundredFiftyFiveEW_13, prime_oneHundredFiftyFiveEW_953, prime_oneHundredFiftyFiveEW_1373, prime_oneHundredFiftyFiveEW_1114172737, prime_oneHundredFiftyFiveEW_1933828254263]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048036 : Nat.totient 183251367035937476264261048036 = 91624695717068390313656107200 := by
  rw [← show ((([(2, 2), (100391, 1), (1219831, 1), (374104373566082329, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048036 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_2, prime_oneHundredFiftyFiveEW_100391, prime_oneHundredFiftyFiveEW_1219831, prime_oneHundredFiftyFiveEW_374104373566082329]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048037 : Nat.totient 183251367035937476264261048037 = 121347661392925040210785839120 := by
  rw [← show ((([(3, 1), (149, 1), (409958315516638649360762971, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048037 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_3, prime_oneHundredFiftyFiveEW_149, prime_oneHundredFiftyFiveEW_409958315516638649360762971]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048038 : Nat.totient 183251367035937476264261048038 = 84948554374703187985936576512 := by
  rw [← show ((([(2, 1), (17, 1), (67, 1), (532093, 1), (708733, 1), (213315936919609, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048038 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_2, prime_oneHundredFiftyFiveEW_17, prime_oneHundredFiftyFiveEW_67, prime_oneHundredFiftyFiveEW_532093, prime_oneHundredFiftyFiveEW_708733, prime_oneHundredFiftyFiveEW_213315936919609]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048039 : Nat.totient 183251367035937476264261048039 = 164966665031839545554145850560 := by
  rw [← show ((([(11, 2), (103, 1), (20543, 1), (2915509, 1), (245497105242619, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048039 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_11, prime_oneHundredFiftyFiveEW_103, prime_oneHundredFiftyFiveEW_20543, prime_oneHundredFiftyFiveEW_2915509, prime_oneHundredFiftyFiveEW_245497105242619]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048040 : Nat.totient 183251367035937476264261048040 = 48566220208900633959644528640 := by
  rw [← show ((([(2, 3), (3, 3), (5, 1), (193, 1), (1021, 1), (8184194567, 1), (105211804913, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048040 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_2, prime_oneHundredFiftyFiveEW_3, prime_oneHundredFiftyFiveEW_5, prime_oneHundredFiftyFiveEW_193, prime_oneHundredFiftyFiveEW_1021, prime_oneHundredFiftyFiveEW_8184194567, prime_oneHundredFiftyFiveEW_105211804913]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048041 : Nat.totient 183251367035937476264261048041 = 150241659140263585125620421648 := by
  rw [← show ((([(7, 1), (23, 1), (88499, 1), (12861244179825976646419, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048041 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_7, prime_oneHundredFiftyFiveEW_23, prime_oneHundredFiftyFiveEW_88499, prime_oneHundredFiftyFiveEW_12861244179825976646419]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048042 : Nat.totient 183251367035937476264261048042 = 91625683517323653152693182252 := by
  rw [← show ((([(2, 1), (142036641083, 1), (645084837400700687, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048042 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_2, prime_oneHundredFiftyFiveEW_142036641083, prime_oneHundredFiftyFiveEW_645084837400700687]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048043 : Nat.totient 183251367035937476264261048043 = 113248474856577739517809881600 := by
  rw [← show ((([(3, 1), (19, 1), (47, 1), (4241, 1), (6774191, 1), (2380941909280307, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048043 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_3, prime_oneHundredFiftyFiveEW_19, prime_oneHundredFiftyFiveEW_47, prime_oneHundredFiftyFiveEW_4241, prime_oneHundredFiftyFiveEW_6774191, prime_oneHundredFiftyFiveEW_2380941909280307]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048044 : Nat.totient 183251367035937476264261048044 = 91620825747315281271963044160 := by
  rw [← show ((([(2, 2), (19541, 1), (542533, 1), (4321298704489309187, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048044 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_2, prime_oneHundredFiftyFiveEW_19541, prime_oneHundredFiftyFiveEW_542533, prime_oneHundredFiftyFiveEW_4321298704489309187]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048045 : Nat.totient 183251367035937476264261048045 = 146601093628749981011408838432 := by
  rw [← show ((([(5, 1), (36650273407187495252852209609, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048045 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_5, prime_oneHundredFiftyFiveEW_36650273407187495252852209609]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048046 : Nat.totient 183251367035937476264261048046 = 61073377499631233862757207296 := by
  rw [← show ((([(2, 1), (3, 1), (5867, 1), (646860439, 1), (8047653949077857, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048046 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_2, prime_oneHundredFiftyFiveEW_3, prime_oneHundredFiftyFiveEW_5867, prime_oneHundredFiftyFiveEW_646860439, prime_oneHundredFiftyFiveEW_8047653949077857]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048047 : Nat.totient 183251367035937476264261048047 = 183232039963305348722963269728 := by
  rw [← show ((([(13219, 1), (34267, 1), (2054519, 1), (9800207, 1), (20092183, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048047 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_13219, prime_oneHundredFiftyFiveEW_34267, prime_oneHundredFiftyFiveEW_2054519, prime_oneHundredFiftyFiveEW_9800207, prime_oneHundredFiftyFiveEW_20092183]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048048 : Nat.totient 183251367035937476264261048048 = 72495045012625660192947148800 := by
  rw [← show ((([(2, 4), (7, 1), (13, 1), (56315333, 1), (2234905640739533401, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048048 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_2, prime_oneHundredFiftyFiveEW_7, prime_oneHundredFiftyFiveEW_13, prime_oneHundredFiftyFiveEW_56315333, prime_oneHundredFiftyFiveEW_2234905640739533401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048049 : Nat.totient 183251367035937476264261048049 = 122111146757945206804157700480 := by
  rw [← show ((([(3, 2), (2909, 1), (8461, 1), (134653427, 1), (6143585213707, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048049 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_3, prime_oneHundredFiftyFiveEW_2909, prime_oneHundredFiftyFiveEW_8461, prime_oneHundredFiftyFiveEW_134653427, prime_oneHundredFiftyFiveEW_6143585213707]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048050 : Nat.totient 183251367035937476264261048050 = 65486087687040059113899264000 := by
  rw [← show ((([(2, 1), (5, 2), (11, 1), (61, 1), (1123, 1), (23242647853, 1), (209261502889, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048050 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_2, prime_oneHundredFiftyFiveEW_5, prime_oneHundredFiftyFiveEW_11, prime_oneHundredFiftyFiveEW_61, prime_oneHundredFiftyFiveEW_1123, prime_oneHundredFiftyFiveEW_23242647853, prime_oneHundredFiftyFiveEW_209261502889]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048051 : Nat.totient 183251367035937476264261048051 = 183251364283789818634738774368 := by
  rw [← show ((([(75872317, 1), (544020469, 1), (4439648997587, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048051 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_75872317, prime_oneHundredFiftyFiveEW_544020469, prime_oneHundredFiftyFiveEW_4439648997587]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048052 : Nat.totient 183251367035937476264261048052 = 61083788985602220472294810048 := by
  rw [← show ((([(2, 2), (3, 1), (2315802857, 1), (6594234568298915303, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048052 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_2, prime_oneHundredFiftyFiveEW_3, prime_oneHundredFiftyFiveEW_2315802857, prime_oneHundredFiftyFiveEW_6594234568298915303]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048053 : Nat.totient 183251367035937476264261048053 = 183191027435285373924150717360 := by
  rw [← show ((([(3037, 1), (6806167501039, 1), (8865429861271, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048053 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_3037, prime_oneHundredFiftyFiveEW_6806167501039, prime_oneHundredFiftyFiveEW_8865429861271]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048054 : Nat.totient 183251367035937476264261048054 = 91580617416279830434366464000 := by
  rw [← show ((([(2, 1), (3673, 1), (6827, 1), (17377, 1), (107981, 1), (158791, 1), (12263611, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048054 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_2, prime_oneHundredFiftyFiveEW_3673, prime_oneHundredFiftyFiveEW_6827, prime_oneHundredFiftyFiveEW_17377, prime_oneHundredFiftyFiveEW_107981, prime_oneHundredFiftyFiveEW_158791, prime_oneHundredFiftyFiveEW_12263611]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048055 : Nat.totient 183251367035937476264261048055 = 76034741423343800185141272576 := by
  rw [← show ((([(3, 1), (5, 1), (7, 1), (17, 1), (29, 1), (839, 1), (1805059, 1), (2337532415679887, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048055 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_3, prime_oneHundredFiftyFiveEW_5, prime_oneHundredFiftyFiveEW_7, prime_oneHundredFiftyFiveEW_17, prime_oneHundredFiftyFiveEW_29, prime_oneHundredFiftyFiveEW_839, prime_oneHundredFiftyFiveEW_1805059, prime_oneHundredFiftyFiveEW_2337532415679887]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048056 : Nat.totient 183251367035937476264261048056 = 90915702573524365733147836416 := by
  rw [← show ((([(2, 3), (137, 1), (2213, 1), (1466177, 1), (5301337, 1), (9720384403, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048056 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_2, prime_oneHundredFiftyFiveEW_137, prime_oneHundredFiftyFiveEW_2213, prime_oneHundredFiftyFiveEW_1466177, prime_oneHundredFiftyFiveEW_5301337, prime_oneHundredFiftyFiveEW_9720384403]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048057 : Nat.totient 183251367035937476264261048057 = 183251367035937476264261048056 := by
  rw [← show ((([(183251367035937476264261048057, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048057 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_183251367035937476264261048057]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048058 : Nat.totient 183251367035937476264261048058 = 61082324924819026898383499520 := by
  rw [← show ((([(2, 1), (3, 2), (41761, 1), (44014567, 1), (5538694287583363, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048058 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_2, prime_oneHundredFiftyFiveEW_3, prime_oneHundredFiftyFiveEW_41761, prime_oneHundredFiftyFiveEW_44014567, prime_oneHundredFiftyFiveEW_5538694287583363]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048059 : Nat.totient 183251367035937476264261048059 = 179793794072995259730973103704 := by
  rw [← show ((([(53, 1), (3457572962942216533287944303, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048059 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_53, prime_oneHundredFiftyFiveEW_3457572962942216533287944303]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048060 : Nat.totient 183251367035937476264261048060 = 73300546814373336716479108544 := by
  rw [← show ((([(2, 2), (5, 1), (64360559390279, 1), (142363093773557, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048060 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_2, prime_oneHundredFiftyFiveEW_5, prime_oneHundredFiftyFiveEW_64360559390279, prime_oneHundredFiftyFiveEW_142363093773557]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048061 : Nat.totient 183251367035937476264261048061 = 101981491660449806725986432000 := by
  rw [← show ((([(3, 1), (11, 1), (13, 1), (191, 1), (9371441, 1), (238643817878991839, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048061 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_3, prime_oneHundredFiftyFiveEW_11, prime_oneHundredFiftyFiveEW_13, prime_oneHundredFiftyFiveEW_191, prime_oneHundredFiftyFiveEW_9371441, prime_oneHundredFiftyFiveEW_238643817878991839]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048062 : Nat.totient 183251367035937476264261048062 = 70069607494940110200746803200 := by
  rw [← show ((([(2, 1), (7, 1), (19, 1), (31, 1), (41, 1), (397, 1), (13617913, 1), (100257985466497, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048062 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_2, prime_oneHundredFiftyFiveEW_7, prime_oneHundredFiftyFiveEW_19, prime_oneHundredFiftyFiveEW_31, prime_oneHundredFiftyFiveEW_41, prime_oneHundredFiftyFiveEW_397, prime_oneHundredFiftyFiveEW_13617913, prime_oneHundredFiftyFiveEW_100257985466497]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048063 : Nat.totient 183251367035937476264261048063 = 182575158333073375969791367200 := by
  rw [← show ((([(271, 1), (41527781, 1), (16283179359033735613, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048063 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_271, prime_oneHundredFiftyFiveEW_41527781, prime_oneHundredFiftyFiveEW_16283179359033735613]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048064 : Nat.totient 183251367035937476264261048064 = 55464127210729639777148928000 := by
  rw [← show ((([(2, 8), (3, 1), (23, 1), (37, 1), (43, 1), (991, 1), (9203, 1), (94651, 1), (7553699507, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048064 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_2, prime_oneHundredFiftyFiveEW_3, prime_oneHundredFiftyFiveEW_23, prime_oneHundredFiftyFiveEW_37, prime_oneHundredFiftyFiveEW_43, prime_oneHundredFiftyFiveEW_991, prime_oneHundredFiftyFiveEW_9203, prime_oneHundredFiftyFiveEW_94651, prime_oneHundredFiftyFiveEW_7553699507]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048065 : Nat.totient 183251367035937476264261048065 = 142820049773381801808278592000 := by
  rw [← show ((([(5, 1), (71, 1), (109, 1), (367, 1), (12904058043247987123801, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048065 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_5, prime_oneHundredFiftyFiveEW_71, prime_oneHundredFiftyFiveEW_109, prime_oneHundredFiftyFiveEW_367, prime_oneHundredFiftyFiveEW_12904058043247987123801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048066 : Nat.totient 183251367035937476264261048066 = 91247526908893593598497522000 := by
  rw [← show ((([(2, 1), (251, 1), (6959, 1), (52456181034144060706237, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048066 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_2, prime_oneHundredFiftyFiveEW_251, prime_oneHundredFiftyFiveEW_6959, prime_oneHundredFiftyFiveEW_52456181034144060706237]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048067 : Nat.totient 183251367035937476264261048067 = 122167578023954237882753106336 := by
  rw [← show ((([(3, 3), (35509041075533, 1), (191136889716637, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048067 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_3, prime_oneHundredFiftyFiveEW_35509041075533, prime_oneHundredFiftyFiveEW_191136889716637]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048068 : Nat.totient 183251367035937476264261048068 = 90072507553074946423497185280 := by
  rw [← show ((([(2, 2), (59, 1), (454297, 1), (9672156961, 1), (176714430539, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048068 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_2, prime_oneHundredFiftyFiveEW_59, prime_oneHundredFiftyFiveEW_454297, prime_oneHundredFiftyFiveEW_9672156961, prime_oneHundredFiftyFiveEW_176714430539]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048069 : Nat.totient 183251367035937476264261048069 = 156513623089863689889515304000 := by
  rw [← show ((([(7, 2), (281, 1), (117938908511, 1), (112846402628291, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048069 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_7, prime_oneHundredFiftyFiveEW_281, prime_oneHundredFiftyFiveEW_117938908511, prime_oneHundredFiftyFiveEW_112846402628291]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048070 : Nat.totient 183251367035937476264261048070 = 48858710137903197244192296960 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (5897, 1), (1424021, 1), (727408625826681937, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048070 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_2, prime_oneHundredFiftyFiveEW_3, prime_oneHundredFiftyFiveEW_5, prime_oneHundredFiftyFiveEW_5897, prime_oneHundredFiftyFiveEW_1424021, prime_oneHundredFiftyFiveEW_727408625826681937]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048071 : Nat.totient 183251367035937476264261048071 = 183243424104680229613649250000 := by
  rw [← show ((([(23071, 1), (7942931257246650611775001, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048071 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_23071, prime_oneHundredFiftyFiveEW_7942931257246650611775001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048072 : Nat.totient 183251367035937476264261048072 = 78317674531508985541718876160 := by
  rw [← show ((([(2, 3), (11, 1), (17, 1), (997, 1), (4240926479, 1), (28970749284089, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048072 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_2, prime_oneHundredFiftyFiveEW_11, prime_oneHundredFiftyFiveEW_17, prime_oneHundredFiftyFiveEW_997, prime_oneHundredFiftyFiveEW_4240926479, prime_oneHundredFiftyFiveEW_28970749284089]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048073 : Nat.totient 183251367035937476264261048073 = 122167578023932779188749556304 := by
  rw [← show ((([(3, 1), (4785490048973, 1), (12764374888855567, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048073 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_3, prime_oneHundredFiftyFiveEW_4785490048973, prime_oneHundredFiftyFiveEW_12764374888855567]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048074 : Nat.totient 183251367035937476264261048074 = 83379316903557058690155970560 := by
  rw [← show ((([(2, 1), (13, 1), (73, 1), (2113, 1), (522947, 1), (40024703, 1), (2183060261, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048074 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_2, prime_oneHundredFiftyFiveEW_13, prime_oneHundredFiftyFiveEW_73, prime_oneHundredFiftyFiveEW_2113, prime_oneHundredFiftyFiveEW_522947, prime_oneHundredFiftyFiveEW_40024703, prime_oneHundredFiftyFiveEW_2183060261]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048075 : Nat.totient 183251367035937476264261048075 = 144380871575855571674686648320 := by
  rw [← show ((([(5, 2), (89, 1), (433, 1), (607, 1), (313357880006437214197, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048075 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_5, prime_oneHundredFiftyFiveEW_89, prime_oneHundredFiftyFiveEW_433, prime_oneHundredFiftyFiveEW_607, prime_oneHundredFiftyFiveEW_313357880006437214197]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048076 : Nat.totient 183251367035937476264261048076 = 51945269396013772799318083296 := by
  rw [← show ((([(2, 2), (3, 2), (7, 1), (127, 1), (5725889483687585185110019, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048076 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_2, prime_oneHundredFiftyFiveEW_3, prime_oneHundredFiftyFiveEW_7, prime_oneHundredFiftyFiveEW_127, prime_oneHundredFiftyFiveEW_5725889483687585185110019]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048077 : Nat.totient 183251367035937476264261048077 = 183250943403173749104862476000 := by
  rw [← show ((([(432587, 1), (11907887471, 1), (35574519037801, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048077 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_432587, prime_oneHundredFiftyFiveEW_11907887471, prime_oneHundredFiftyFiveEW_35574519037801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048078 : Nat.totient 183251367035937476264261048078 = 91625673001585337243605876680 := by
  rw [← show ((([(2, 1), (8712661, 1), (10516383400888515934699, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048078 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_2, prime_oneHundredFiftyFiveEW_8712661, prime_oneHundredFiftyFiveEW_10516383400888515934699]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048079 : Nat.totient 183251367035937476264261048079 = 122167562464169553113358317280 := by
  rw [← show ((([(3, 1), (12292699, 1), (21731947, 1), (228654674135581, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048079 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_3, prime_oneHundredFiftyFiveEW_12292699, prime_oneHundredFiftyFiveEW_21731947, prime_oneHundredFiftyFiveEW_228654674135581]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048080 : Nat.totient 183251367035937476264261048080 = 73300546814374990505704419200 := by
  rw [← show ((([(2, 4), (5, 1), (2290642087949218453303263101, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048080 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_2, prime_oneHundredFiftyFiveEW_5, prime_oneHundredFiftyFiveEW_2290642087949218453303263101]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048081 : Nat.totient 183251367035937476264261048081 = 173301450057850777664027827680 := by
  rw [← show ((([(19, 1), (569, 1), (16950454817864903918625571, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048081 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_19, prime_oneHundredFiftyFiveEW_569, prime_oneHundredFiftyFiveEW_16950454817864903918625571]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048082 : Nat.totient 183251367035937476264261048082 = 61081159150653461111547249120 := by
  rw [← show ((([(2, 1), (3, 1), (23227, 1), (1314930662848821603193561, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048082 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_2, prime_oneHundredFiftyFiveEW_3, prime_oneHundredFiftyFiveEW_23227, prime_oneHundredFiftyFiveEW_1314930662848821603193561]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048083 : Nat.totient 183251367035937476264261048083 = 142793273015016215270852764680 := by
  rw [← show ((([(7, 1), (11, 1), (2379887883583603587847546079, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048083 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_7, prime_oneHundredFiftyFiveEW_11, prime_oneHundredFiftyFiveEW_2379887883583603587847546079]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048084 : Nat.totient 183251367035937476264261048084 = 88466177188827704834198650880 := by
  rw [← show ((([(2, 2), (29, 1), (94595042561, 1), (16700168648734409, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048084 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_2, prime_oneHundredFiftyFiveEW_29, prime_oneHundredFiftyFiveEW_94595042561, prime_oneHundredFiftyFiveEW_16700168648734409]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048085 : Nat.totient 183251367035937476264261048085 = 96495931059817556986044543360 := by
  rw [← show ((([(3, 2), (5, 1), (131, 1), (199, 1), (20563, 1), (7596680508025691879, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048085 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_3, prime_oneHundredFiftyFiveEW_5, prime_oneHundredFiftyFiveEW_131, prime_oneHundredFiftyFiveEW_199, prime_oneHundredFiftyFiveEW_20563, prime_oneHundredFiftyFiveEW_7596680508025691879]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048086 : Nat.totient 183251367035937476264261048086 = 91332949704812288489535857520 := by
  rw [← show ((([(2, 1), (313, 1), (292733813156449642594666211, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048086 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_2, prime_oneHundredFiftyFiveEW_313, prime_oneHundredFiftyFiveEW_292733813156449642594666211]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048087 : Nat.totient 183251367035937476264261048087 = 161536641849467048160436137984 := by
  rw [← show ((([(13, 1), (23, 1), (709, 1), (4637, 1), (206303, 1), (2732579, 1), (330684953, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048087 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_13, prime_oneHundredFiftyFiveEW_23, prime_oneHundredFiftyFiveEW_709, prime_oneHundredFiftyFiveEW_4637, prime_oneHundredFiftyFiveEW_206303, prime_oneHundredFiftyFiveEW_2732579, prime_oneHundredFiftyFiveEW_330684953]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048088 : Nat.totient 183251367035937476264261048088 = 60488439253156258925570232192 := by
  rw [← show ((([(2, 3), (3, 1), (139, 1), (389, 1), (141211992130668839939047, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048088 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_2, prime_oneHundredFiftyFiveEW_3, prime_oneHundredFiftyFiveEW_139, prime_oneHundredFiftyFiveEW_389, prime_oneHundredFiftyFiveEW_141211992130668839939047]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048089 : Nat.totient 183251367035937476264261048089 = 172471874856974781053712834816 := by
  rw [← show ((([(17, 1), (456117349789, 1), (23633155335071453, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048089 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_17, prime_oneHundredFiftyFiveEW_456117349789, prime_oneHundredFiftyFiveEW_23633155335071453]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048090 : Nat.totient 183251367035937476264261048090 = 60857846810427993427068549120 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (47, 1), (97, 1), (131023, 1), (4382602193503262191, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048090 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_2, prime_oneHundredFiftyFiveEW_5, prime_oneHundredFiftyFiveEW_7, prime_oneHundredFiftyFiveEW_47, prime_oneHundredFiftyFiveEW_97, prime_oneHundredFiftyFiveEW_131023, prime_oneHundredFiftyFiveEW_4382602193503262191]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048091 : Nat.totient 183251367035937476264261048091 = 119437932290425327325731353600 := by
  rw [← show ((([(3, 1), (83, 1), (101, 1), (1907, 1), (1812089, 1), (12391007, 1), (170172619, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048091 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_3, prime_oneHundredFiftyFiveEW_83, prime_oneHundredFiftyFiveEW_101, prime_oneHundredFiftyFiveEW_1907, prime_oneHundredFiftyFiveEW_1812089, prime_oneHundredFiftyFiveEW_12391007, prime_oneHundredFiftyFiveEW_170172619]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048092 : Nat.totient 183251367035937476264261048092 = 91569367788881172156083220480 := by
  rw [← show ((([(2, 2), (1627, 1), (19329914629, 1), (1456698734350081, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048092 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_2, prime_oneHundredFiftyFiveEW_1627, prime_oneHundredFiftyFiveEW_19329914629, prime_oneHundredFiftyFiveEW_1456698734350081]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048093 : Nat.totient 183251367035937476264261048093 = 177339983340738967551032912640 := by
  rw [← show ((([(31, 2), (3599009, 1), (52983531609217552957, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048093 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_31, prime_oneHundredFiftyFiveEW_3599009, prime_oneHundredFiftyFiveEW_52983531609217552957]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048094 : Nat.totient 183251367035937476264261048094 = 55222338154282361670143232000 := by
  rw [← show ((([(2, 1), (3, 4), (11, 1), (181, 1), (34961, 1), (16250888185640250137, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048094 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_2, prime_oneHundredFiftyFiveEW_3, prime_oneHundredFiftyFiveEW_11, prime_oneHundredFiftyFiveEW_181, prime_oneHundredFiftyFiveEW_34961, prime_oneHundredFiftyFiveEW_16250888185640250137]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048095 : Nat.totient 183251367035937476264261048095 = 146601093623183114320575576576 := by
  rw [← show ((([(5, 1), (26334580033, 1), (1391716646373735443, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048095 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_5, prime_oneHundredFiftyFiveEW_26334580033, prime_oneHundredFiftyFiveEW_1391716646373735443]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048096 : Nat.totient 183251367035937476264261048096 = 91346580706955449419201745920 := by
  rw [← show ((([(2, 5), (337, 1), (12659, 1), (1342356728613354717491, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048096 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_2, prime_oneHundredFiftyFiveEW_337, prime_oneHundredFiftyFiveEW_12659, prime_oneHundredFiftyFiveEW_1342356728613354717491]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048097 : Nat.totient 183251367035937476264261048097 = 104715066676354698304771973712 := by
  rw [← show ((([(3, 1), (7, 1), (520132423, 1), (16776988296189872059, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048097 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_3, prime_oneHundredFiftyFiveEW_7, prime_oneHundredFiftyFiveEW_520132423, prime_oneHundredFiftyFiveEW_16776988296189872059]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048098 : Nat.totient 183251367035937476264261048098 = 91214806013403855898354153764 := by
  rw [← show ((([(2, 1), (223, 1), (410877504564882233776370063, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048098 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_2, prime_oneHundredFiftyFiveEW_223, prime_oneHundredFiftyFiveEW_410877504564882233776370063]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048099 : Nat.totient 183251367035937476264261048099 = 182868796332313389674982840840 := by
  rw [← show ((([(479, 1), (382570703624086589278206781, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048099 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_479, prime_oneHundredFiftyFiveEW_382570703624086589278206781]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048100 : Nat.totient 183251367035937476264261048100 = 42733919295231958770191147520 := by
  rw [← show ((([(2, 2), (3, 1), (5, 2), (13, 1), (19, 1), (15629399, 1), (158229238067428459, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048100 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_2, prime_oneHundredFiftyFiveEW_3, prime_oneHundredFiftyFiveEW_5, prime_oneHundredFiftyFiveEW_13, prime_oneHundredFiftyFiveEW_19, prime_oneHundredFiftyFiveEW_15629399, prime_oneHundredFiftyFiveEW_158229238067428459]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyFiveEW_183251367035937476264261048101 : Nat.totient 183251367035937476264261048101 = 177947979240058979488643248128 := by
  rw [← show ((([(37, 1), (769, 1), (1499, 1), (4296526812951097689683, 1)] : List FactorBlock).map factorBlockValue).prod) = 183251367035937476264261048101 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyFiveEW_37, prime_oneHundredFiftyFiveEW_769, prime_oneHundredFiftyFiveEW_1499, prime_oneHundredFiftyFiveEW_4296526812951097689683]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64OneHundredFiftyFiveEW : certifiedKill 1 183251367035937476264261047999 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_oneHundredFiftyFiveEW_183251367035937476264261048000, phi_oneHundredFiftyFiveEW_183251367035937476264261048001, phi_oneHundredFiftyFiveEW_183251367035937476264261048002,
    phi_oneHundredFiftyFiveEW_183251367035937476264261048003, phi_oneHundredFiftyFiveEW_183251367035937476264261048004, phi_oneHundredFiftyFiveEW_183251367035937476264261048005,
    phi_oneHundredFiftyFiveEW_183251367035937476264261048006, phi_oneHundredFiftyFiveEW_183251367035937476264261048007, phi_oneHundredFiftyFiveEW_183251367035937476264261048008,
    phi_oneHundredFiftyFiveEW_183251367035937476264261048009, phi_oneHundredFiftyFiveEW_183251367035937476264261048010, phi_oneHundredFiftyFiveEW_183251367035937476264261048011,
    phi_oneHundredFiftyFiveEW_183251367035937476264261048012, phi_oneHundredFiftyFiveEW_183251367035937476264261048013, phi_oneHundredFiftyFiveEW_183251367035937476264261048014,
    phi_oneHundredFiftyFiveEW_183251367035937476264261048015, phi_oneHundredFiftyFiveEW_183251367035937476264261048016, phi_oneHundredFiftyFiveEW_183251367035937476264261048017,
    phi_oneHundredFiftyFiveEW_183251367035937476264261048018, phi_oneHundredFiftyFiveEW_183251367035937476264261048019, phi_oneHundredFiftyFiveEW_183251367035937476264261048020,
    phi_oneHundredFiftyFiveEW_183251367035937476264261048021, phi_oneHundredFiftyFiveEW_183251367035937476264261048022, phi_oneHundredFiftyFiveEW_183251367035937476264261048023,
    phi_oneHundredFiftyFiveEW_183251367035937476264261048024, phi_oneHundredFiftyFiveEW_183251367035937476264261048025, phi_oneHundredFiftyFiveEW_183251367035937476264261048026,
    phi_oneHundredFiftyFiveEW_183251367035937476264261048027, phi_oneHundredFiftyFiveEW_183251367035937476264261048028, phi_oneHundredFiftyFiveEW_183251367035937476264261048029,
    phi_oneHundredFiftyFiveEW_183251367035937476264261048030, phi_oneHundredFiftyFiveEW_183251367035937476264261048031, phi_oneHundredFiftyFiveEW_183251367035937476264261048032,
    phi_oneHundredFiftyFiveEW_183251367035937476264261048033, phi_oneHundredFiftyFiveEW_183251367035937476264261048034, phi_oneHundredFiftyFiveEW_183251367035937476264261048035,
    phi_oneHundredFiftyFiveEW_183251367035937476264261048036, phi_oneHundredFiftyFiveEW_183251367035937476264261048037, phi_oneHundredFiftyFiveEW_183251367035937476264261048038,
    phi_oneHundredFiftyFiveEW_183251367035937476264261048039, phi_oneHundredFiftyFiveEW_183251367035937476264261048040, phi_oneHundredFiftyFiveEW_183251367035937476264261048041,
    phi_oneHundredFiftyFiveEW_183251367035937476264261048042, phi_oneHundredFiftyFiveEW_183251367035937476264261048043, phi_oneHundredFiftyFiveEW_183251367035937476264261048044,
    phi_oneHundredFiftyFiveEW_183251367035937476264261048045, phi_oneHundredFiftyFiveEW_183251367035937476264261048046, phi_oneHundredFiftyFiveEW_183251367035937476264261048047,
    phi_oneHundredFiftyFiveEW_183251367035937476264261048048, phi_oneHundredFiftyFiveEW_183251367035937476264261048049, phi_oneHundredFiftyFiveEW_183251367035937476264261048050,
    phi_oneHundredFiftyFiveEW_183251367035937476264261048051, phi_oneHundredFiftyFiveEW_183251367035937476264261048052, phi_oneHundredFiftyFiveEW_183251367035937476264261048053,
    phi_oneHundredFiftyFiveEW_183251367035937476264261048054, phi_oneHundredFiftyFiveEW_183251367035937476264261048055, phi_oneHundredFiftyFiveEW_183251367035937476264261048056,
    phi_oneHundredFiftyFiveEW_183251367035937476264261048057, phi_oneHundredFiftyFiveEW_183251367035937476264261048058, phi_oneHundredFiftyFiveEW_183251367035937476264261048059,
    phi_oneHundredFiftyFiveEW_183251367035937476264261048060, phi_oneHundredFiftyFiveEW_183251367035937476264261048061, phi_oneHundredFiftyFiveEW_183251367035937476264261048062,
    phi_oneHundredFiftyFiveEW_183251367035937476264261048063, phi_oneHundredFiftyFiveEW_183251367035937476264261048064, phi_oneHundredFiftyFiveEW_183251367035937476264261048065,
    phi_oneHundredFiftyFiveEW_183251367035937476264261048066, phi_oneHundredFiftyFiveEW_183251367035937476264261048067, phi_oneHundredFiftyFiveEW_183251367035937476264261048068,
    phi_oneHundredFiftyFiveEW_183251367035937476264261048069, phi_oneHundredFiftyFiveEW_183251367035937476264261048070, phi_oneHundredFiftyFiveEW_183251367035937476264261048071,
    phi_oneHundredFiftyFiveEW_183251367035937476264261048072, phi_oneHundredFiftyFiveEW_183251367035937476264261048073, phi_oneHundredFiftyFiveEW_183251367035937476264261048074,
    phi_oneHundredFiftyFiveEW_183251367035937476264261048075, phi_oneHundredFiftyFiveEW_183251367035937476264261048076, phi_oneHundredFiftyFiveEW_183251367035937476264261048077,
    phi_oneHundredFiftyFiveEW_183251367035937476264261048078, phi_oneHundredFiftyFiveEW_183251367035937476264261048079, phi_oneHundredFiftyFiveEW_183251367035937476264261048080,
    phi_oneHundredFiftyFiveEW_183251367035937476264261048081, phi_oneHundredFiftyFiveEW_183251367035937476264261048082, phi_oneHundredFiftyFiveEW_183251367035937476264261048083,
    phi_oneHundredFiftyFiveEW_183251367035937476264261048084, phi_oneHundredFiftyFiveEW_183251367035937476264261048085, phi_oneHundredFiftyFiveEW_183251367035937476264261048086,
    phi_oneHundredFiftyFiveEW_183251367035937476264261048087, phi_oneHundredFiftyFiveEW_183251367035937476264261048088, phi_oneHundredFiftyFiveEW_183251367035937476264261048089,
    phi_oneHundredFiftyFiveEW_183251367035937476264261048090, phi_oneHundredFiftyFiveEW_183251367035937476264261048091, phi_oneHundredFiftyFiveEW_183251367035937476264261048092,
    phi_oneHundredFiftyFiveEW_183251367035937476264261048093, phi_oneHundredFiftyFiveEW_183251367035937476264261048094, phi_oneHundredFiftyFiveEW_183251367035937476264261048095,
    phi_oneHundredFiftyFiveEW_183251367035937476264261048096, phi_oneHundredFiftyFiveEW_183251367035937476264261048097, phi_oneHundredFiftyFiveEW_183251367035937476264261048098,
    phi_oneHundredFiftyFiveEW_183251367035937476264261048099, phi_oneHundredFiftyFiveEW_183251367035937476264261048100, phi_oneHundredFiftyFiveEW_183251367035937476264261048101]

end TotientTailPeriodKiller
end Erdos249257
