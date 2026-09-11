import Erdos249257.DiagonalPincerCertificatesT64

/- Kernel-checked off-diagonal certificate at a freely chosen position. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def oneHundredTwentyFiveDSFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem oneHundredTwentyFiveDSFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : oneHundredTwentyFiveDSFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [oneHundredTwentyFiveDSFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [oneHundredTwentyFiveDSFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then oneHundredTwentyFiveDSFastPow a n * oneHundredTwentyFiveDSFastPow a n * a else oneHundredTwentyFiveDSFastPow a n * oneHundredTwentyFiveDSFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_oneHundredTwentyFiveDS_2 : Nat.Prime 2 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_3 : Nat.Prime 3 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_5 : Nat.Prime 5 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_7 : Nat.Prime 7 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_11 : Nat.Prime 11 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_13 : Nat.Prime 13 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_17 : Nat.Prime 17 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_19 : Nat.Prime 19 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_23 : Nat.Prime 23 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_29 : Nat.Prime 29 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_31 : Nat.Prime 31 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_37 : Nat.Prime 37 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_41 : Nat.Prime 41 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_43 : Nat.Prime 43 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_47 : Nat.Prime 47 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_53 : Nat.Prime 53 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_59 : Nat.Prime 59 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_61 : Nat.Prime 61 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_67 : Nat.Prime 67 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_71 : Nat.Prime 71 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_73 : Nat.Prime 73 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_79 : Nat.Prime 79 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_83 : Nat.Prime 83 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_89 : Nat.Prime 89 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_97 : Nat.Prime 97 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_101 : Nat.Prime 101 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_103 : Nat.Prime 103 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_107 : Nat.Prime 107 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_109 : Nat.Prime 109 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_113 : Nat.Prime 113 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_127 : Nat.Prime 127 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_131 : Nat.Prime 131 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_137 : Nat.Prime 137 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_139 : Nat.Prime 139 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_149 : Nat.Prime 149 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_151 : Nat.Prime 151 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_157 : Nat.Prime 157 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_163 : Nat.Prime 163 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_173 : Nat.Prime 173 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_181 : Nat.Prime 181 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_191 : Nat.Prime 191 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_197 : Nat.Prime 197 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_199 : Nat.Prime 199 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_211 : Nat.Prime 211 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_223 : Nat.Prime 223 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_227 : Nat.Prime 227 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_229 : Nat.Prime 229 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_239 : Nat.Prime 239 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_257 : Nat.Prime 257 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_263 : Nat.Prime 263 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_269 : Nat.Prime 269 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_277 : Nat.Prime 277 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_281 : Nat.Prime 281 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_293 : Nat.Prime 293 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_307 : Nat.Prime 307 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_313 : Nat.Prime 313 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_317 : Nat.Prime 317 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_331 : Nat.Prime 331 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_347 : Nat.Prime 347 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_349 : Nat.Prime 349 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_353 : Nat.Prime 353 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_359 : Nat.Prime 359 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_373 : Nat.Prime 373 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_379 : Nat.Prime 379 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_383 : Nat.Prime 383 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_397 : Nat.Prime 397 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_401 : Nat.Prime 401 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_409 : Nat.Prime 409 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_421 : Nat.Prime 421 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_433 : Nat.Prime 433 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_449 : Nat.Prime 449 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_463 : Nat.Prime 463 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_509 : Nat.Prime 509 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_541 : Nat.Prime 541 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_547 : Nat.Prime 547 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_563 : Nat.Prime 563 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_577 : Nat.Prime 577 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_587 : Nat.Prime 587 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_593 : Nat.Prime 593 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_599 : Nat.Prime 599 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_601 : Nat.Prime 601 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_613 : Nat.Prime 613 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_631 : Nat.Prime 631 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_647 : Nat.Prime 647 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_653 : Nat.Prime 653 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_673 : Nat.Prime 673 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_677 : Nat.Prime 677 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_683 : Nat.Prime 683 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_727 : Nat.Prime 727 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_733 : Nat.Prime 733 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_761 : Nat.Prime 761 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_773 : Nat.Prime 773 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_787 : Nat.Prime 787 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_797 : Nat.Prime 797 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_821 : Nat.Prime 821 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_823 : Nat.Prime 823 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_853 : Nat.Prime 853 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_857 : Nat.Prime 857 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_863 : Nat.Prime 863 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_887 : Nat.Prime 887 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_911 : Nat.Prime 911 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_941 : Nat.Prime 941 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_967 : Nat.Prime 967 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_1013 : Nat.Prime 1013 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_1019 : Nat.Prime 1019 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_1049 : Nat.Prime 1049 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_1051 : Nat.Prime 1051 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_1091 : Nat.Prime 1091 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_1123 : Nat.Prime 1123 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_1153 : Nat.Prime 1153 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_1163 : Nat.Prime 1163 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_1181 : Nat.Prime 1181 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_1237 : Nat.Prime 1237 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_1249 : Nat.Prime 1249 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_1279 : Nat.Prime 1279 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_1291 : Nat.Prime 1291 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_1327 : Nat.Prime 1327 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_1423 : Nat.Prime 1423 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_1429 : Nat.Prime 1429 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_1453 : Nat.Prime 1453 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_1481 : Nat.Prime 1481 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_1567 : Nat.Prime 1567 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_1609 : Nat.Prime 1609 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_1619 : Nat.Prime 1619 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_1657 : Nat.Prime 1657 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_1663 : Nat.Prime 1663 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_1669 : Nat.Prime 1669 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_1699 : Nat.Prime 1699 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_1721 : Nat.Prime 1721 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_1733 : Nat.Prime 1733 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_1783 : Nat.Prime 1783 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_1787 : Nat.Prime 1787 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_1867 : Nat.Prime 1867 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_1871 : Nat.Prime 1871 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_1873 : Nat.Prime 1873 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_1949 : Nat.Prime 1949 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_1979 : Nat.Prime 1979 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_1987 : Nat.Prime 1987 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_2003 : Nat.Prime 2003 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_2063 : Nat.Prime 2063 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_2081 : Nat.Prime 2081 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_2083 : Nat.Prime 2083 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_2089 : Nat.Prime 2089 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_2099 : Nat.Prime 2099 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_2179 : Nat.Prime 2179 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_2203 : Nat.Prime 2203 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_2239 : Nat.Prime 2239 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_2251 : Nat.Prime 2251 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_2297 : Nat.Prime 2297 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_2311 : Nat.Prime 2311 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_2341 : Nat.Prime 2341 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_2347 : Nat.Prime 2347 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_2389 : Nat.Prime 2389 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_2411 : Nat.Prime 2411 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_2477 : Nat.Prime 2477 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_2579 : Nat.Prime 2579 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_2699 : Nat.Prime 2699 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_2713 : Nat.Prime 2713 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_2767 : Nat.Prime 2767 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_2791 : Nat.Prime 2791 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_2797 : Nat.Prime 2797 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_2843 : Nat.Prime 2843 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_2857 : Nat.Prime 2857 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_2887 : Nat.Prime 2887 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_2903 : Nat.Prime 2903 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_2957 : Nat.Prime 2957 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_3049 : Nat.Prime 3049 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_3167 : Nat.Prime 3167 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_3307 : Nat.Prime 3307 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_3319 : Nat.Prime 3319 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_3343 : Nat.Prime 3343 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_3467 : Nat.Prime 3467 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_3469 : Nat.Prime 3469 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_3583 : Nat.Prime 3583 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_3623 : Nat.Prime 3623 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_3863 : Nat.Prime 3863 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_4211 : Nat.Prime 4211 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_4253 : Nat.Prime 4253 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_4271 : Nat.Prime 4271 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_4273 : Nat.Prime 4273 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_4289 : Nat.Prime 4289 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_4481 : Nat.Prime 4481 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_4621 : Nat.Prime 4621 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_4889 : Nat.Prime 4889 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_4999 : Nat.Prime 4999 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_5167 : Nat.Prime 5167 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_5189 : Nat.Prime 5189 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_5197 : Nat.Prime 5197 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_5387 : Nat.Prime 5387 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_5557 : Nat.Prime 5557 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_5879 : Nat.Prime 5879 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_6317 : Nat.Prime 6317 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_6323 : Nat.Prime 6323 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_6491 : Nat.Prime 6491 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_7193 : Nat.Prime 7193 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_7349 : Nat.Prime 7349 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_7393 : Nat.Prime 7393 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_7477 : Nat.Prime 7477 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_7841 : Nat.Prime 7841 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_8167 : Nat.Prime 8167 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_8317 : Nat.Prime 8317 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_8369 : Nat.Prime 8369 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_8447 : Nat.Prime 8447 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_8713 : Nat.Prime 8713 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_8807 : Nat.Prime 8807 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_8863 : Nat.Prime 8863 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_9067 : Nat.Prime 9067 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_9281 : Nat.Prime 9281 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_9371 : Nat.Prime 9371 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_9907 : Nat.Prime 9907 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_10067 : Nat.Prime 10067 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_10391 : Nat.Prime 10391 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_10487 : Nat.Prime 10487 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_10651 : Nat.Prime 10651 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_11069 : Nat.Prime 11069 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_11087 : Nat.Prime 11087 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_11093 : Nat.Prime 11093 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_11551 : Nat.Prime 11551 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_11593 : Nat.Prime 11593 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_11597 : Nat.Prime 11597 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_11699 : Nat.Prime 11699 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_11789 : Nat.Prime 11789 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_12071 : Nat.Prime 12071 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_12163 : Nat.Prime 12163 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_12451 : Nat.Prime 12451 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_12539 : Nat.Prime 12539 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_13147 : Nat.Prime 13147 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_13151 : Nat.Prime 13151 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_13381 : Nat.Prime 13381 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_13711 : Nat.Prime 13711 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_14437 : Nat.Prime 14437 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_15269 : Nat.Prime 15269 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_15749 : Nat.Prime 15749 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_15809 : Nat.Prime 15809 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_16007 : Nat.Prime 16007 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_16217 : Nat.Prime 16217 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_16349 : Nat.Prime 16349 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_16381 : Nat.Prime 16381 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_16487 : Nat.Prime 16487 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_16763 : Nat.Prime 16763 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_16843 : Nat.Prime 16843 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_17203 : Nat.Prime 17203 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_18077 : Nat.Prime 18077 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_18217 : Nat.Prime 18217 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_18521 : Nat.Prime 18521 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_18979 : Nat.Prime 18979 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_19531 : Nat.Prime 19531 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_19717 : Nat.Prime 19717 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_19841 : Nat.Prime 19841 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_20477 : Nat.Prime 20477 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_20599 : Nat.Prime 20599 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_20753 : Nat.Prime 20753 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_21563 : Nat.Prime 21563 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_22247 : Nat.Prime 22247 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_24733 : Nat.Prime 24733 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_25657 : Nat.Prime 25657 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_26293 : Nat.Prime 26293 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_27299 : Nat.Prime 27299 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_28541 : Nat.Prime 28541 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_29473 : Nat.Prime 29473 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_30389 : Nat.Prime 30389 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_30983 : Nat.Prime 30983 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_31379 : Nat.Prime 31379 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_32069 : Nat.Prime 32069 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_33757 : Nat.Prime 33757 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_34183 : Nat.Prime 34183 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_34687 : Nat.Prime 34687 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_35069 : Nat.Prime 35069 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_35267 : Nat.Prime 35267 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_36457 : Nat.Prime 36457 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_36767 : Nat.Prime 36767 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_37057 : Nat.Prime 37057 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_37861 : Nat.Prime 37861 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_38351 : Nat.Prime 38351 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_38833 : Nat.Prime 38833 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_39043 : Nat.Prime 39043 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_39341 : Nat.Prime 39341 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_39769 : Nat.Prime 39769 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_40151 : Nat.Prime 40151 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_40241 : Nat.Prime 40241 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_42457 : Nat.Prime 42457 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_46477 : Nat.Prime 46477 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_47569 : Nat.Prime 47569 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_48239 : Nat.Prime 48239 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_49549 : Nat.Prime 49549 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_50411 : Nat.Prime 50411 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_50767 : Nat.Prime 50767 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_52457 : Nat.Prime 52457 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_52541 : Nat.Prime 52541 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_53017 : Nat.Prime 53017 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_55339 : Nat.Prime 55339 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_56237 : Nat.Prime 56237 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_56809 : Nat.Prime 56809 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_57241 : Nat.Prime 57241 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_57503 : Nat.Prime 57503 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_59333 : Nat.Prime 59333 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_60127 : Nat.Prime 60127 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_60257 : Nat.Prime 60257 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_62467 : Nat.Prime 62467 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_63907 : Nat.Prime 63907 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_65099 : Nat.Prime 65099 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_65293 : Nat.Prime 65293 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_65981 : Nat.Prime 65981 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_72139 : Nat.Prime 72139 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_75767 : Nat.Prime 75767 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_76873 : Nat.Prime 76873 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_77041 : Nat.Prime 77041 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_83003 : Nat.Prime 83003 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_88499 : Nat.Prime 88499 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_90403 : Nat.Prime 90403 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_91457 : Nat.Prime 91457 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_98807 : Nat.Prime 98807 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_105277 : Nat.Prime 105277 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_106753 : Nat.Prime 106753 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_115883 : Nat.Prime 115883 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_122219 : Nat.Prime 122219 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_123457 : Nat.Prime 123457 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_131849 : Nat.Prime 131849 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_133831 : Nat.Prime 133831 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_144779 : Nat.Prime 144779 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_151939 : Nat.Prime 151939 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_152219 : Nat.Prime 152219 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_154723 : Nat.Prime 154723 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_154991 : Nat.Prime 154991 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_160813 : Nat.Prime 160813 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_169097 : Nat.Prime 169097 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_171091 : Nat.Prime 171091 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_171401 : Nat.Prime 171401 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_173807 : Nat.Prime 173807 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_178537 : Nat.Prime 178537 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_182579 : Nat.Prime 182579 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_185153 : Nat.Prime 185153 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_196817 : Nat.Prime 196817 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_198571 : Nat.Prime 198571 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_200201 : Nat.Prime 200201 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_205211 : Nat.Prime 205211 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_205421 : Nat.Prime 205421 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_220411 : Nat.Prime 220411 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_224603 : Nat.Prime 224603 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_225941 : Nat.Prime 225941 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_228457 : Nat.Prime 228457 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_228469 : Nat.Prime 228469 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_229223 : Nat.Prime 229223 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_236017 : Nat.Prime 236017 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_236917 : Nat.Prime 236917 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_251917 : Nat.Prime 251917 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_253543 : Nat.Prime 253543 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_276079 : Nat.Prime 276079 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_332569 : Nat.Prime 332569 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_335633 : Nat.Prime 335633 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_351031 : Nat.Prime 351031 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_362357 : Nat.Prime 362357 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_369731 : Nat.Prime 369731 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_401311 : Nat.Prime 401311 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_406313 : Nat.Prime 406313 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_411127 : Nat.Prime 411127 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_424129 : Nat.Prime 424129 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_442139 : Nat.Prime 442139 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_460531 : Nat.Prime 460531 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_481769 : Nat.Prime 481769 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_495569 : Nat.Prime 495569 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_508187 : Nat.Prime 508187 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_540301 : Nat.Prime 540301 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_572963 : Nat.Prime 572963 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_588827 : Nat.Prime 588827 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_594179 : Nat.Prime 594179 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_597593 : Nat.Prime 597593 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_607213 : Nat.Prime 607213 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_680249 : Nat.Prime 680249 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_700643 : Nat.Prime 700643 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_702239 : Nat.Prime 702239 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_743173 : Nat.Prime 743173 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_744859 : Nat.Prime 744859 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_754427 : Nat.Prime 754427 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_771643 : Nat.Prime 771643 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_772333 : Nat.Prime 772333 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_860569 : Nat.Prime 860569 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_1005971 : Nat.Prime 1005971 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_1059833 : Nat.Prime 1059833 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_1117033 : Nat.Prime 1117033 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_1149191 : Nat.Prime 1149191 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_1166723 : Nat.Prime 1166723 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_1210127 : Nat.Prime 1210127 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_1327561 : Nat.Prime 1327561 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_1345241 : Nat.Prime 1345241 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_1400327 : Nat.Prime 1400327 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_1417261 : Nat.Prime 1417261 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_1419233 : Nat.Prime 1419233 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_1463873 : Nat.Prime 1463873 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_1475563 : Nat.Prime 1475563 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_1599331 : Nat.Prime 1599331 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_1777411 : Nat.Prime 1777411 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_1893799 : Nat.Prime 1893799 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_1898591 : Nat.Prime 1898591 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_1910417 : Nat.Prime 1910417 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_1945483 : Nat.Prime 1945483 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_1982567 : Nat.Prime 1982567 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_1996217 : Nat.Prime 1996217 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_2046553 : Nat.Prime 2046553 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_2166119 : Nat.Prime 2166119 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_2347153 : Nat.Prime 2347153 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_2424341 : Nat.Prime 2424341 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_2441431 : Nat.Prime 2441431 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_2481629 : Nat.Prime 2481629 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_2508769 : Nat.Prime 2508769 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_2777531 : Nat.Prime 2777531 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_2807741 : Nat.Prime 2807741 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_3157171 : Nat.Prime 3157171 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_3333749 : Nat.Prime 3333749 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_3404827 : Nat.Prime 3404827 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_3433231 : Nat.Prime 3433231 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_3445873 : Nat.Prime 3445873 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_3479381 : Nat.Prime 3479381 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_3591073 : Nat.Prime 3591073 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_3599009 : Nat.Prime 3599009 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_4181393 : Nat.Prime 4181393 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_4243511 : Nat.Prime 4243511 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_4303099 : Nat.Prime 4303099 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_4345031 : Nat.Prime 4345031 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_4628321 : Nat.Prime 4628321 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_4635437 : Nat.Prime 4635437 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_4674151 : Nat.Prime 4674151 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_5216921 : Nat.Prime 5216921 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_5469559 : Nat.Prime 5469559 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_6380281 : Nat.Prime 6380281 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_6395869 : Nat.Prime 6395869 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_6496339 : Nat.Prime 6496339 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_6621991 : Nat.Prime 6621991 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_6697657 : Nat.Prime 6697657 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_6703889 : Nat.Prime 6703889 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_6932297 : Nat.Prime 6932297 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_7695671 : Nat.Prime 7695671 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_8223667 : Nat.Prime 8223667 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_8552471 : Nat.Prime 8552471 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_9128653 : Nat.Prime 9128653 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_9298811 : Nat.Prime 9298811 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_9421309 : Nat.Prime 9421309 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_9540991 : Nat.Prime 9540991 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_10556981 : Nat.Prime 10556981 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_10766489 : Nat.Prime 10766489 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_10820141 : Nat.Prime 10820141 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_10861121 : Nat.Prime 10861121 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_12844297 : Nat.Prime 12844297 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_13617913 : Nat.Prime 13617913 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_14483401 : Nat.Prime 14483401 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_16442347 : Nat.Prime 16442347 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_17802263 : Nat.Prime 17802263 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_19714811 : Nat.Prime 19714811 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_21989953 : Nat.Prime 21989953 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_22422131 : Nat.Prime 22422131 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_22998923 : Nat.Prime 22998923 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_24681493 : Nat.Prime 24681493 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_25308187 : Nat.Prime 25308187 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_25709711 : Nat.Prime 25709711 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_26240419 : Nat.Prime 26240419 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_29293681 : Nat.Prime 29293681 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_29533583 : Nat.Prime 29533583 := by norm_num

private theorem prime_oneHundredTwentyFiveDS_33184579 : Nat.Prime 33184579 := by
  apply lucas_primality 33184579 (2 : ZMod 33184579)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (17, 1), (46477, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (17, 1), (46477, 1)] : List FactorBlock).map factorBlockValue).prod) = 33184579 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_7
      · exact prime_oneHundredTwentyFiveDS_17
      · exact prime_oneHundredTwentyFiveDS_46477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 33184579) ^ 16592289 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 33184579) ^ 11061526 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 33184579) ^ 4740654 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 33184579) ^ 1952034 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 33184579) ^ 714 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_33521843 : Nat.Prime 33521843 := by
  apply lucas_primality 33521843 (2 : ZMod 33521843)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (67, 1), (97, 1), (2579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (67, 1), (97, 1), (2579, 1)] : List FactorBlock).map factorBlockValue).prod) = 33521843 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_67
      · exact prime_oneHundredTwentyFiveDS_97
      · exact prime_oneHundredTwentyFiveDS_2579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 33521843) ^ 16760921 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 33521843) ^ 500326 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 33521843) ^ 345586 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 33521843) ^ 12998 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_34648651 : Nat.Prime 34648651 := by
  apply lucas_primality 34648651 (2 : ZMod 34648651)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (37, 1), (2081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (37, 1), (2081, 1)] : List FactorBlock).map factorBlockValue).prod) = 34648651 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_5
      · exact prime_oneHundredTwentyFiveDS_37
      · exact prime_oneHundredTwentyFiveDS_2081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 34648651) ^ 17324325 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 34648651) ^ 11549550 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 34648651) ^ 6929730 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 34648651) ^ 936450 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 34648651) ^ 16650 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_36402757 : Nat.Prime 36402757 := by
  apply lucas_primality 36402757 (2 : ZMod 36402757)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (229, 1), (1019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (229, 1), (1019, 1)] : List FactorBlock).map factorBlockValue).prod) = 36402757 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_13
      · exact prime_oneHundredTwentyFiveDS_229
      · exact prime_oneHundredTwentyFiveDS_1019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 36402757) ^ 18201378 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 36402757) ^ 12134252 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 36402757) ^ 2800212 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 36402757) ^ 158964 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 36402757) ^ 35724 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_38226899 : Nat.Prime 38226899 := by
  apply lucas_primality 38226899 (2 : ZMod 38226899)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (1005971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (1005971, 1)] : List FactorBlock).map factorBlockValue).prod) = 38226899 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_19
      · exact prime_oneHundredTwentyFiveDS_1005971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 38226899) ^ 19113449 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 38226899) ^ 2011942 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 38226899) ^ 38 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_39429623 : Nat.Prime 39429623 := by
  apply lucas_primality 39429623 (5 : ZMod 39429623)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19714811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19714811, 1)] : List FactorBlock).map factorBlockValue).prod) = 39429623 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_19714811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 39429623) ^ 19714811 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 39429623) ^ 2 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_40184357 : Nat.Prime 40184357 := by
  apply lucas_primality 40184357 (2 : ZMod 40184357)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1153, 1), (8713, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1153, 1), (8713, 1)] : List FactorBlock).map factorBlockValue).prod) = 40184357 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_1153
      · exact prime_oneHundredTwentyFiveDS_8713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 40184357) ^ 20092178 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 40184357) ^ 34852 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 40184357) ^ 4612 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_43092877 : Nat.Prime 43092877 := by
  apply lucas_primality 43092877 (2 : ZMod 43092877)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (3591073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (3591073, 1)] : List FactorBlock).map factorBlockValue).prod) = 43092877 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_3591073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 43092877) ^ 21546438 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 43092877) ^ 14364292 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 43092877) ^ 12 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_44749589 : Nat.Prime 44749589 := by
  apply lucas_primality 44749589 (2 : ZMod 44749589)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (860569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (860569, 1)] : List FactorBlock).map factorBlockValue).prod) = 44749589 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_13
      · exact prime_oneHundredTwentyFiveDS_860569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 44749589) ^ 22374794 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 44749589) ^ 3442276 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 44749589) ^ 52 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_46174027 : Nat.Prime 46174027 := by
  apply lucas_primality 46174027 (2 : ZMod 46174027)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7695671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7695671, 1)] : List FactorBlock).map factorBlockValue).prod) = 46174027 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_7695671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 46174027) ^ 23087013 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 46174027) ^ 15391342 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 46174027) ^ 6 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_46484761 : Nat.Prime 46484761 := by
  apply lucas_primality 46484761 (26 : ZMod 46484761)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (7, 1), (55339, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (7, 1), (55339, 1)] : List FactorBlock).map factorBlockValue).prod) = 46484761 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_5
      · exact prime_oneHundredTwentyFiveDS_7
      · exact prime_oneHundredTwentyFiveDS_55339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (26 : ZMod 46484761) ^ 23242380 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (26 : ZMod 46484761) ^ 15494920 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (26 : ZMod 46484761) ^ 9296952 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (26 : ZMod 46484761) ^ 6640680 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (26 : ZMod 46484761) ^ 840 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_46771393 : Nat.Prime 46771393 := by
  apply lucas_primality 46771393 (5 : ZMod 46771393)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (47, 1), (71, 1), (73, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (47, 1), (71, 1), (73, 1)] : List FactorBlock).map factorBlockValue).prod) = 46771393 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_47
      · exact prime_oneHundredTwentyFiveDS_71
      · exact prime_oneHundredTwentyFiveDS_73
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 46771393) ^ 23385696 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 46771393) ^ 15590464 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 46771393) ^ 995136 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 46771393) ^ 658752 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 46771393) ^ 640704 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_48627091 : Nat.Prime 48627091 := by
  apply lucas_primality 48627091 (7 : ZMod 48627091)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (540301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (540301, 1)] : List FactorBlock).map factorBlockValue).prod) = 48627091 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_5
      · exact prime_oneHundredTwentyFiveDS_540301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 48627091) ^ 24313545 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (7 : ZMod 48627091) ^ 16209030 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (7 : ZMod 48627091) ^ 9725418 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (7 : ZMod 48627091) ^ 90 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_49613561 : Nat.Prime 49613561 := by
  apply lucas_primality 49613561 (6 : ZMod 49613561)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (19, 1), (97, 1), (673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (19, 1), (97, 1), (673, 1)] : List FactorBlock).map factorBlockValue).prod) = 49613561 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_5
      · exact prime_oneHundredTwentyFiveDS_19
      · exact prime_oneHundredTwentyFiveDS_97
      · exact prime_oneHundredTwentyFiveDS_673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 49613561) ^ 24806780 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (6 : ZMod 49613561) ^ 9922712 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (6 : ZMod 49613561) ^ 2611240 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (6 : ZMod 49613561) ^ 511480 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (6 : ZMod 49613561) ^ 73720 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_49995559 : Nat.Prime 49995559 := by
  apply lucas_primality 49995559 (3 : ZMod 49995559)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (2777531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (2777531, 1)] : List FactorBlock).map factorBlockValue).prod) = 49995559 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_2777531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 49995559) ^ 24997779 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 49995559) ^ 16665186 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 49995559) ^ 18 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_50027641 : Nat.Prime 50027641 := by
  apply lucas_primality 50027641 (14 : ZMod 50027641)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (13, 1), (32069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (13, 1), (32069, 1)] : List FactorBlock).map factorBlockValue).prod) = 50027641 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_5
      · exact prime_oneHundredTwentyFiveDS_13
      · exact prime_oneHundredTwentyFiveDS_32069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 50027641) ^ 25013820 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (14 : ZMod 50027641) ^ 16675880 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (14 : ZMod 50027641) ^ 10005528 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (14 : ZMod 50027641) ^ 3848280 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (14 : ZMod 50027641) ^ 1560 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_52591997 : Nat.Prime 52591997 := by
  apply lucas_primality 52591997 (2 : ZMod 52591997)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (31, 1), (424129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (31, 1), (424129, 1)] : List FactorBlock).map factorBlockValue).prod) = 52591997 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_31
      · exact prime_oneHundredTwentyFiveDS_424129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 52591997) ^ 26295998 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 52591997) ^ 1696516 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 52591997) ^ 124 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_52864081 : Nat.Prime 52864081 := by
  apply lucas_primality 52864081 (17 : ZMod 52864081)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (19, 1), (11593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (19, 1), (11593, 1)] : List FactorBlock).map factorBlockValue).prod) = 52864081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_5
      · exact prime_oneHundredTwentyFiveDS_19
      · exact prime_oneHundredTwentyFiveDS_11593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 52864081) ^ 26432040 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (17 : ZMod 52864081) ^ 17621360 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (17 : ZMod 52864081) ^ 10572816 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (17 : ZMod 52864081) ^ 2782320 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (17 : ZMod 52864081) ^ 4560 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_54771919 : Nat.Prime 54771919 := by
  apply lucas_primality 54771919 (3 : ZMod 54771919)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (9128653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (9128653, 1)] : List FactorBlock).map factorBlockValue).prod) = 54771919 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_9128653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 54771919) ^ 27385959 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 54771919) ^ 18257306 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 54771919) ^ 6 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_55270627 : Nat.Prime 55270627 := by
  apply lucas_primality 55270627 (5 : ZMod 55270627)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (53, 1), (173807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (53, 1), (173807, 1)] : List FactorBlock).map factorBlockValue).prod) = 55270627 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_53
      · exact prime_oneHundredTwentyFiveDS_173807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 55270627) ^ 27635313 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 55270627) ^ 18423542 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 55270627) ^ 1042842 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 55270627) ^ 318 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_56957731 : Nat.Prime 56957731 := by
  apply lucas_primality 56957731 (2 : ZMod 56957731)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (1898591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (1898591, 1)] : List FactorBlock).map factorBlockValue).prod) = 56957731 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_5
      · exact prime_oneHundredTwentyFiveDS_1898591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 56957731) ^ 28478865 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 56957731) ^ 18985910 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 56957731) ^ 11391546 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 56957731) ^ 30 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_59067167 : Nat.Prime 59067167 := by
  apply lucas_primality 59067167 (5 : ZMod 59067167)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29533583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29533583, 1)] : List FactorBlock).map factorBlockValue).prod) = 59067167 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_29533583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 59067167) ^ 29533583 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 59067167) ^ 2 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_59869031 : Nat.Prime 59869031 := by
  apply lucas_primality 59869031 (17 : ZMod 59869031)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (460531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (460531, 1)] : List FactorBlock).map factorBlockValue).prod) = 59869031 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_5
      · exact prime_oneHundredTwentyFiveDS_13
      · exact prime_oneHundredTwentyFiveDS_460531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 59869031) ^ 29934515 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (17 : ZMod 59869031) ^ 11973806 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (17 : ZMod 59869031) ^ 4605310 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (17 : ZMod 59869031) ^ 130 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_61931869 : Nat.Prime 61931869 := by
  apply lucas_primality 61931869 (7 : ZMod 61931869)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (43, 1), (6317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (43, 1), (6317, 1)] : List FactorBlock).map factorBlockValue).prod) = 61931869 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_19
      · exact prime_oneHundredTwentyFiveDS_43
      · exact prime_oneHundredTwentyFiveDS_6317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 61931869) ^ 30965934 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (7 : ZMod 61931869) ^ 20643956 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (7 : ZMod 61931869) ^ 3259572 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (7 : ZMod 61931869) ^ 1440276 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (7 : ZMod 61931869) ^ 9804 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_68802511 : Nat.Prime 68802511 := by
  apply lucas_primality 68802511 (6 : ZMod 68802511)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (41, 1), (61, 1), (131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (41, 1), (61, 1), (131, 1)] : List FactorBlock).map factorBlockValue).prod) = 68802511 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_5
      · exact prime_oneHundredTwentyFiveDS_7
      · exact prime_oneHundredTwentyFiveDS_41
      · exact prime_oneHundredTwentyFiveDS_61
      · exact prime_oneHundredTwentyFiveDS_131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 68802511) ^ 34401255 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (6 : ZMod 68802511) ^ 22934170 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (6 : ZMod 68802511) ^ 13760502 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (6 : ZMod 68802511) ^ 9828930 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (6 : ZMod 68802511) ^ 1678110 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (6 : ZMod 68802511) ^ 1127910 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (6 : ZMod 68802511) ^ 525210 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_76408531 : Nat.Prime 76408531 := by
  apply lucas_primality 76408531 (2 : ZMod 76408531)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (23, 1), (10067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (23, 1), (10067, 1)] : List FactorBlock).map factorBlockValue).prod) = 76408531 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_5
      · exact prime_oneHundredTwentyFiveDS_11
      · exact prime_oneHundredTwentyFiveDS_23
      · exact prime_oneHundredTwentyFiveDS_10067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 76408531) ^ 38204265 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 76408531) ^ 25469510 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 76408531) ^ 15281706 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 76408531) ^ 6946230 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 76408531) ^ 3322110 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 76408531) ^ 7590 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_82829821 : Nat.Prime 82829821 := by
  apply lucas_primality 82829821 (2 : ZMod 82829821)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (601, 1), (2297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (601, 1), (2297, 1)] : List FactorBlock).map factorBlockValue).prod) = 82829821 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_5
      · exact prime_oneHundredTwentyFiveDS_601
      · exact prime_oneHundredTwentyFiveDS_2297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 82829821) ^ 41414910 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 82829821) ^ 27609940 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 82829821) ^ 16565964 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 82829821) ^ 137820 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 82829821) ^ 36060 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_86670719 : Nat.Prime 86670719 := by
  apply lucas_primality 86670719 (7 : ZMod 86670719)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (911, 1), (47569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (911, 1), (47569, 1)] : List FactorBlock).map factorBlockValue).prod) = 86670719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_911
      · exact prime_oneHundredTwentyFiveDS_47569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 86670719) ^ 43335359 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (7 : ZMod 86670719) ^ 95138 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (7 : ZMod 86670719) ^ 1822 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_88109039 : Nat.Prime 88109039 := by
  apply lucas_primality 88109039 (7 : ZMod 88109039)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (113, 1), (197, 1), (1979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (113, 1), (197, 1), (1979, 1)] : List FactorBlock).map factorBlockValue).prod) = 88109039 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_113
      · exact prime_oneHundredTwentyFiveDS_197
      · exact prime_oneHundredTwentyFiveDS_1979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 88109039) ^ 44054519 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (7 : ZMod 88109039) ^ 779726 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (7 : ZMod 88109039) ^ 447254 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (7 : ZMod 88109039) ^ 44522 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_88812211 : Nat.Prime 88812211 := by
  apply lucas_primality 88812211 (3 : ZMod 88812211)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (29, 1), (31, 1), (37, 1), (89, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (29, 1), (31, 1), (37, 1), (89, 1)] : List FactorBlock).map factorBlockValue).prod) = 88812211 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_5
      · exact prime_oneHundredTwentyFiveDS_29
      · exact prime_oneHundredTwentyFiveDS_31
      · exact prime_oneHundredTwentyFiveDS_37
      · exact prime_oneHundredTwentyFiveDS_89
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 88812211) ^ 44406105 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 88812211) ^ 29604070 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 88812211) ^ 17762442 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 88812211) ^ 3062490 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 88812211) ^ 2864910 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 88812211) ^ 2400330 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 88812211) ^ 997890 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_90131191 : Nat.Prime 90131191 := by
  apply lucas_primality 90131191 (13 : ZMod 90131191)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (89, 1), (33757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (89, 1), (33757, 1)] : List FactorBlock).map factorBlockValue).prod) = 90131191 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_5
      · exact prime_oneHundredTwentyFiveDS_89
      · exact prime_oneHundredTwentyFiveDS_33757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 90131191) ^ 45065595 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (13 : ZMod 90131191) ^ 30043730 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (13 : ZMod 90131191) ^ 18026238 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (13 : ZMod 90131191) ^ 1012710 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (13 : ZMod 90131191) ^ 2670 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_94647361 : Nat.Prime 94647361 := by
  apply lucas_primality 94647361 (31 : ZMod 94647361)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (5, 1), (19, 1), (5189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (5, 1), (19, 1), (5189, 1)] : List FactorBlock).map factorBlockValue).prod) = 94647361 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_5
      · exact prime_oneHundredTwentyFiveDS_19
      · exact prime_oneHundredTwentyFiveDS_5189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (31 : ZMod 94647361) ^ 47323680 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (31 : ZMod 94647361) ^ 31549120 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (31 : ZMod 94647361) ^ 18929472 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (31 : ZMod 94647361) ^ 4981440 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (31 : ZMod 94647361) ^ 18240 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_96773623 : Nat.Prime 96773623 := by
  apply lucas_primality 96773623 (3 : ZMod 96773623)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 2), (17, 1), (7841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 2), (17, 1), (7841, 1)] : List FactorBlock).map factorBlockValue).prod) = 96773623 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_11
      · exact prime_oneHundredTwentyFiveDS_17
      · exact prime_oneHundredTwentyFiveDS_7841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 96773623) ^ 48386811 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 96773623) ^ 32257874 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 96773623) ^ 8797602 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 96773623) ^ 5692566 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 96773623) ^ 12342 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_102406289 : Nat.Prime 102406289 := by
  apply lucas_primality 102406289 (3 : ZMod 102406289)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (683, 1), (9371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (683, 1), (9371, 1)] : List FactorBlock).map factorBlockValue).prod) = 102406289 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_683
      · exact prime_oneHundredTwentyFiveDS_9371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 102406289) ^ 51203144 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 102406289) ^ 149936 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 102406289) ^ 10928 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_125356541 : Nat.Prime 125356541 := by
  apply lucas_primality 125356541 (3 : ZMod 125356541)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (109, 1), (57503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (109, 1), (57503, 1)] : List FactorBlock).map factorBlockValue).prod) = 125356541 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_5
      · exact prime_oneHundredTwentyFiveDS_109
      · exact prime_oneHundredTwentyFiveDS_57503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 125356541) ^ 62678270 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 125356541) ^ 25071308 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 125356541) ^ 1150060 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 125356541) ^ 2180 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_134341979 : Nat.Prime 134341979 := by
  apply lucas_primality 134341979 (2 : ZMod 134341979)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (263, 1), (8807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (263, 1), (8807, 1)] : List FactorBlock).map factorBlockValue).prod) = 134341979 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_29
      · exact prime_oneHundredTwentyFiveDS_263
      · exact prime_oneHundredTwentyFiveDS_8807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 134341979) ^ 67170989 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 134341979) ^ 4632482 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 134341979) ^ 510806 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 134341979) ^ 15254 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_136360163 : Nat.Prime 136360163 := by
  apply lucas_primality 136360163 (6 : ZMod 136360163)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (79, 1), (50767, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (79, 1), (50767, 1)] : List FactorBlock).map factorBlockValue).prod) = 136360163 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_17
      · exact prime_oneHundredTwentyFiveDS_79
      · exact prime_oneHundredTwentyFiveDS_50767
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 136360163) ^ 68180081 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (6 : ZMod 136360163) ^ 8021186 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (6 : ZMod 136360163) ^ 1726078 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (6 : ZMod 136360163) ^ 2686 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_137009569 : Nat.Prime 137009569 := by
  apply lucas_primality 137009569 (13 : ZMod 137009569)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (887, 1), (1609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (887, 1), (1609, 1)] : List FactorBlock).map factorBlockValue).prod) = 137009569 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_887
      · exact prime_oneHundredTwentyFiveDS_1609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 137009569) ^ 68504784 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (13 : ZMod 137009569) ^ 45669856 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (13 : ZMod 137009569) ^ 154464 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (13 : ZMod 137009569) ^ 85152 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_143385917 : Nat.Prime 143385917 := by
  apply lucas_primality 143385917 (2 : ZMod 143385917)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (631, 1), (56809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (631, 1), (56809, 1)] : List FactorBlock).map factorBlockValue).prod) = 143385917 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_631
      · exact prime_oneHundredTwentyFiveDS_56809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 143385917) ^ 71692958 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 143385917) ^ 227236 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 143385917) ^ 2524 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_146249921 : Nat.Prime 146249921 := by
  apply lucas_primality 146249921 (3 : ZMod 146249921)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (5, 1), (269, 1), (1699, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (5, 1), (269, 1), (1699, 1)] : List FactorBlock).map factorBlockValue).prod) = 146249921 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_5
      · exact prime_oneHundredTwentyFiveDS_269
      · exact prime_oneHundredTwentyFiveDS_1699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 146249921) ^ 73124960 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 146249921) ^ 29249984 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 146249921) ^ 543680 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 146249921) ^ 86080 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_148088959 : Nat.Prime 148088959 := by
  apply lucas_primality 148088959 (3 : ZMod 148088959)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (24681493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (24681493, 1)] : List FactorBlock).map factorBlockValue).prod) = 148088959 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_24681493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 148088959) ^ 74044479 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 148088959) ^ 49362986 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 148088959) ^ 6 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_150071237 : Nat.Prime 150071237 := by
  apply lucas_primality 150071237 (3 : ZMod 150071237)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (541, 1), (9907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (541, 1), (9907, 1)] : List FactorBlock).map factorBlockValue).prod) = 150071237 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_7
      · exact prime_oneHundredTwentyFiveDS_541
      · exact prime_oneHundredTwentyFiveDS_9907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 150071237) ^ 75035618 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 150071237) ^ 21438748 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 150071237) ^ 277396 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 150071237) ^ 15148 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_160292807 : Nat.Prime 160292807 := by
  apply lucas_primality 160292807 (5 : ZMod 160292807)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (2166119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (2166119, 1)] : List FactorBlock).map factorBlockValue).prod) = 160292807 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_37
      · exact prime_oneHundredTwentyFiveDS_2166119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 160292807) ^ 80146403 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 160292807) ^ 4332238 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 160292807) ^ 74 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_204812579 : Nat.Prime 204812579 := by
  apply lucas_primality 204812579 (2 : ZMod 204812579)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (102406289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (102406289, 1)] : List FactorBlock).map factorBlockValue).prod) = 204812579 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_102406289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 204812579) ^ 102406289 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 204812579) ^ 2 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_236577739 : Nat.Prime 236577739 := by
  apply lucas_primality 236577739 (3 : ZMod 236577739)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (39429623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (39429623, 1)] : List FactorBlock).map factorBlockValue).prod) = 236577739 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_39429623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 236577739) ^ 118288869 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 236577739) ^ 78859246 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 236577739) ^ 6 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_244033831 : Nat.Prime 244033831 := by
  apply lucas_primality 244033831 (6 : ZMod 244033831)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (107, 1), (8447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (107, 1), (8447, 1)] : List FactorBlock).map factorBlockValue).prod) = 244033831 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_5
      · exact prime_oneHundredTwentyFiveDS_107
      · exact prime_oneHundredTwentyFiveDS_8447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 244033831) ^ 122016915 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (6 : ZMod 244033831) ^ 81344610 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (6 : ZMod 244033831) ^ 48806766 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (6 : ZMod 244033831) ^ 2280690 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (6 : ZMod 244033831) ^ 28890 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_267097681 : Nat.Prime 267097681 := by
  apply lucas_primality 267097681 (13 : ZMod 267097681)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5, 1), (107, 1), (3467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5, 1), (107, 1), (3467, 1)] : List FactorBlock).map factorBlockValue).prod) = 267097681 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_5
      · exact prime_oneHundredTwentyFiveDS_107
      · exact prime_oneHundredTwentyFiveDS_3467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 267097681) ^ 133548840 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (13 : ZMod 267097681) ^ 89032560 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (13 : ZMod 267097681) ^ 53419536 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (13 : ZMod 267097681) ^ 2496240 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (13 : ZMod 267097681) ^ 77040 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_269705861 : Nat.Prime 269705861 := by
  apply lucas_primality 269705861 (10 : ZMod 269705861)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (1453, 1), (9281, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (1453, 1), (9281, 1)] : List FactorBlock).map factorBlockValue).prod) = 269705861 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_5
      · exact prime_oneHundredTwentyFiveDS_1453
      · exact prime_oneHundredTwentyFiveDS_9281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 269705861) ^ 134852930 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (10 : ZMod 269705861) ^ 53941172 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (10 : ZMod 269705861) ^ 185620 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (10 : ZMod 269705861) ^ 29060 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_308091257 : Nat.Prime 308091257 := by
  apply lucas_primality 308091257 (5 : ZMod 308091257)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (23, 1), (152219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (23, 1), (152219, 1)] : List FactorBlock).map factorBlockValue).prod) = 308091257 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_11
      · exact prime_oneHundredTwentyFiveDS_23
      · exact prime_oneHundredTwentyFiveDS_152219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 308091257) ^ 154045628 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 308091257) ^ 28008296 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 308091257) ^ 13395272 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 308091257) ^ 2024 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_327254021 : Nat.Prime 327254021 := by
  apply lucas_primality 327254021 (2 : ZMod 327254021)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (61, 1), (313, 1), (857, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (61, 1), (313, 1), (857, 1)] : List FactorBlock).map factorBlockValue).prod) = 327254021 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_5
      · exact prime_oneHundredTwentyFiveDS_61
      · exact prime_oneHundredTwentyFiveDS_313
      · exact prime_oneHundredTwentyFiveDS_857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 327254021) ^ 163627010 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 327254021) ^ 65450804 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 327254021) ^ 5364820 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 327254021) ^ 1045540 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 327254021) ^ 381860 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_330945607 : Nat.Prime 330945607 := by
  apply lucas_primality 330945607 (3 : ZMod 330945607)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (1163, 1), (15809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (1163, 1), (15809, 1)] : List FactorBlock).map factorBlockValue).prod) = 330945607 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_1163
      · exact prime_oneHundredTwentyFiveDS_15809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 330945607) ^ 165472803 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 330945607) ^ 110315202 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 330945607) ^ 284562 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 330945607) ^ 20934 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_348513211 : Nat.Prime 348513211 := by
  apply lucas_primality 348513211 (3 : ZMod 348513211)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (331, 1), (11699, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (331, 1), (11699, 1)] : List FactorBlock).map factorBlockValue).prod) = 348513211 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_5
      · exact prime_oneHundredTwentyFiveDS_331
      · exact prime_oneHundredTwentyFiveDS_11699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 348513211) ^ 174256605 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 348513211) ^ 116171070 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 348513211) ^ 69702642 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 348513211) ^ 1052910 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 348513211) ^ 29790 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_362051087 : Nat.Prime 362051087 := by
  apply lucas_primality 362051087 (5 : ZMod 362051087)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (12539, 1), (14437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (12539, 1), (14437, 1)] : List FactorBlock).map factorBlockValue).prod) = 362051087 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_12539
      · exact prime_oneHundredTwentyFiveDS_14437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 362051087) ^ 181025543 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 362051087) ^ 28874 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 362051087) ^ 25078 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_368167819 : Nat.Prime 368167819 := by
  apply lucas_primality 368167819 (2 : ZMod 368167819)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 1), (61, 1), (34687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 1), (61, 1), (34687, 1)] : List FactorBlock).map factorBlockValue).prod) = 368167819 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_29
      · exact prime_oneHundredTwentyFiveDS_61
      · exact prime_oneHundredTwentyFiveDS_34687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 368167819) ^ 184083909 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 368167819) ^ 122722606 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 368167819) ^ 12695442 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 368167819) ^ 6035538 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 368167819) ^ 10614 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_426966413 : Nat.Prime 426966413 := by
  apply lucas_primality 426966413 (2 : ZMod 426966413)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (421, 1), (253543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (421, 1), (253543, 1)] : List FactorBlock).map factorBlockValue).prod) = 426966413 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_421
      · exact prime_oneHundredTwentyFiveDS_253543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 426966413) ^ 213483206 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 426966413) ^ 1014172 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 426966413) ^ 1684 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_446511433 : Nat.Prime 446511433 := by
  apply lucas_primality 446511433 (10 : ZMod 446511433)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (53, 1), (351031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (53, 1), (351031, 1)] : List FactorBlock).map factorBlockValue).prod) = 446511433 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_53
      · exact prime_oneHundredTwentyFiveDS_351031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 446511433) ^ 223255716 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (10 : ZMod 446511433) ^ 148837144 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (10 : ZMod 446511433) ^ 8424744 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (10 : ZMod 446511433) ^ 1272 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_466546253 : Nat.Prime 466546253 := by
  apply lucas_primality 466546253 (2 : ZMod 466546253)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (47, 1), (2481629, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (47, 1), (2481629, 1)] : List FactorBlock).map factorBlockValue).prod) = 466546253 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_47
      · exact prime_oneHundredTwentyFiveDS_2481629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 466546253) ^ 233273126 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 466546253) ^ 9926516 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 466546253) ^ 188 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_527286259 : Nat.Prime 527286259 := by
  apply lucas_primality 527286259 (2 : ZMod 527286259)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (29293681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (29293681, 1)] : List FactorBlock).map factorBlockValue).prod) = 527286259 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_29293681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 527286259) ^ 263643129 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 527286259) ^ 175762086 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 527286259) ^ 18 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_578483509 : Nat.Prime 578483509 := by
  apply lucas_primality 578483509 (2 : ZMod 578483509)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (211, 1), (228469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (211, 1), (228469, 1)] : List FactorBlock).map factorBlockValue).prod) = 578483509 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_211
      · exact prime_oneHundredTwentyFiveDS_228469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 578483509) ^ 289241754 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 578483509) ^ 192827836 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 578483509) ^ 2741628 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 578483509) ^ 2532 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_714027719 : Nat.Prime 714027719 := by
  apply lucas_primality 714027719 (11 : ZMod 714027719)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) = 714027719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_17203
      · exact prime_oneHundredTwentyFiveDS_20753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 714027719) ^ 357013859 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 41506 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 34406 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_746315257 : Nat.Prime 746315257 := by
  apply lucas_primality 746315257 (5 : ZMod 746315257)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (47, 1), (463, 1), (1429, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (47, 1), (463, 1), (1429, 1)] : List FactorBlock).map factorBlockValue).prod) = 746315257 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_47
      · exact prime_oneHundredTwentyFiveDS_463
      · exact prime_oneHundredTwentyFiveDS_1429
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 746315257) ^ 373157628 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 746315257) ^ 248771752 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 746315257) ^ 15879048 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 746315257) ^ 1611912 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 746315257) ^ 522264 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_762435017 : Nat.Prime 762435017 := by
  apply lucas_primality 762435017 (3 : ZMod 762435017)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (41, 1), (139, 1), (2389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (41, 1), (139, 1), (2389, 1)] : List FactorBlock).map factorBlockValue).prod) = 762435017 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_7
      · exact prime_oneHundredTwentyFiveDS_41
      · exact prime_oneHundredTwentyFiveDS_139
      · exact prime_oneHundredTwentyFiveDS_2389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 762435017) ^ 381217508 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 762435017) ^ 108919288 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 762435017) ^ 18595976 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 762435017) ^ 5485144 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 762435017) ^ 319144 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_852045983 : Nat.Prime 852045983 := by
  apply lucas_primality 852045983 (5 : ZMod 852045983)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (223, 1), (1910417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (223, 1), (1910417, 1)] : List FactorBlock).map factorBlockValue).prod) = 852045983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_223
      · exact prime_oneHundredTwentyFiveDS_1910417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 852045983) ^ 426022991 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 852045983) ^ 3820834 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 852045983) ^ 446 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_946310957 : Nat.Prime 946310957 := by
  apply lucas_primality 946310957 (2 : ZMod 946310957)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (236577739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (236577739, 1)] : List FactorBlock).map factorBlockValue).prod) = 946310957 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_236577739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 946310957) ^ 473155478 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 946310957) ^ 4 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_946473611 : Nat.Prime 946473611 := by
  apply lucas_primality 946473611 (6 : ZMod 946473611)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (94647361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (94647361, 1)] : List FactorBlock).map factorBlockValue).prod) = 946473611 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_5
      · exact prime_oneHundredTwentyFiveDS_94647361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 946473611) ^ 473236805 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (6 : ZMod 946473611) ^ 189294722 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (6 : ZMod 946473611) ^ 10 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_948683023 : Nat.Prime 948683023 := by
  apply lucas_primality 948683023 (5 : ZMod 948683023)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (599, 1), (5387, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (599, 1), (5387, 1)] : List FactorBlock).map factorBlockValue).prod) = 948683023 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_7
      · exact prime_oneHundredTwentyFiveDS_599
      · exact prime_oneHundredTwentyFiveDS_5387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 948683023) ^ 474341511 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 948683023) ^ 316227674 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 948683023) ^ 135526146 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 948683023) ^ 1583778 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 948683023) ^ 176106 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_985457719 : Nat.Prime 985457719 := by
  apply lucas_primality 985457719 (7 : ZMod 985457719)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 2), (131, 1), (2843, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 2), (131, 1), (2843, 1)] : List FactorBlock).map factorBlockValue).prod) = 985457719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_7
      · exact prime_oneHundredTwentyFiveDS_131
      · exact prime_oneHundredTwentyFiveDS_2843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 985457719) ^ 492728859 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (7 : ZMod 985457719) ^ 328485906 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (7 : ZMod 985457719) ^ 140779674 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (7 : ZMod 985457719) ^ 7522578 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (7 : ZMod 985457719) ^ 346626 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_1009649983 : Nat.Prime 1009649983 := by
  apply lucas_primality 1009649983 (3 : ZMod 1009649983)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (199, 1), (76873, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (199, 1), (76873, 1)] : List FactorBlock).map factorBlockValue).prod) = 1009649983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_11
      · exact prime_oneHundredTwentyFiveDS_199
      · exact prime_oneHundredTwentyFiveDS_76873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1009649983) ^ 504824991 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1009649983) ^ 336549994 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1009649983) ^ 91786362 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1009649983) ^ 5073618 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1009649983) ^ 13134 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_1051839941 : Nat.Prime 1051839941 := by
  apply lucas_primality 1051839941 (2 : ZMod 1051839941)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (52591997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (52591997, 1)] : List FactorBlock).map factorBlockValue).prod) = 1051839941 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_5
      · exact prime_oneHundredTwentyFiveDS_52591997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1051839941) ^ 525919970 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1051839941) ^ 210367988 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1051839941) ^ 20 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_1111078159 : Nat.Prime 1111078159 := by
  apply lucas_primality 1111078159 (3 : ZMod 1111078159)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (97, 1), (83003, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (97, 1), (83003, 1)] : List FactorBlock).map factorBlockValue).prod) = 1111078159 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_23
      · exact prime_oneHundredTwentyFiveDS_97
      · exact prime_oneHundredTwentyFiveDS_83003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1111078159) ^ 555539079 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1111078159) ^ 370359386 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1111078159) ^ 48307746 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1111078159) ^ 11454414 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1111078159) ^ 13386 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_1152897883 : Nat.Prime 1152897883 := by
  apply lucas_primality 1152897883 (2 : ZMod 1152897883)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (6323, 1), (30389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (6323, 1), (30389, 1)] : List FactorBlock).map factorBlockValue).prod) = 1152897883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_6323
      · exact prime_oneHundredTwentyFiveDS_30389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1152897883) ^ 576448941 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1152897883) ^ 384299294 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1152897883) ^ 182334 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1152897883) ^ 37938 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_1418544643 : Nat.Prime 1418544643 := by
  apply lucas_primality 1418544643 (2 : ZMod 1418544643)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (71, 1), (144779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (71, 1), (144779, 1)] : List FactorBlock).map factorBlockValue).prod) = 1418544643 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_23
      · exact prime_oneHundredTwentyFiveDS_71
      · exact prime_oneHundredTwentyFiveDS_144779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1418544643) ^ 709272321 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1418544643) ^ 472848214 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1418544643) ^ 61675854 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1418544643) ^ 19979502 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1418544643) ^ 9798 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_1441801583 : Nat.Prime 1441801583 := by
  apply lucas_primality 1441801583 (5 : ZMod 1441801583)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (4999, 1), (11093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (4999, 1), (11093, 1)] : List FactorBlock).map factorBlockValue).prod) = 1441801583 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_13
      · exact prime_oneHundredTwentyFiveDS_4999
      · exact prime_oneHundredTwentyFiveDS_11093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1441801583) ^ 720900791 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 1441801583) ^ 110907814 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 1441801583) ^ 288418 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 1441801583) ^ 129974 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_1491991379 : Nat.Prime 1491991379 := by
  apply lucas_primality 1491991379 (2 : ZMod 1491991379)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (653, 1), (60127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (653, 1), (60127, 1)] : List FactorBlock).map factorBlockValue).prod) = 1491991379 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_19
      · exact prime_oneHundredTwentyFiveDS_653
      · exact prime_oneHundredTwentyFiveDS_60127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1491991379) ^ 745995689 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1491991379) ^ 78525862 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1491991379) ^ 2284826 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1491991379) ^ 24814 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_1498629871 : Nat.Prime 1498629871 := by
  apply lucas_primality 1498629871 (7 : ZMod 1498629871)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (37, 1), (67, 1), (2239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (37, 1), (67, 1), (2239, 1)] : List FactorBlock).map factorBlockValue).prod) = 1498629871 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_5
      · exact prime_oneHundredTwentyFiveDS_37
      · exact prime_oneHundredTwentyFiveDS_67
      · exact prime_oneHundredTwentyFiveDS_2239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1498629871) ^ 749314935 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (7 : ZMod 1498629871) ^ 499543290 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (7 : ZMod 1498629871) ^ 299725974 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (7 : ZMod 1498629871) ^ 40503510 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (7 : ZMod 1498629871) ^ 22367610 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (7 : ZMod 1498629871) ^ 669330 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_1535746343 : Nat.Prime 1535746343 := by
  apply lucas_primality 1535746343 (5 : ZMod 1535746343)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (59067167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (59067167, 1)] : List FactorBlock).map factorBlockValue).prod) = 1535746343 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_13
      · exact prime_oneHundredTwentyFiveDS_59067167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1535746343) ^ 767873171 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 1535746343) ^ 118134334 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 1535746343) ^ 26 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_1546739021 : Nat.Prime 1546739021 := by
  apply lucas_primality 1546739021 (2 : ZMod 1546739021)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (509, 1), (151939, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (509, 1), (151939, 1)] : List FactorBlock).map factorBlockValue).prod) = 1546739021 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_5
      · exact prime_oneHundredTwentyFiveDS_509
      · exact prime_oneHundredTwentyFiveDS_151939
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1546739021) ^ 773369510 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1546739021) ^ 309347804 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1546739021) ^ 3038780 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1546739021) ^ 10180 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_1704091967 : Nat.Prime 1704091967 := by
  apply lucas_primality 1704091967 (5 : ZMod 1704091967)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (852045983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (852045983, 1)] : List FactorBlock).map factorBlockValue).prod) = 1704091967 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_852045983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 1704091967) ^ 852045983 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 1704091967) ^ 2 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_1733414381 : Nat.Prime 1733414381 := by
  apply lucas_primality 1733414381 (2 : ZMod 1733414381)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (86670719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (86670719, 1)] : List FactorBlock).map factorBlockValue).prod) = 1733414381 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_5
      · exact prime_oneHundredTwentyFiveDS_86670719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1733414381) ^ 866707190 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1733414381) ^ 346682876 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1733414381) ^ 20 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_1735613543 : Nat.Prime 1735613543 := by
  apply lucas_primality 1735613543 (5 : ZMod 1735613543)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (2699, 1), (24733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (2699, 1), (24733, 1)] : List FactorBlock).map factorBlockValue).prod) = 1735613543 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_13
      · exact prime_oneHundredTwentyFiveDS_2699
      · exact prime_oneHundredTwentyFiveDS_24733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1735613543) ^ 867806771 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 1735613543) ^ 133508734 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 1735613543) ^ 643058 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 1735613543) ^ 70174 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_1834640921 : Nat.Prime 1834640921 := by
  apply lucas_primality 1834640921 (3 : ZMod 1834640921)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (7, 1), (29, 1), (225941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (7, 1), (29, 1), (225941, 1)] : List FactorBlock).map factorBlockValue).prod) = 1834640921 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_5
      · exact prime_oneHundredTwentyFiveDS_7
      · exact prime_oneHundredTwentyFiveDS_29
      · exact prime_oneHundredTwentyFiveDS_225941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1834640921) ^ 917320460 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1834640921) ^ 366928184 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1834640921) ^ 262091560 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1834640921) ^ 63263480 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1834640921) ^ 8120 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_2103679883 : Nat.Prime 2103679883 := by
  apply lucas_primality 2103679883 (2 : ZMod 2103679883)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1051839941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1051839941, 1)] : List FactorBlock).map factorBlockValue).prod) = 2103679883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_1051839941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 2103679883) ^ 1051839941 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 2103679883) ^ 2 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_2599006913 : Nat.Prime 2599006913 := by
  apply lucas_primality 2599006913 (3 : ZMod 2599006913)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (29, 1), (1400327, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (29, 1), (1400327, 1)] : List FactorBlock).map factorBlockValue).prod) = 2599006913 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_29
      · exact prime_oneHundredTwentyFiveDS_1400327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2599006913) ^ 1299503456 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 2599006913) ^ 89620928 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 2599006913) ^ 1856 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_2837014421 : Nat.Prime 2837014421 := by
  apply lucas_primality 2837014421 (2 : ZMod 2837014421)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (2179, 1), (65099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (2179, 1), (65099, 1)] : List FactorBlock).map factorBlockValue).prod) = 2837014421 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_5
      · exact prime_oneHundredTwentyFiveDS_2179
      · exact prime_oneHundredTwentyFiveDS_65099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2837014421) ^ 1418507210 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 2837014421) ^ 567402884 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 2837014421) ^ 1301980 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 2837014421) ^ 43580 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_2962549301 : Nat.Prime 2962549301 := by
  apply lucas_primality 2962549301 (2 : ZMod 2962549301)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (37, 1), (41, 1), (59, 1), (331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (37, 1), (41, 1), (59, 1), (331, 1)] : List FactorBlock).map factorBlockValue).prod) = 2962549301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_5
      · exact prime_oneHundredTwentyFiveDS_37
      · exact prime_oneHundredTwentyFiveDS_41
      · exact prime_oneHundredTwentyFiveDS_59
      · exact prime_oneHundredTwentyFiveDS_331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2962549301) ^ 1481274650 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 2962549301) ^ 592509860 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 2962549301) ^ 80068900 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 2962549301) ^ 72257300 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 2962549301) ^ 50212700 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 2962549301) ^ 8950300 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_3140331247 : Nat.Prime 3140331247 := by
  apply lucas_primality 3140331247 (3 : ZMod 3140331247)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (113, 2), (1051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (113, 2), (1051, 1)] : List FactorBlock).map factorBlockValue).prod) = 3140331247 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_13
      · exact prime_oneHundredTwentyFiveDS_113
      · exact prime_oneHundredTwentyFiveDS_1051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3140331247) ^ 1570165623 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 3140331247) ^ 1046777082 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 3140331247) ^ 241563942 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 3140331247) ^ 27790542 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 3140331247) ^ 2987946 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_3466828763 : Nat.Prime 3466828763 := by
  apply lucas_primality 3466828763 (2 : ZMod 3466828763)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1733414381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1733414381, 1)] : List FactorBlock).map factorBlockValue).prod) = 3466828763 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_1733414381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 3466828763) ^ 1733414381 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 3466828763) ^ 2 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_3566049547 : Nat.Prime 3566049547 := by
  apply lucas_primality 3566049547 (2 : ZMod 3566049547)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1481, 1), (401311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1481, 1), (401311, 1)] : List FactorBlock).map factorBlockValue).prod) = 3566049547 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_1481
      · exact prime_oneHundredTwentyFiveDS_401311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3566049547) ^ 1783024773 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 3566049547) ^ 1188683182 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 3566049547) ^ 2407866 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 3566049547) ^ 8886 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_4211958841 : Nat.Prime 4211958841 := by
  apply lucas_primality 4211958841 (11 : ZMod 4211958841)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (29, 1), (31, 1), (39043, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (29, 1), (31, 1), (39043, 1)] : List FactorBlock).map factorBlockValue).prod) = 4211958841 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_5
      · exact prime_oneHundredTwentyFiveDS_29
      · exact prime_oneHundredTwentyFiveDS_31
      · exact prime_oneHundredTwentyFiveDS_39043
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 4211958841) ^ 2105979420 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (11 : ZMod 4211958841) ^ 1403986280 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (11 : ZMod 4211958841) ^ 842391768 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (11 : ZMod 4211958841) ^ 145239960 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (11 : ZMod 4211958841) ^ 135869640 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (11 : ZMod 4211958841) ^ 107880 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_4555473661 : Nat.Prime 4555473661 := by
  apply lucas_primality 4555473661 (2 : ZMod 4555473661)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (25308187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (25308187, 1)] : List FactorBlock).map factorBlockValue).prod) = 4555473661 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_5
      · exact prime_oneHundredTwentyFiveDS_25308187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4555473661) ^ 2277736830 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 4555473661) ^ 1518491220 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 4555473661) ^ 911094732 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 4555473661) ^ 180 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_6037638679 : Nat.Prime 6037638679 := by
  apply lucas_primality 6037638679 (3 : ZMod 6037638679)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) = 6037638679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_31
      · exact prime_oneHundredTwentyFiveDS_10820141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6037638679) ^ 3018819339 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 2012546226 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 194762538 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 558 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_7189874807 : Nat.Prime 7189874807 := by
  apply lucas_primality 7189874807 (5 : ZMod 7189874807)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (137, 1), (26240419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (137, 1), (26240419, 1)] : List FactorBlock).map factorBlockValue).prod) = 7189874807 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_137
      · exact prime_oneHundredTwentyFiveDS_26240419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 7189874807) ^ 3594937403 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 7189874807) ^ 52480838 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 7189874807) ^ 274 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_7667290643 : Nat.Prime 7667290643 := by
  apply lucas_primality 7667290643 (2 : ZMod 7667290643)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (348513211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (348513211, 1)] : List FactorBlock).map factorBlockValue).prod) = 7667290643 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_11
      · exact prime_oneHundredTwentyFiveDS_348513211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 7667290643) ^ 3833645321 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 7667290643) ^ 697026422 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 7667290643) ^ 22 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_8099692019 : Nat.Prime 8099692019 := by
  apply lucas_primality 8099692019 (2 : ZMod 8099692019)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (368167819, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (368167819, 1)] : List FactorBlock).map factorBlockValue).prod) = 8099692019 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_11
      · exact prime_oneHundredTwentyFiveDS_368167819
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 8099692019) ^ 4049846009 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 8099692019) ^ 736335638 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 8099692019) ^ 22 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_8959648127 : Nat.Prime 8959648127 := by
  apply lucas_primality 8959648127 (5 : ZMod 8959648127)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (13, 1), (1733, 1), (18077, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (13, 1), (1733, 1), (18077, 1)] : List FactorBlock).map factorBlockValue).prod) = 8959648127 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_11
      · exact prime_oneHundredTwentyFiveDS_13
      · exact prime_oneHundredTwentyFiveDS_1733
      · exact prime_oneHundredTwentyFiveDS_18077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 8959648127) ^ 4479824063 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 8959648127) ^ 814513466 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 8959648127) ^ 689203702 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 8959648127) ^ 5170022 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 8959648127) ^ 495638 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_10228771507 : Nat.Prime 10228771507 := by
  apply lucas_primality 10228771507 (2 : ZMod 10228771507)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (197, 1), (317, 1), (27299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (197, 1), (317, 1), (27299, 1)] : List FactorBlock).map factorBlockValue).prod) = 10228771507 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_197
      · exact prime_oneHundredTwentyFiveDS_317
      · exact prime_oneHundredTwentyFiveDS_27299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 10228771507) ^ 5114385753 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 10228771507) ^ 3409590502 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 10228771507) ^ 51922698 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 10228771507) ^ 32267418 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 10228771507) ^ 374694 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_10816275053 : Nat.Prime 10816275053 := by
  apply lucas_primality 10816275053 (2 : ZMod 10816275053)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (1249, 1), (196817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (1249, 1), (196817, 1)] : List FactorBlock).map factorBlockValue).prod) = 10816275053 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_11
      · exact prime_oneHundredTwentyFiveDS_1249
      · exact prime_oneHundredTwentyFiveDS_196817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 10816275053) ^ 5408137526 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 10816275053) ^ 983297732 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 10816275053) ^ 8659948 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 10816275053) ^ 54956 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_15613124869 : Nat.Prime 15613124869 := by
  apply lucas_primality 15613124869 (6 : ZMod 15613124869)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (11, 1), (23, 1), (79, 1), (2411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (11, 1), (23, 1), (79, 1), (2411, 1)] : List FactorBlock).map factorBlockValue).prod) = 15613124869 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_11
      · exact prime_oneHundredTwentyFiveDS_23
      · exact prime_oneHundredTwentyFiveDS_79
      · exact prime_oneHundredTwentyFiveDS_2411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 15613124869) ^ 7806562434 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (6 : ZMod 15613124869) ^ 5204374956 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (6 : ZMod 15613124869) ^ 1419374988 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (6 : ZMod 15613124869) ^ 678831516 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (6 : ZMod 15613124869) ^ 197634492 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (6 : ZMod 15613124869) ^ 6475788 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_16482432073 : Nat.Prime 16482432073 := by
  apply lucas_primality 16482432073 (10 : ZMod 16482432073)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (139, 1), (1279, 1), (3863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (139, 1), (1279, 1), (3863, 1)] : List FactorBlock).map factorBlockValue).prod) = 16482432073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_139
      · exact prime_oneHundredTwentyFiveDS_1279
      · exact prime_oneHundredTwentyFiveDS_3863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 16482432073) ^ 8241216036 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (10 : ZMod 16482432073) ^ 5494144024 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (10 : ZMod 16482432073) ^ 118578648 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (10 : ZMod 16482432073) ^ 12886968 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (10 : ZMod 16482432073) ^ 4266744 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_19208849867 : Nat.Prime 19208849867 := by
  apply lucas_primality 19208849867 (2 : ZMod 19208849867)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1123, 1), (8552471, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1123, 1), (8552471, 1)] : List FactorBlock).map factorBlockValue).prod) = 19208849867 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_1123
      · exact prime_oneHundredTwentyFiveDS_8552471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 19208849867) ^ 9604424933 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 19208849867) ^ 17104942 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 19208849867) ^ 2246 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_20171157229 : Nat.Prime 20171157229 := by
  apply lucas_primality 20171157229 (2 : ZMod 20171157229)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (23, 2), (101, 1), (10487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (23, 2), (101, 1), (10487, 1)] : List FactorBlock).map factorBlockValue).prod) = 20171157229 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_23
      · exact prime_oneHundredTwentyFiveDS_101
      · exact prime_oneHundredTwentyFiveDS_10487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 20171157229) ^ 10085578614 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 20171157229) ^ 6723719076 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 20171157229) ^ 877006836 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 20171157229) ^ 199714428 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 20171157229) ^ 1923444 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_21804470119 : Nat.Prime 21804470119 := by
  apply lucas_primality 21804470119 (3 : ZMod 21804470119)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (3343, 1), (362357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (3343, 1), (362357, 1)] : List FactorBlock).map factorBlockValue).prod) = 21804470119 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_3343
      · exact prime_oneHundredTwentyFiveDS_362357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 21804470119) ^ 10902235059 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 21804470119) ^ 7268156706 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 21804470119) ^ 6522426 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 21804470119) ^ 60174 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_23075222129 : Nat.Prime 23075222129 := by
  apply lucas_primality 23075222129 (3 : ZMod 23075222129)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (4271, 1), (48239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (4271, 1), (48239, 1)] : List FactorBlock).map factorBlockValue).prod) = 23075222129 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_7
      · exact prime_oneHundredTwentyFiveDS_4271
      · exact prime_oneHundredTwentyFiveDS_48239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 23075222129) ^ 11537611064 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 23075222129) ^ 3296460304 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 23075222129) ^ 5402768 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 23075222129) ^ 478352 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_23195491427 : Nat.Prime 23195491427 := by
  apply lucas_primality 23195491427 (2 : ZMod 23195491427)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (151, 1), (2089, 1), (36767, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (151, 1), (2089, 1), (36767, 1)] : List FactorBlock).map factorBlockValue).prod) = 23195491427 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_151
      · exact prime_oneHundredTwentyFiveDS_2089
      · exact prime_oneHundredTwentyFiveDS_36767
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 23195491427) ^ 11597745713 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 23195491427) ^ 153612526 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 23195491427) ^ 11103634 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 23195491427) ^ 630878 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_25232565443 : Nat.Prime 25232565443 := by
  apply lucas_primality 25232565443 (2 : ZMod 25232565443)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (2389, 1), (754427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (2389, 1), (754427, 1)] : List FactorBlock).map factorBlockValue).prod) = 25232565443 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_7
      · exact prime_oneHundredTwentyFiveDS_2389
      · exact prime_oneHundredTwentyFiveDS_754427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 25232565443) ^ 12616282721 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 25232565443) ^ 3604652206 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 25232565443) ^ 10561978 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 25232565443) ^ 33446 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_26752207429 : Nat.Prime 26752207429 := by
  apply lucas_primality 26752207429 (2 : ZMod 26752207429)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (4621, 1), (160813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (4621, 1), (160813, 1)] : List FactorBlock).map factorBlockValue).prod) = 26752207429 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_4621
      · exact prime_oneHundredTwentyFiveDS_160813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 26752207429) ^ 13376103714 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 26752207429) ^ 8917402476 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 26752207429) ^ 5789268 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 26752207429) ^ 166356 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_27054425759 : Nat.Prime 27054425759 := by
  apply lucas_primality 27054425759 (7 : ZMod 27054425759)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (75767, 1), (178537, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (75767, 1), (178537, 1)] : List FactorBlock).map factorBlockValue).prod) = 27054425759 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_75767
      · exact prime_oneHundredTwentyFiveDS_178537
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 27054425759) ^ 13527212879 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (7 : ZMod 27054425759) ^ 357074 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (7 : ZMod 27054425759) ^ 151534 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_28925867687 : Nat.Prime 28925867687 := by
  apply lucas_primality 28925867687 (5 : ZMod 28925867687)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (466546253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (466546253, 1)] : List FactorBlock).map factorBlockValue).prod) = 28925867687 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_31
      · exact prime_oneHundredTwentyFiveDS_466546253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 28925867687) ^ 14462933843 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 28925867687) ^ 933092506 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 28925867687) ^ 62 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_36571632973 : Nat.Prime 36571632973 := by
  apply lucas_primality 36571632973 (2 : ZMod 36571632973)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (19, 1), (83, 1), (276079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (19, 1), (83, 1), (276079, 1)] : List FactorBlock).map factorBlockValue).prod) = 36571632973 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_7
      · exact prime_oneHundredTwentyFiveDS_19
      · exact prime_oneHundredTwentyFiveDS_83
      · exact prime_oneHundredTwentyFiveDS_276079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 36571632973) ^ 18285816486 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 36571632973) ^ 12190544324 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 36571632973) ^ 5224518996 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 36571632973) ^ 1924822788 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 36571632973) ^ 440622084 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 36571632973) ^ 132468 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_39082261807 : Nat.Prime 39082261807 := by
  apply lucas_primality 39082261807 (5 : ZMod 39082261807)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 1), (1567, 1), (65981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 1), (1567, 1), (65981, 1)] : List FactorBlock).map factorBlockValue).prod) = 39082261807 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_7
      · exact prime_oneHundredTwentyFiveDS_1567
      · exact prime_oneHundredTwentyFiveDS_65981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 39082261807) ^ 19541130903 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 39082261807) ^ 13027420602 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 39082261807) ^ 5583180258 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 39082261807) ^ 24940818 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 39082261807) ^ 592326 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_39197916607 : Nat.Prime 39197916607 := by
  apply lucas_primality 39197916607 (3 : ZMod 39197916607)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (49549, 1), (131849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (49549, 1), (131849, 1)] : List FactorBlock).map factorBlockValue).prod) = 39197916607 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_49549
      · exact prime_oneHundredTwentyFiveDS_131849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 39197916607) ^ 19598958303 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 39197916607) ^ 13065972202 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 39197916607) ^ 791094 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 39197916607) ^ 297294 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_44087865863 : Nat.Prime 44087865863 := by
  apply lucas_primality 44087865863 (5 : ZMod 44087865863)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (239, 1), (449, 1), (205421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (239, 1), (449, 1), (205421, 1)] : List FactorBlock).map factorBlockValue).prod) = 44087865863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_239
      · exact prime_oneHundredTwentyFiveDS_449
      · exact prime_oneHundredTwentyFiveDS_205421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 44087865863) ^ 22043932931 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 44087865863) ^ 184468058 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 44087865863) ^ 98191238 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 44087865863) ^ 214622 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_47423310787 : Nat.Prime 47423310787 := by
  apply lucas_primality 47423310787 (2 : ZMod 47423310787)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (131, 1), (6703889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (131, 1), (6703889, 1)] : List FactorBlock).map factorBlockValue).prod) = 47423310787 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_131
      · exact prime_oneHundredTwentyFiveDS_6703889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 47423310787) ^ 23711655393 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 47423310787) ^ 15807770262 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 47423310787) ^ 362010006 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 47423310787) ^ 7074 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_49179546079 : Nat.Prime 49179546079 := by
  apply lucas_primality 49179546079 (3 : ZMod 49179546079)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (19, 1), (33184579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (19, 1), (33184579, 1)] : List FactorBlock).map factorBlockValue).prod) = 49179546079 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_13
      · exact prime_oneHundredTwentyFiveDS_19
      · exact prime_oneHundredTwentyFiveDS_33184579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 49179546079) ^ 24589773039 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 49179546079) ^ 16393182026 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 49179546079) ^ 3783042006 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 49179546079) ^ 2588397162 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 49179546079) ^ 1482 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_59633903137 : Nat.Prime 59633903137 := by
  apply lucas_primality 59633903137 (5 : ZMod 59633903137)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (16763, 1), (37057, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (16763, 1), (37057, 1)] : List FactorBlock).map factorBlockValue).prod) = 59633903137 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_16763
      · exact prime_oneHundredTwentyFiveDS_37057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 59633903137) ^ 29816951568 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 59633903137) ^ 19877967712 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 59633903137) ^ 3557472 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 59633903137) ^ 1609248 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_61347310813 : Nat.Prime 61347310813 := by
  apply lucas_primality 61347310813 (2 : ZMod 61347310813)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (1704091967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (1704091967, 1)] : List FactorBlock).map factorBlockValue).prod) = 61347310813 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_1704091967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 61347310813) ^ 30673655406 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 61347310813) ^ 20449103604 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 61347310813) ^ 36 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_65675742617 : Nat.Prime 65675742617 := by
  apply lucas_primality 65675742617 (3 : ZMod 65675742617)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (746315257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (746315257, 1)] : List FactorBlock).map factorBlockValue).prod) = 65675742617 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_11
      · exact prime_oneHundredTwentyFiveDS_746315257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 65675742617) ^ 32837871308 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 65675742617) ^ 5970522056 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 65675742617) ^ 88 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_65786638727 : Nat.Prime 65786638727 := by
  apply lucas_primality 65786638727 (5 : ZMod 65786638727)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (8167, 1), (236917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (8167, 1), (236917, 1)] : List FactorBlock).map factorBlockValue).prod) = 65786638727 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_17
      · exact prime_oneHundredTwentyFiveDS_8167
      · exact prime_oneHundredTwentyFiveDS_236917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 65786638727) ^ 32893319363 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 65786638727) ^ 3869802278 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 65786638727) ^ 8055178 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 65786638727) ^ 277678 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_66156878033 : Nat.Prime 66156878033 := by
  apply lucas_primality 66156878033 (3 : ZMod 66156878033)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 2), (4253, 1), (19841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 2), (4253, 1), (19841, 1)] : List FactorBlock).map factorBlockValue).prod) = 66156878033 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_7
      · exact prime_oneHundredTwentyFiveDS_4253
      · exact prime_oneHundredTwentyFiveDS_19841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 66156878033) ^ 33078439016 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 66156878033) ^ 9450982576 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 66156878033) ^ 15555344 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 66156878033) ^ 3334352 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_66274533293 : Nat.Prime 66274533293 := by
  apply lucas_primality 66274533293 (2 : ZMod 66274533293)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (1291, 1), (1166723, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (1291, 1), (1166723, 1)] : List FactorBlock).map factorBlockValue).prod) = 66274533293 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_11
      · exact prime_oneHundredTwentyFiveDS_1291
      · exact prime_oneHundredTwentyFiveDS_1166723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 66274533293) ^ 33137266646 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 66274533293) ^ 6024957572 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 66274533293) ^ 51335812 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 66274533293) ^ 56804 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_87683238689 : Nat.Prime 87683238689 := by
  apply lucas_primality 87683238689 (3 : ZMod 87683238689)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (73, 1), (149, 1), (251917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (73, 1), (149, 1), (251917, 1)] : List FactorBlock).map factorBlockValue).prod) = 87683238689 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_73
      · exact prime_oneHundredTwentyFiveDS_149
      · exact prime_oneHundredTwentyFiveDS_251917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 87683238689) ^ 43841619344 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 87683238689) ^ 1201140256 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 87683238689) ^ 588478112 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 87683238689) ^ 348064 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_91211282467 : Nat.Prime 91211282467 := by
  apply lucas_primality 91211282467 (2 : ZMod 91211282467)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (41, 1), (2713, 1), (7193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (41, 1), (2713, 1), (7193, 1)] : List FactorBlock).map factorBlockValue).prod) = 91211282467 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_19
      · exact prime_oneHundredTwentyFiveDS_41
      · exact prime_oneHundredTwentyFiveDS_2713
      · exact prime_oneHundredTwentyFiveDS_7193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 91211282467) ^ 45605641233 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 91211282467) ^ 30403760822 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 91211282467) ^ 4800593814 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 91211282467) ^ 2224665426 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 91211282467) ^ 33620082 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 91211282467) ^ 12680562 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_105025293643 : Nat.Prime 105025293643 := by
  apply lucas_primality 105025293643 (2 : ZMod 105025293643)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (53, 1), (97, 1), (3404827, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (53, 1), (97, 1), (3404827, 1)] : List FactorBlock).map factorBlockValue).prod) = 105025293643 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_53
      · exact prime_oneHundredTwentyFiveDS_97
      · exact prime_oneHundredTwentyFiveDS_3404827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 105025293643) ^ 52512646821 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 105025293643) ^ 35008431214 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 105025293643) ^ 1981609314 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 105025293643) ^ 1082734986 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 105025293643) ^ 30846 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_107373267763 : Nat.Prime 107373267763 := by
  apply lucas_primality 107373267763 (2 : ZMod 107373267763)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (67, 1), (267097681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (67, 1), (267097681, 1)] : List FactorBlock).map factorBlockValue).prod) = 107373267763 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_67
      · exact prime_oneHundredTwentyFiveDS_267097681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 107373267763) ^ 53686633881 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 107373267763) ^ 35791089254 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 107373267763) ^ 1602586086 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 107373267763) ^ 402 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_129795300637 : Nat.Prime 129795300637 := by
  apply lucas_primality 129795300637 (2 : ZMod 129795300637)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (10816275053, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (10816275053, 1)] : List FactorBlock).map factorBlockValue).prod) = 129795300637 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_10816275053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 129795300637) ^ 64897650318 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 129795300637) ^ 43265100212 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 129795300637) ^ 12 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_134618114963 : Nat.Prime 134618114963 := by
  apply lucas_primality 134618114963 (2 : ZMod 134618114963)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (60257, 1), (1117033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (60257, 1), (1117033, 1)] : List FactorBlock).map factorBlockValue).prod) = 134618114963 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_60257
      · exact prime_oneHundredTwentyFiveDS_1117033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 134618114963) ^ 67309057481 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 134618114963) ^ 2234066 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 134618114963) ^ 120514 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_137306949937 : Nat.Prime 137306949937 := by
  apply lucas_primality 137306949937 (5 : ZMod 137306949937)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (13, 1), (17, 1), (131, 1), (98807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (13, 1), (17, 1), (131, 1), (98807, 1)] : List FactorBlock).map factorBlockValue).prod) = 137306949937 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_13
      · exact prime_oneHundredTwentyFiveDS_17
      · exact prime_oneHundredTwentyFiveDS_131
      · exact prime_oneHundredTwentyFiveDS_98807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 137306949937) ^ 68653474968 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 137306949937) ^ 45768983312 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 137306949937) ^ 10562073072 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 137306949937) ^ 8076879408 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 137306949937) ^ 1048144656 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 137306949937) ^ 1389648 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_140168308879 : Nat.Prime 140168308879 := by
  apply lucas_primality 140168308879 (3 : ZMod 140168308879)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (853, 1), (702239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (853, 1), (702239, 1)] : List FactorBlock).map factorBlockValue).prod) = 140168308879 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_13
      · exact prime_oneHundredTwentyFiveDS_853
      · exact prime_oneHundredTwentyFiveDS_702239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 140168308879) ^ 70084154439 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 140168308879) ^ 46722769626 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 140168308879) ^ 10782177606 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 140168308879) ^ 164323926 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 140168308879) ^ 199602 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_156791666429 : Nat.Prime 156791666429 := by
  apply lucas_primality 156791666429 (2 : ZMod 156791666429)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (39197916607, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (39197916607, 1)] : List FactorBlock).map factorBlockValue).prod) = 156791666429 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_39197916607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 156791666429) ^ 78395833214 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 156791666429) ^ 4 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_157131497951 : Nat.Prime 157131497951 := by
  apply lucas_primality 157131497951 (28 : ZMod 157131497951)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (7, 1), (97, 1), (4628321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (7, 1), (97, 1), (4628321, 1)] : List FactorBlock).map factorBlockValue).prod) = 157131497951 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_5
      · exact prime_oneHundredTwentyFiveDS_7
      · exact prime_oneHundredTwentyFiveDS_97
      · exact prime_oneHundredTwentyFiveDS_4628321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (28 : ZMod 157131497951) ^ 78565748975 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (28 : ZMod 157131497951) ^ 31426299590 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (28 : ZMod 157131497951) ^ 22447356850 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (28 : ZMod 157131497951) ^ 1619912350 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (28 : ZMod 157131497951) ^ 33950 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_161273666287 : Nat.Prime 161273666287 := by
  apply lucas_primality 161273666287 (3 : ZMod 161273666287)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (8959648127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (8959648127, 1)] : List FactorBlock).map factorBlockValue).prod) = 161273666287 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_8959648127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 161273666287) ^ 80636833143 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 161273666287) ^ 53757888762 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 161273666287) ^ 18 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_178584772031 : Nat.Prime 178584772031 := by
  apply lucas_primality 178584772031 (7 : ZMod 178584772031)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (17, 1), (150071237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (17, 1), (150071237, 1)] : List FactorBlock).map factorBlockValue).prod) = 178584772031 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_5
      · exact prime_oneHundredTwentyFiveDS_7
      · exact prime_oneHundredTwentyFiveDS_17
      · exact prime_oneHundredTwentyFiveDS_150071237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 178584772031) ^ 89292386015 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (7 : ZMod 178584772031) ^ 35716954406 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (7 : ZMod 178584772031) ^ 25512110290 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (7 : ZMod 178584772031) ^ 10504986590 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (7 : ZMod 178584772031) ^ 1190 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_197450244671 : Nat.Prime 197450244671 := by
  apply lucas_primality 197450244671 (11 : ZMod 197450244671)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 4), (8223667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 4), (8223667, 1)] : List FactorBlock).map factorBlockValue).prod) = 197450244671 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_5
      · exact prime_oneHundredTwentyFiveDS_7
      · exact prime_oneHundredTwentyFiveDS_8223667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 197450244671) ^ 98725122335 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (11 : ZMod 197450244671) ^ 39490048934 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (11 : ZMod 197450244671) ^ 28207177810 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (11 : ZMod 197450244671) ^ 24010 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_207222858971 : Nat.Prime 207222858971 := by
  apply lucas_primality 207222858971 (2 : ZMod 207222858971)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (37, 1), (89, 1), (1987, 1), (3167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (37, 1), (89, 1), (1987, 1), (3167, 1)] : List FactorBlock).map factorBlockValue).prod) = 207222858971 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_5
      · exact prime_oneHundredTwentyFiveDS_37
      · exact prime_oneHundredTwentyFiveDS_89
      · exact prime_oneHundredTwentyFiveDS_1987
      · exact prime_oneHundredTwentyFiveDS_3167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 207222858971) ^ 103611429485 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 207222858971) ^ 41444571794 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 207222858971) ^ 5600617810 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 207222858971) ^ 2328346730 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 207222858971) ^ 104289310 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 207222858971) ^ 65431910 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_336716473243 : Nat.Prime 336716473243 := by
  apply lucas_primality 336716473243 (2 : ZMod 336716473243)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5167, 1), (10861121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5167, 1), (10861121, 1)] : List FactorBlock).map factorBlockValue).prod) = 336716473243 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_5167
      · exact prime_oneHundredTwentyFiveDS_10861121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 336716473243) ^ 168358236621 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 336716473243) ^ 112238824414 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 336716473243) ^ 65166726 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 336716473243) ^ 31002 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_353255916203 : Nat.Prime 353255916203 := by
  apply lucas_primality 353255916203 (2 : ZMod 353255916203)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (25232565443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (25232565443, 1)] : List FactorBlock).map factorBlockValue).prod) = 353255916203 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_7
      · exact prime_oneHundredTwentyFiveDS_25232565443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 353255916203) ^ 176627958101 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 353255916203) ^ 50465130886 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 353255916203) ^ 14 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_357169544063 : Nat.Prime 357169544063 := by
  apply lucas_primality 357169544063 (5 : ZMod 357169544063)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (178584772031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (178584772031, 1)] : List FactorBlock).map factorBlockValue).prod) = 357169544063 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_178584772031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 357169544063) ^ 178584772031 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 357169544063) ^ 2 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_569326079471 : Nat.Prime 569326079471 := by
  apply lucas_primality 569326079471 (7 : ZMod 569326079471)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (73, 1), (20599, 1), (37861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (73, 1), (20599, 1), (37861, 1)] : List FactorBlock).map factorBlockValue).prod) = 569326079471 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_5
      · exact prime_oneHundredTwentyFiveDS_73
      · exact prime_oneHundredTwentyFiveDS_20599
      · exact prime_oneHundredTwentyFiveDS_37861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 569326079471) ^ 284663039735 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (7 : ZMod 569326079471) ^ 113865215894 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (7 : ZMod 569326079471) ^ 7798987390 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (7 : ZMod 569326079471) ^ 27638530 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (7 : ZMod 569326079471) ^ 15037270 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_639742302293 : Nat.Prime 639742302293 := by
  apply lucas_primality 639742302293 (2 : ZMod 639742302293)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (593, 1), (269705861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (593, 1), (269705861, 1)] : List FactorBlock).map factorBlockValue).prod) = 639742302293 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_593
      · exact prime_oneHundredTwentyFiveDS_269705861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 639742302293) ^ 319871151146 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 639742302293) ^ 1078823444 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 639742302293) ^ 2372 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_659795388823 : Nat.Prime 659795388823 := by
  apply lucas_primality 659795388823 (6 : ZMod 659795388823)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (37, 1), (83, 1), (103, 1), (115883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (37, 1), (83, 1), (103, 1), (115883, 1)] : List FactorBlock).map factorBlockValue).prod) = 659795388823 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_37
      · exact prime_oneHundredTwentyFiveDS_83
      · exact prime_oneHundredTwentyFiveDS_103
      · exact prime_oneHundredTwentyFiveDS_115883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 659795388823) ^ 329897694411 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (6 : ZMod 659795388823) ^ 219931796274 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (6 : ZMod 659795388823) ^ 17832307806 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (6 : ZMod 659795388823) ^ 7949342034 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (6 : ZMod 659795388823) ^ 6405780474 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (6 : ZMod 659795388823) ^ 5693634 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_679392525673 : Nat.Prime 679392525673 := by
  apply lucas_primality 679392525673 (35 : ZMod 679392525673)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (7, 1), (17, 1), (23, 1), (1149191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (7, 1), (17, 1), (23, 1), (1149191, 1)] : List FactorBlock).map factorBlockValue).prod) = 679392525673 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_7
      · exact prime_oneHundredTwentyFiveDS_17
      · exact prime_oneHundredTwentyFiveDS_23
      · exact prime_oneHundredTwentyFiveDS_1149191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (35 : ZMod 679392525673) ^ 339696262836 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (35 : ZMod 679392525673) ^ 226464175224 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (35 : ZMod 679392525673) ^ 97056075096 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (35 : ZMod 679392525673) ^ 39964266216 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (35 : ZMod 679392525673) ^ 29538805464 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (35 : ZMod 679392525673) ^ 591192 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_738747629527 : Nat.Prime 738747629527 := by
  apply lucas_primality 738747629527 (5 : ZMod 738747629527)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (52457, 1), (2347153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (52457, 1), (2347153, 1)] : List FactorBlock).map factorBlockValue).prod) = 738747629527 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_52457
      · exact prime_oneHundredTwentyFiveDS_2347153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 738747629527) ^ 369373814763 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 738747629527) ^ 246249209842 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 738747629527) ^ 14082918 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 738747629527) ^ 314742 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_791150393801 : Nat.Prime 791150393801 := by
  apply lucas_primality 791150393801 (3 : ZMod 791150393801)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (13, 1), (823, 1), (369731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (13, 1), (823, 1), (369731, 1)] : List FactorBlock).map factorBlockValue).prod) = 791150393801 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_5
      · exact prime_oneHundredTwentyFiveDS_13
      · exact prime_oneHundredTwentyFiveDS_823
      · exact prime_oneHundredTwentyFiveDS_369731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 791150393801) ^ 395575196900 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 791150393801) ^ 158230078760 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 791150393801) ^ 60857722600 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 791150393801) ^ 961300600 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 791150393801) ^ 2139800 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_886658979091 : Nat.Prime 886658979091 := by
  apply lucas_primality 886658979091 (3 : ZMod 886658979091)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (853, 1), (34648651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (853, 1), (34648651, 1)] : List FactorBlock).map factorBlockValue).prod) = 886658979091 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_5
      · exact prime_oneHundredTwentyFiveDS_853
      · exact prime_oneHundredTwentyFiveDS_34648651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 886658979091) ^ 443329489545 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 886658979091) ^ 295552993030 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 886658979091) ^ 177331795818 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 886658979091) ^ 1039459530 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 886658979091) ^ 25590 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_912112824671 : Nat.Prime 912112824671 := by
  apply lucas_primality 912112824671 (11 : ZMod 912112824671)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (91211282467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (91211282467, 1)] : List FactorBlock).map factorBlockValue).prod) = 912112824671 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_5
      · exact prime_oneHundredTwentyFiveDS_91211282467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 912112824671) ^ 456056412335 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (11 : ZMod 912112824671) ^ 182422564934 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (11 : ZMod 912112824671) ^ 10 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_913146925993 : Nat.Prime 913146925993 := by
  apply lucas_primality 913146925993 (5 : ZMod 913146925993)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (79, 1), (68802511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (79, 1), (68802511, 1)] : List FactorBlock).map factorBlockValue).prod) = 913146925993 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_7
      · exact prime_oneHundredTwentyFiveDS_79
      · exact prime_oneHundredTwentyFiveDS_68802511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 913146925993) ^ 456573462996 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 913146925993) ^ 304382308664 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 913146925993) ^ 130449560856 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 913146925993) ^ 11558821848 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 913146925993) ^ 13272 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_971937009349 : Nat.Prime 971937009349 := by
  apply lucas_primality 971937009349 (2 : ZMod 971937009349)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1619, 1), (50027641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1619, 1), (50027641, 1)] : List FactorBlock).map factorBlockValue).prod) = 971937009349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_1619
      · exact prime_oneHundredTwentyFiveDS_50027641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 971937009349) ^ 485968504674 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 971937009349) ^ 323979003116 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 971937009349) ^ 600331692 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 971937009349) ^ 19428 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_1023533882359 : Nat.Prime 1023533882359 := by
  apply lucas_primality 1023533882359 (6 : ZMod 1023533882359)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (23, 1), (191, 1), (1327, 1), (2251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (23, 1), (191, 1), (1327, 1), (2251, 1)] : List FactorBlock).map factorBlockValue).prod) = 1023533882359 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_13
      · exact prime_oneHundredTwentyFiveDS_23
      · exact prime_oneHundredTwentyFiveDS_191
      · exact prime_oneHundredTwentyFiveDS_1327
      · exact prime_oneHundredTwentyFiveDS_2251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1023533882359) ^ 511766941179 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (6 : ZMod 1023533882359) ^ 341177960786 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (6 : ZMod 1023533882359) ^ 78733375566 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (6 : ZMod 1023533882359) ^ 44501473146 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (6 : ZMod 1023533882359) ^ 5358816138 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (6 : ZMod 1023533882359) ^ 771314154 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (6 : ZMod 1023533882359) ^ 454701858 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_1064628001417 : Nat.Prime 1064628001417 := by
  apply lucas_primality 1064628001417 (5 : ZMod 1064628001417)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (37, 1), (61, 1), (2807741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (37, 1), (61, 1), (2807741, 1)] : List FactorBlock).map factorBlockValue).prod) = 1064628001417 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_7
      · exact prime_oneHundredTwentyFiveDS_37
      · exact prime_oneHundredTwentyFiveDS_61
      · exact prime_oneHundredTwentyFiveDS_2807741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1064628001417) ^ 532314000708 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 1064628001417) ^ 354876000472 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 1064628001417) ^ 152089714488 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 1064628001417) ^ 28773729768 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 1064628001417) ^ 17452918056 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 1064628001417) ^ 379176 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_1141414241159 : Nat.Prime 1141414241159 := by
  apply lucas_primality 1141414241159 (11 : ZMod 1141414241159)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (547, 1), (587, 1), (1777411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (547, 1), (587, 1), (1777411, 1)] : List FactorBlock).map factorBlockValue).prod) = 1141414241159 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_547
      · exact prime_oneHundredTwentyFiveDS_587
      · exact prime_oneHundredTwentyFiveDS_1777411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 1141414241159) ^ 570707120579 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (11 : ZMod 1141414241159) ^ 2086680514 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (11 : ZMod 1141414241159) ^ 1944487634 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (11 : ZMod 1141414241159) ^ 642178 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_1370014198489 : Nat.Prime 1370014198489 := by
  apply lucas_primality 1370014198489 (7 : ZMod 1370014198489)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (13, 1), (13711, 1), (106753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (13, 1), (13711, 1), (106753, 1)] : List FactorBlock).map factorBlockValue).prod) = 1370014198489 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_13
      · exact prime_oneHundredTwentyFiveDS_13711
      · exact prime_oneHundredTwentyFiveDS_106753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1370014198489) ^ 685007099244 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (7 : ZMod 1370014198489) ^ 456671399496 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (7 : ZMod 1370014198489) ^ 105385707576 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (7 : ZMod 1370014198489) ^ 99920808 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (7 : ZMod 1370014198489) ^ 12833496 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_1510899225343 : Nat.Prime 1510899225343 := by
  apply lucas_primality 1510899225343 (5 : ZMod 1510899225343)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (16007, 1), (1210127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (16007, 1), (1210127, 1)] : List FactorBlock).map factorBlockValue).prod) = 1510899225343 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_13
      · exact prime_oneHundredTwentyFiveDS_16007
      · exact prime_oneHundredTwentyFiveDS_1210127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1510899225343) ^ 755449612671 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 1510899225343) ^ 503633075114 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 1510899225343) ^ 116223017334 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 1510899225343) ^ 94389906 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 1510899225343) ^ 1248546 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_1754271617359 : Nat.Prime 1754271617359 := by
  apply lucas_primality 1754271617359 (3 : ZMod 1754271617359)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (73, 1), (308091257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (73, 1), (308091257, 1)] : List FactorBlock).map factorBlockValue).prod) = 1754271617359 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_13
      · exact prime_oneHundredTwentyFiveDS_73
      · exact prime_oneHundredTwentyFiveDS_308091257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1754271617359) ^ 877135808679 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1754271617359) ^ 584757205786 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1754271617359) ^ 134943970566 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1754271617359) ^ 24031118046 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1754271617359) ^ 5694 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_1836650332529 : Nat.Prime 1836650332529 := by
  apply lucas_primality 1836650332529 (3 : ZMod 1836650332529)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (11, 2), (948683023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (11, 2), (948683023, 1)] : List FactorBlock).map factorBlockValue).prod) = 1836650332529 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_11
      · exact prime_oneHundredTwentyFiveDS_948683023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1836650332529) ^ 918325166264 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1836650332529) ^ 166968212048 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1836650332529) ^ 1936 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_1858612209943 : Nat.Prime 1858612209943 := by
  apply lucas_primality 1858612209943 (5 : ZMod 1858612209943)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (61, 1), (3469, 1), (1463873, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (61, 1), (3469, 1), (1463873, 1)] : List FactorBlock).map factorBlockValue).prod) = 1858612209943 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_61
      · exact prime_oneHundredTwentyFiveDS_3469
      · exact prime_oneHundredTwentyFiveDS_1463873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1858612209943) ^ 929306104971 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 1858612209943) ^ 619537403314 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 1858612209943) ^ 30469052622 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 1858612209943) ^ 535777518 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 1858612209943) ^ 1269654 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_1881499997149 : Nat.Prime 1881499997149 := by
  apply lucas_primality 1881499997149 (6 : ZMod 1881499997149)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (156791666429, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (156791666429, 1)] : List FactorBlock).map factorBlockValue).prod) = 1881499997149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_156791666429
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 1881499997149) ^ 940749998574 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (6 : ZMod 1881499997149) ^ 627166665716 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (6 : ZMod 1881499997149) ^ 12 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_1890399915251 : Nat.Prime 1890399915251 := by
  apply lucas_primality 1890399915251 (7 : ZMod 1890399915251)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 3), (7, 1), (11, 1), (73, 1), (1345241, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 3), (7, 1), (11, 1), (73, 1), (1345241, 1)] : List FactorBlock).map factorBlockValue).prod) = 1890399915251 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_5
      · exact prime_oneHundredTwentyFiveDS_7
      · exact prime_oneHundredTwentyFiveDS_11
      · exact prime_oneHundredTwentyFiveDS_73
      · exact prime_oneHundredTwentyFiveDS_1345241
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1890399915251) ^ 945199957625 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (7 : ZMod 1890399915251) ^ 378079983050 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (7 : ZMod 1890399915251) ^ 270057130750 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (7 : ZMod 1890399915251) ^ 171854537750 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (7 : ZMod 1890399915251) ^ 25895889250 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (7 : ZMod 1890399915251) ^ 1405250 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_2428226959999 : Nat.Prime 2428226959999 := by
  apply lucas_primality 2428226959999 (3 : ZMod 2428226959999)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (83, 1), (3049, 1), (228457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (83, 1), (3049, 1), (228457, 1)] : List FactorBlock).map factorBlockValue).prod) = 2428226959999 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_7
      · exact prime_oneHundredTwentyFiveDS_83
      · exact prime_oneHundredTwentyFiveDS_3049
      · exact prime_oneHundredTwentyFiveDS_228457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2428226959999) ^ 1214113479999 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 2428226959999) ^ 809408986666 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 2428226959999) ^ 346889565714 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 2428226959999) ^ 29255746506 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 2428226959999) ^ 796401102 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 2428226959999) ^ 10628814 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_2729490688553 : Nat.Prime 2729490688553 := by
  apply lucas_primality 2729490688553 (3 : ZMod 2729490688553)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (173, 1), (35069, 1), (56237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (173, 1), (35069, 1), (56237, 1)] : List FactorBlock).map factorBlockValue).prod) = 2729490688553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_173
      · exact prime_oneHundredTwentyFiveDS_35069
      · exact prime_oneHundredTwentyFiveDS_56237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2729490688553) ^ 1364745344276 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 2729490688553) ^ 15777402824 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 2729490688553) ^ 77832008 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 2729490688553) ^ 48535496 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_2841040091737 : Nat.Prime 2841040091737 := by
  apply lucas_primality 2841040091737 (5 : ZMod 2841040091737)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (7, 1), (11, 1), (103, 1), (677, 1), (7349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (7, 1), (11, 1), (103, 1), (677, 1), (7349, 1)] : List FactorBlock).map factorBlockValue).prod) = 2841040091737 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_7
      · exact prime_oneHundredTwentyFiveDS_11
      · exact prime_oneHundredTwentyFiveDS_103
      · exact prime_oneHundredTwentyFiveDS_677
      · exact prime_oneHundredTwentyFiveDS_7349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2841040091737) ^ 1420520045868 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 2841040091737) ^ 947013363912 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 2841040091737) ^ 405862870248 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 2841040091737) ^ 258276371976 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 2841040091737) ^ 27582913512 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 2841040091737) ^ 4196514168 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 2841040091737) ^ 386588664 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_3415956476827 : Nat.Prime 3415956476827 := by
  apply lucas_primality 3415956476827 (2 : ZMod 3415956476827)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (569326079471, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (569326079471, 1)] : List FactorBlock).map factorBlockValue).prod) = 3415956476827 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_569326079471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3415956476827) ^ 1707978238413 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 3415956476827) ^ 1138652158942 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 3415956476827) ^ 6 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_5008861874381 : Nat.Prime 5008861874381 := by
  apply lucas_primality 5008861874381 (3 : ZMod 5008861874381)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (13, 1), (397, 1), (6932297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (13, 1), (397, 1), (6932297, 1)] : List FactorBlock).map factorBlockValue).prod) = 5008861874381 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_5
      · exact prime_oneHundredTwentyFiveDS_7
      · exact prime_oneHundredTwentyFiveDS_13
      · exact prime_oneHundredTwentyFiveDS_397
      · exact prime_oneHundredTwentyFiveDS_6932297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 5008861874381) ^ 2504430937190 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 5008861874381) ^ 1001772374876 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 5008861874381) ^ 715551696340 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 5008861874381) ^ 385297067260 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 5008861874381) ^ 12616780540 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 5008861874381) ^ 722540 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_9105076137821 : Nat.Prime 9105076137821 := by
  apply lucas_primality 9105076137821 (2 : ZMod 9105076137821)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (13, 1), (37, 1), (946473611, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (13, 1), (37, 1), (946473611, 1)] : List FactorBlock).map factorBlockValue).prod) = 9105076137821 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_5
      · exact prime_oneHundredTwentyFiveDS_13
      · exact prime_oneHundredTwentyFiveDS_37
      · exact prime_oneHundredTwentyFiveDS_946473611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9105076137821) ^ 4552538068910 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 9105076137821) ^ 1821015227564 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 9105076137821) ^ 700390472140 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 9105076137821) ^ 246083138860 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 9105076137821) ^ 9620 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_9191211511631 : Nat.Prime 9191211511631 := by
  apply lucas_primality 9191211511631 (7 : ZMod 9191211511631)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (23, 1), (11597, 1), (3445873, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (23, 1), (11597, 1), (3445873, 1)] : List FactorBlock).map factorBlockValue).prod) = 9191211511631 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_5
      · exact prime_oneHundredTwentyFiveDS_23
      · exact prime_oneHundredTwentyFiveDS_11597
      · exact prime_oneHundredTwentyFiveDS_3445873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 9191211511631) ^ 4595605755815 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (7 : ZMod 9191211511631) ^ 1838242302326 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (7 : ZMod 9191211511631) ^ 399617891810 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (7 : ZMod 9191211511631) ^ 792550790 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (7 : ZMod 9191211511631) ^ 2667310 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_9438033162319 : Nat.Prime 9438033162319 := by
  apply lucas_primality 9438033162319 (6 : ZMod 9438033162319)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1091, 1), (1441801583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1091, 1), (1441801583, 1)] : List FactorBlock).map factorBlockValue).prod) = 9438033162319 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_1091
      · exact prime_oneHundredTwentyFiveDS_1441801583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 9438033162319) ^ 4719016581159 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (6 : ZMod 9438033162319) ^ 3146011054106 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (6 : ZMod 9438033162319) ^ 8650809498 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (6 : ZMod 9438033162319) ^ 6546 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_10223538369013 : Nat.Prime 10223538369013 := by
  apply lucas_primality 10223538369013 (2 : ZMod 10223538369013)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (29, 1), (13147, 1), (744859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (29, 1), (13147, 1), (744859, 1)] : List FactorBlock).map factorBlockValue).prod) = 10223538369013 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_29
      · exact prime_oneHundredTwentyFiveDS_13147
      · exact prime_oneHundredTwentyFiveDS_744859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 10223538369013) ^ 5111769184506 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 10223538369013) ^ 3407846123004 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 10223538369013) ^ 352535805828 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 10223538369013) ^ 777632796 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 10223538369013) ^ 13725468 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_10800628043461 : Nat.Prime 10800628043461 := by
  apply lucas_primality 10800628043461 (2 : ZMod 10800628043461)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (17, 1), (277, 1), (38226899, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (17, 1), (277, 1), (38226899, 1)] : List FactorBlock).map factorBlockValue).prod) = 10800628043461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_5
      · exact prime_oneHundredTwentyFiveDS_17
      · exact prime_oneHundredTwentyFiveDS_277
      · exact prime_oneHundredTwentyFiveDS_38226899
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 10800628043461) ^ 5400314021730 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 10800628043461) ^ 3600209347820 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 10800628043461) ^ 2160125608692 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 10800628043461) ^ 635331061380 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 10800628043461) ^ 38991436980 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 10800628043461) ^ 282540 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_17791598001283 : Nat.Prime 17791598001283 := by
  apply lucas_primality 17791598001283 (2 : ZMod 17791598001283)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (71, 1), (863, 1), (2083, 1), (3319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (71, 1), (863, 1), (2083, 1), (3319, 1)] : List FactorBlock).map factorBlockValue).prod) = 17791598001283 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_7
      · exact prime_oneHundredTwentyFiveDS_71
      · exact prime_oneHundredTwentyFiveDS_863
      · exact prime_oneHundredTwentyFiveDS_2083
      · exact prime_oneHundredTwentyFiveDS_3319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 17791598001283) ^ 8895799000641 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 17791598001283) ^ 5930532667094 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 17791598001283) ^ 2541656857326 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 17791598001283) ^ 250585887342 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 17791598001283) ^ 20615988414 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 17791598001283) ^ 8541333654 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 17791598001283) ^ 5360529678 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_20402133931279 : Nat.Prime 20402133931279 := by
  apply lucas_primality 20402133931279 (11 : ZMod 20402133931279)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 2), (89, 1), (2887, 1), (36457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 2), (89, 1), (2887, 1), (36457, 1)] : List FactorBlock).map factorBlockValue).prod) = 20402133931279 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_11
      · exact prime_oneHundredTwentyFiveDS_89
      · exact prime_oneHundredTwentyFiveDS_2887
      · exact prime_oneHundredTwentyFiveDS_36457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 20402133931279) ^ 10201066965639 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (11 : ZMod 20402133931279) ^ 6800711310426 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (11 : ZMod 20402133931279) ^ 1854739448298 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (11 : ZMod 20402133931279) ^ 229237459902 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (11 : ZMod 20402133931279) ^ 7066897794 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (11 : ZMod 20402133931279) ^ 559621854 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_20962583569177 : Nat.Prime 20962583569177 := by
  apply lucas_primality 20962583569177 (11 : ZMod 20962583569177)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (17, 1), (157, 1), (327254021, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (17, 1), (157, 1), (327254021, 1)] : List FactorBlock).map factorBlockValue).prod) = 20962583569177 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_17
      · exact prime_oneHundredTwentyFiveDS_157
      · exact prime_oneHundredTwentyFiveDS_327254021
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 20962583569177) ^ 10481291784588 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (11 : ZMod 20962583569177) ^ 6987527856392 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (11 : ZMod 20962583569177) ^ 1233093151128 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (11 : ZMod 20962583569177) ^ 133519640568 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (11 : ZMod 20962583569177) ^ 64056 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_21062796965167 : Nat.Prime 21062796965167 := by
  apply lucas_primality 21062796965167 (3 : ZMod 21062796965167)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (43, 1), (293, 1), (1237, 1), (20477, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (43, 1), (293, 1), (1237, 1), (20477, 1)] : List FactorBlock).map factorBlockValue).prod) = 21062796965167 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_11
      · exact prime_oneHundredTwentyFiveDS_43
      · exact prime_oneHundredTwentyFiveDS_293
      · exact prime_oneHundredTwentyFiveDS_1237
      · exact prime_oneHundredTwentyFiveDS_20477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 21062796965167) ^ 10531398482583 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 21062796965167) ^ 7020932321722 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 21062796965167) ^ 1914799724106 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 21062796965167) ^ 489832487562 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 21062796965167) ^ 71886679062 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 21062796965167) ^ 17027321718 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 21062796965167) ^ 1028607558 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_21324626424469 : Nat.Prime 21324626424469 := by
  apply lucas_primality 21324626424469 (2 : ZMod 21324626424469)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (197450244671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (197450244671, 1)] : List FactorBlock).map factorBlockValue).prod) = 21324626424469 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_197450244671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 21324626424469) ^ 10662313212234 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 21324626424469) ^ 7108208808156 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 21324626424469) ^ 108 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_24831037027507 : Nat.Prime 24831037027507 := by
  apply lucas_primality 24831037027507 (2 : ZMod 24831037027507)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (123457, 1), (33521843, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (123457, 1), (33521843, 1)] : List FactorBlock).map factorBlockValue).prod) = 24831037027507 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_123457
      · exact prime_oneHundredTwentyFiveDS_33521843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 24831037027507) ^ 12415518513753 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 24831037027507) ^ 8277012342502 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 24831037027507) ^ 201131058 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 24831037027507) ^ 740742 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_31711264472561 : Nat.Prime 31711264472561 := by
  apply lucas_primality 31711264472561 (3 : ZMod 31711264472561)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (198571, 1), (1996217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (198571, 1), (1996217, 1)] : List FactorBlock).map factorBlockValue).prod) = 31711264472561 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_5
      · exact prime_oneHundredTwentyFiveDS_198571
      · exact prime_oneHundredTwentyFiveDS_1996217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 31711264472561) ^ 15855632236280 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 31711264472561) ^ 6342252894512 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 31711264472561) ^ 159697360 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 31711264472561) ^ 15885680 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_38308738636183 : Nat.Prime 38308738636183 := by
  apply lucas_primality 38308738636183 (6 : ZMod 38308738636183)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (912112824671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (912112824671, 1)] : List FactorBlock).map factorBlockValue).prod) = 38308738636183 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_7
      · exact prime_oneHundredTwentyFiveDS_912112824671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 38308738636183) ^ 19154369318091 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (6 : ZMod 38308738636183) ^ 12769579545394 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (6 : ZMod 38308738636183) ^ 5472676948026 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (6 : ZMod 38308738636183) ^ 42 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_40012680077077 : Nat.Prime 40012680077077 := by
  apply lucas_primality 40012680077077 (2 : ZMod 40012680077077)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (335633, 1), (1419233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (335633, 1), (1419233, 1)] : List FactorBlock).map factorBlockValue).prod) = 40012680077077 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_7
      · exact prime_oneHundredTwentyFiveDS_335633
      · exact prime_oneHundredTwentyFiveDS_1419233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 40012680077077) ^ 20006340038538 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 40012680077077) ^ 13337560025692 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 40012680077077) ^ 5716097153868 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 40012680077077) ^ 119215572 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 40012680077077) ^ 28193172 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_41392999937279 : Nat.Prime 41392999937279 := by
  apply lucas_primality 41392999937279 (7 : ZMod 41392999937279)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (1881499997149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (1881499997149, 1)] : List FactorBlock).map factorBlockValue).prod) = 41392999937279 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_11
      · exact prime_oneHundredTwentyFiveDS_1881499997149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 41392999937279) ^ 20696499968639 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (7 : ZMod 41392999937279) ^ 3762999994298 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (7 : ZMod 41392999937279) ^ 22 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_51712334066891 : Nat.Prime 51712334066891 := by
  apply lucas_primality 51712334066891 (2 : ZMod 51712334066891)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (738747629527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (738747629527, 1)] : List FactorBlock).map factorBlockValue).prod) = 51712334066891 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_5
      · exact prime_oneHundredTwentyFiveDS_7
      · exact prime_oneHundredTwentyFiveDS_738747629527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 51712334066891) ^ 25856167033445 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 51712334066891) ^ 10342466813378 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 51712334066891) ^ 7387476295270 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 51712334066891) ^ 70 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_62960806628351 : Nat.Prime 62960806628351 := by
  apply lucas_primality 62960806628351 (7 : ZMod 62960806628351)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (19, 1), (66274533293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (19, 1), (66274533293, 1)] : List FactorBlock).map factorBlockValue).prod) = 62960806628351 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_5
      · exact prime_oneHundredTwentyFiveDS_19
      · exact prime_oneHundredTwentyFiveDS_66274533293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 62960806628351) ^ 31480403314175 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (7 : ZMod 62960806628351) ^ 12592161325670 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (7 : ZMod 62960806628351) ^ 3313726664650 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (7 : ZMod 62960806628351) ^ 950 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_82785999874559 : Nat.Prime 82785999874559 := by
  apply lucas_primality 82785999874559 (7 : ZMod 82785999874559)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41392999937279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41392999937279, 1)] : List FactorBlock).map factorBlockValue).prod) = 82785999874559 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_41392999937279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (7 : ZMod 82785999874559) ^ 41392999937279 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (7 : ZMod 82785999874559) ^ 2 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_100257985466497 : Nat.Prime 100257985466497 := by
  apply lucas_primality 100257985466497 (5 : ZMod 100257985466497)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 2), (11, 1), (13, 1), (19, 1), (173, 1), (185153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 2), (11, 1), (13, 1), (19, 1), (173, 1), (185153, 1)] : List FactorBlock).map factorBlockValue).prod) = 100257985466497 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_11
      · exact prime_oneHundredTwentyFiveDS_13
      · exact prime_oneHundredTwentyFiveDS_19
      · exact prime_oneHundredTwentyFiveDS_173
      · exact prime_oneHundredTwentyFiveDS_185153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 100257985466497) ^ 50128992733248 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 100257985466497) ^ 33419328488832 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 100257985466497) ^ 9114362315136 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 100257985466497) ^ 7712152728192 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 100257985466497) ^ 5276736077184 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 100257985466497) ^ 579525927552 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 100257985466497) ^ 541487232 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_101052806134517 : Nat.Prime 101052806134517 := by
  apply lucas_primality 101052806134517 (2 : ZMod 101052806134517)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1249, 1), (1721, 1), (2791, 1), (4211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1249, 1), (1721, 1), (2791, 1), (4211, 1)] : List FactorBlock).map factorBlockValue).prod) = 101052806134517 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_1249
      · exact prime_oneHundredTwentyFiveDS_1721
      · exact prime_oneHundredTwentyFiveDS_2791
      · exact prime_oneHundredTwentyFiveDS_4211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 101052806134517) ^ 50526403067258 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 101052806134517) ^ 80906970484 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 101052806134517) ^ 58717493396 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 101052806134517) ^ 36206666476 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 101052806134517) ^ 23997341756 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_136442192788897 : Nat.Prime 136442192788897 := by
  apply lucas_primality 136442192788897 (5 : ZMod 136442192788897)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (39043, 1), (36402757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (39043, 1), (36402757, 1)] : List FactorBlock).map factorBlockValue).prod) = 136442192788897 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_39043
      · exact prime_oneHundredTwentyFiveDS_36402757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 136442192788897) ^ 68221096394448 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 136442192788897) ^ 45480730929632 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 136442192788897) ^ 3494664672 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 136442192788897) ^ 3748128 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_138705063180113 : Nat.Prime 138705063180113 := by
  apply lucas_primality 138705063180113 (3 : ZMod 138705063180113)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (11, 1), (13, 1), (17, 1), (3566049547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (11, 1), (13, 1), (17, 1), (3566049547, 1)] : List FactorBlock).map factorBlockValue).prod) = 138705063180113 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_11
      · exact prime_oneHundredTwentyFiveDS_13
      · exact prime_oneHundredTwentyFiveDS_17
      · exact prime_oneHundredTwentyFiveDS_3566049547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 138705063180113) ^ 69352531590056 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 138705063180113) ^ 12609551198192 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 138705063180113) ^ 10669620244624 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 138705063180113) ^ 8159121363536 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 138705063180113) ^ 38896 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_184147520927603 : Nat.Prime 184147520927603 := by
  apply lucas_primality 184147520927603 (2 : ZMod 184147520927603)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (67, 1), (353, 1), (2957, 1), (57241, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (67, 1), (353, 1), (2957, 1), (57241, 1)] : List FactorBlock).map factorBlockValue).prod) = 184147520927603 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_23
      · exact prime_oneHundredTwentyFiveDS_67
      · exact prime_oneHundredTwentyFiveDS_353
      · exact prime_oneHundredTwentyFiveDS_2957
      · exact prime_oneHundredTwentyFiveDS_57241
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 184147520927603) ^ 92073760463801 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 184147520927603) ^ 8006413953374 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 184147520927603) ^ 2748470461606 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 184147520927603) ^ 521664365234 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 184147520927603) ^ 62275116986 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 184147520927603) ^ 3217056322 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_250017697041709 : Nat.Prime 250017697041709 := by
  apply lucas_primality 250017697041709 (2 : ZMod 250017697041709)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (107, 1), (307, 1), (2767, 1), (229223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (107, 1), (307, 1), (2767, 1), (229223, 1)] : List FactorBlock).map factorBlockValue).prod) = 250017697041709 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_107
      · exact prime_oneHundredTwentyFiveDS_307
      · exact prime_oneHundredTwentyFiveDS_2767
      · exact prime_oneHundredTwentyFiveDS_229223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 250017697041709) ^ 125008848520854 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 250017697041709) ^ 83339232347236 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 250017697041709) ^ 2336613991044 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 250017697041709) ^ 814389892644 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 250017697041709) ^ 90356955924 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 250017697041709) ^ 1090718196 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_418920864867751 : Nat.Prime 418920864867751 := by
  apply lucas_primality 418920864867751 (3 : ZMod 418920864867751)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 3), (7, 1), (17, 1), (89, 1), (257, 1), (205211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 3), (7, 1), (17, 1), (89, 1), (257, 1), (205211, 1)] : List FactorBlock).map factorBlockValue).prod) = 418920864867751 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_5
      · exact prime_oneHundredTwentyFiveDS_7
      · exact prime_oneHundredTwentyFiveDS_17
      · exact prime_oneHundredTwentyFiveDS_89
      · exact prime_oneHundredTwentyFiveDS_257
      · exact prime_oneHundredTwentyFiveDS_205211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 418920864867751) ^ 209460432433875 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 418920864867751) ^ 139640288289250 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 418920864867751) ^ 83784172973550 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 418920864867751) ^ 59845837838250 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 418920864867751) ^ 24642403815750 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 418920864867751) ^ 4706976009750 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 418920864867751) ^ 1630042275750 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 418920864867751) ^ 2041415250 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_453626377825363 : Nat.Prime 453626377825363 := by
  apply lucas_primality 453626377825363 (2 : ZMod 453626377825363)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (10800628043461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (10800628043461, 1)] : List FactorBlock).map factorBlockValue).prod) = 453626377825363 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_7
      · exact prime_oneHundredTwentyFiveDS_10800628043461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 453626377825363) ^ 226813188912681 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 453626377825363) ^ 151208792608454 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 453626377825363) ^ 64803768260766 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 453626377825363) ^ 42 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_513686441622119 : Nat.Prime 513686441622119 := by
  apply lucas_primality 513686441622119 (19 : ZMod 513686441622119)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (59, 1), (73, 1), (59633903137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (59, 1), (73, 1), (59633903137, 1)] : List FactorBlock).map factorBlockValue).prod) = 513686441622119 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_59
      · exact prime_oneHundredTwentyFiveDS_73
      · exact prime_oneHundredTwentyFiveDS_59633903137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 513686441622119) ^ 256843220811059 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (19 : ZMod 513686441622119) ^ 8706549858002 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (19 : ZMod 513686441622119) ^ 7036800570166 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (19 : ZMod 513686441622119) ^ 8614 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_662174074879519 : Nat.Prime 662174074879519 := by
  apply lucas_primality 662174074879519 (3 : ZMod 662174074879519)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (131, 1), (281, 1), (1783, 1), (88499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (131, 1), (281, 1), (1783, 1), (88499, 1)] : List FactorBlock).map factorBlockValue).prod) = 662174074879519 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_19
      · exact prime_oneHundredTwentyFiveDS_131
      · exact prime_oneHundredTwentyFiveDS_281
      · exact prime_oneHundredTwentyFiveDS_1783
      · exact prime_oneHundredTwentyFiveDS_88499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 662174074879519) ^ 331087037439759 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 662174074879519) ^ 220724691626506 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 662174074879519) ^ 34851267098922 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 662174074879519) ^ 5054763930378 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 662174074879519) ^ 2356491369678 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 662174074879519) ^ 371381982546 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 662174074879519) ^ 7482277482 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_688424747690369 : Nat.Prime 688424747690369 := by
  apply lucas_primality 688424747690369 (3 : ZMod 688424747690369)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (13, 1), (131, 1), (13381, 1), (236017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (13, 1), (131, 1), (13381, 1), (236017, 1)] : List FactorBlock).map factorBlockValue).prod) = 688424747690369 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_13
      · exact prime_oneHundredTwentyFiveDS_131
      · exact prime_oneHundredTwentyFiveDS_13381
      · exact prime_oneHundredTwentyFiveDS_236017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 688424747690369) ^ 344212373845184 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 688424747690369) ^ 52955749822336 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 688424747690369) ^ 5255150745728 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 688424747690369) ^ 51447929728 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 688424747690369) ^ 2916843904 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_766253565009377 : Nat.Prime 766253565009377 := by
  apply lucas_primality 766253565009377 (3 : ZMod 766253565009377)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (23, 1), (11551, 1), (90131191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (23, 1), (11551, 1), (90131191, 1)] : List FactorBlock).map factorBlockValue).prod) = 766253565009377 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_23
      · exact prime_oneHundredTwentyFiveDS_11551
      · exact prime_oneHundredTwentyFiveDS_90131191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 766253565009377) ^ 383126782504688 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 766253565009377) ^ 33315372391712 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 766253565009377) ^ 66336556576 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 766253565009377) ^ 8501536 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_829322224245917 : Nat.Prime 829322224245917 := by
  apply lucas_primality 829322224245917 (2 : ZMod 829322224245917)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (59, 1), (224603, 1), (680249, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (59, 1), (224603, 1), (680249, 1)] : List FactorBlock).map factorBlockValue).prod) = 829322224245917 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_23
      · exact prime_oneHundredTwentyFiveDS_59
      · exact prime_oneHundredTwentyFiveDS_224603
      · exact prime_oneHundredTwentyFiveDS_680249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 829322224245917) ^ 414661112122958 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 829322224245917) ^ 36057488010692 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 829322224245917) ^ 14056308885524 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 829322224245917) ^ 3692391572 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 829322224245917) ^ 1219145084 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_988350429794713 : Nat.Prime 988350429794713 := by
  apply lucas_primality 988350429794713 (5 : ZMod 988350429794713)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (1657, 1), (16843, 1), (1475563, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (1657, 1), (16843, 1), (1475563, 1)] : List FactorBlock).map factorBlockValue).prod) = 988350429794713 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_1657
      · exact prime_oneHundredTwentyFiveDS_16843
      · exact prime_oneHundredTwentyFiveDS_1475563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 988350429794713) ^ 494175214897356 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 988350429794713) ^ 329450143264904 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 988350429794713) ^ 596469782616 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 988350429794713) ^ 58680189384 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 988350429794713) ^ 669812424 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_1462436978901211 : Nat.Prime 1462436978901211 := by
  apply lucas_primality 1462436978901211 (2 : ZMod 1462436978901211)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (13, 1), (19, 1), (65786638727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (13, 1), (19, 1), (65786638727, 1)] : List FactorBlock).map factorBlockValue).prod) = 1462436978901211 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_5
      · exact prime_oneHundredTwentyFiveDS_13
      · exact prime_oneHundredTwentyFiveDS_19
      · exact prime_oneHundredTwentyFiveDS_65786638727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1462436978901211) ^ 731218489450605 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1462436978901211) ^ 487478992967070 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1462436978901211) ^ 292487395780242 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1462436978901211) ^ 112495152223170 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1462436978901211) ^ 76970367310590 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1462436978901211) ^ 22230 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_1769274945074029 : Nat.Prime 1769274945074029 := by
  apply lucas_primality 1769274945074029 (2 : ZMod 1769274945074029)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (21062796965167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (21062796965167, 1)] : List FactorBlock).map factorBlockValue).prod) = 1769274945074029 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_7
      · exact prime_oneHundredTwentyFiveDS_21062796965167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1769274945074029) ^ 884637472537014 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1769274945074029) ^ 589758315024676 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1769274945074029) ^ 252753563582004 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1769274945074029) ^ 84 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_1957866224632639 : Nat.Prime 1957866224632639 := by
  apply lucas_primality 1957866224632639 (3 : ZMod 1957866224632639)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (227, 1), (967, 1), (12163, 1), (122219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (227, 1), (967, 1), (12163, 1), (122219, 1)] : List FactorBlock).map factorBlockValue).prod) = 1957866224632639 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_227
      · exact prime_oneHundredTwentyFiveDS_967
      · exact prime_oneHundredTwentyFiveDS_12163
      · exact prime_oneHundredTwentyFiveDS_122219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1957866224632639) ^ 978933112316319 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1957866224632639) ^ 652622074877546 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1957866224632639) ^ 8624961341994 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1957866224632639) ^ 2024680687314 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1957866224632639) ^ 160969022826 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1957866224632639) ^ 16019327802 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_2172513742062107 : Nat.Prime 2172513742062107 := by
  apply lucas_primality 2172513742062107 (2 : ZMod 2172513742062107)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (8369, 1), (129795300637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (8369, 1), (129795300637, 1)] : List FactorBlock).map factorBlockValue).prod) = 2172513742062107 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_8369
      · exact prime_oneHundredTwentyFiveDS_129795300637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2172513742062107) ^ 1086256871031053 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 2172513742062107) ^ 259590601274 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 2172513742062107) ^ 16738 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_2678779572134891 : Nat.Prime 2678779572134891 := by
  apply lucas_primality 2678779572134891 (6 : ZMod 2678779572134891)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (38833, 1), (985457719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (38833, 1), (985457719, 1)] : List FactorBlock).map factorBlockValue).prod) = 2678779572134891 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_5
      · exact prime_oneHundredTwentyFiveDS_7
      · exact prime_oneHundredTwentyFiveDS_38833
      · exact prime_oneHundredTwentyFiveDS_985457719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 2678779572134891) ^ 1339389786067445 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (6 : ZMod 2678779572134891) ^ 535755914426978 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (6 : ZMod 2678779572134891) ^ 382682796019270 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (6 : ZMod 2678779572134891) ^ 68982040330 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (6 : ZMod 2678779572134891) ^ 2718310 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_2843528309867111 : Nat.Prime 2843528309867111 := by
  apply lucas_primality 2843528309867111 (11 : ZMod 2843528309867111)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (154991, 1), (1834640921, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (154991, 1), (1834640921, 1)] : List FactorBlock).map factorBlockValue).prod) = 2843528309867111 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_5
      · exact prime_oneHundredTwentyFiveDS_154991
      · exact prime_oneHundredTwentyFiveDS_1834640921
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 2843528309867111) ^ 1421764154933555 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (11 : ZMod 2843528309867111) ^ 568705661973422 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (11 : ZMod 2843528309867111) ^ 18346409210 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (11 : ZMod 2843528309867111) ^ 1549910 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_3141663309578149 : Nat.Prime 3141663309578149 := by
  apply lucas_primality 3141663309578149 (6 : ZMod 3141663309578149)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (733, 1), (357169544063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (733, 1), (357169544063, 1)] : List FactorBlock).map factorBlockValue).prod) = 3141663309578149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_733
      · exact prime_oneHundredTwentyFiveDS_357169544063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 3141663309578149) ^ 1570831654789074 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (6 : ZMod 3141663309578149) ^ 1047221103192716 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (6 : ZMod 3141663309578149) ^ 4286034528756 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (6 : ZMod 3141663309578149) ^ 8796 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_3662695922899327 : Nat.Prime 3662695922899327 := by
  apply lucas_primality 3662695922899327 (3 : ZMod 3662695922899327)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (61, 1), (18979, 1), (527286259, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (61, 1), (18979, 1), (527286259, 1)] : List FactorBlock).map factorBlockValue).prod) = 3662695922899327 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_61
      · exact prime_oneHundredTwentyFiveDS_18979
      · exact prime_oneHundredTwentyFiveDS_527286259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3662695922899327) ^ 1831347961449663 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 3662695922899327) ^ 1220898640966442 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 3662695922899327) ^ 60044195457366 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 3662695922899327) ^ 192986770794 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 3662695922899327) ^ 6946314 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_6164237299465429 : Nat.Prime 6164237299465429 := by
  apply lucas_primality 6164237299465429 (2 : ZMod 6164237299465429)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (513686441622119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (513686441622119, 1)] : List FactorBlock).map factorBlockValue).prod) = 6164237299465429 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_513686441622119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 6164237299465429) ^ 3082118649732714 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 6164237299465429) ^ 2054745766488476 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 6164237299465429) ^ 12 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_7081451319513653 : Nat.Prime 7081451319513653 := by
  apply lucas_primality 7081451319513653 (2 : ZMod 7081451319513653)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13151, 1), (134618114963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13151, 1), (134618114963, 1)] : List FactorBlock).map factorBlockValue).prod) = 7081451319513653 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_13151
      · exact prime_oneHundredTwentyFiveDS_134618114963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 7081451319513653) ^ 3540725659756826 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 7081451319513653) ^ 538472459852 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 7081451319513653) ^ 52604 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_7106882965517941 : Nat.Prime 7106882965517941 := by
  apply lucas_primality 7106882965517941 (6 : ZMod 7106882965517941)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (11, 1), (463, 1), (2203, 1), (10556981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (11, 1), (463, 1), (2203, 1), (10556981, 1)] : List FactorBlock).map factorBlockValue).prod) = 7106882965517941 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_5
      · exact prime_oneHundredTwentyFiveDS_11
      · exact prime_oneHundredTwentyFiveDS_463
      · exact prime_oneHundredTwentyFiveDS_2203
      · exact prime_oneHundredTwentyFiveDS_10556981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 7106882965517941) ^ 3553441482758970 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (6 : ZMod 7106882965517941) ^ 2368960988505980 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (6 : ZMod 7106882965517941) ^ 1421376593103588 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (6 : ZMod 7106882965517941) ^ 646080269592540 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (6 : ZMod 7106882965517941) ^ 15349639234380 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (6 : ZMod 7106882965517941) ^ 3226002253980 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (6 : ZMod 7106882965517941) ^ 673192740 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_10887033067808713 : Nat.Prime 10887033067808713 := by
  apply lucas_primality 10887033067808713 (5 : ZMod 10887033067808713)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (453626377825363, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (453626377825363, 1)] : List FactorBlock).map factorBlockValue).prod) = 10887033067808713 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_453626377825363
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 10887033067808713) ^ 5443516533904356 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 10887033067808713) ^ 3629011022602904 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 10887033067808713) ^ 24 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_15894869376766573 : Nat.Prime 15894869376766573 := by
  apply lucas_primality 15894869376766573 (2 : ZMod 15894869376766573)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (59, 1), (6491, 1), (1152897883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (59, 1), (6491, 1), (1152897883, 1)] : List FactorBlock).map factorBlockValue).prod) = 15894869376766573 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_59
      · exact prime_oneHundredTwentyFiveDS_6491
      · exact prime_oneHundredTwentyFiveDS_1152897883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 15894869376766573) ^ 7947434688383286 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 15894869376766573) ^ 5298289792255524 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 15894869376766573) ^ 269404565707908 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 15894869376766573) ^ 2448755103492 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 15894869376766573) ^ 13786884 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_16418199775413719 : Nat.Prime 16418199775413719 := by
  apply lucas_primality 16418199775413719 (17 : ZMod 16418199775413719)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 1), (281, 1), (679392525673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 1), (281, 1), (679392525673, 1)] : List FactorBlock).map factorBlockValue).prod) = 16418199775413719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_43
      · exact prime_oneHundredTwentyFiveDS_281
      · exact prime_oneHundredTwentyFiveDS_679392525673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 16418199775413719) ^ 8209099887706859 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (17 : ZMod 16418199775413719) ^ 381818599428226 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (17 : ZMod 16418199775413719) ^ 58427757207878 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (17 : ZMod 16418199775413719) ^ 24166 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_35191226542465943 : Nat.Prime 35191226542465943 := by
  apply lucas_primality 35191226542465943 (5 : ZMod 35191226542465943)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (28541, 1), (47423310787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (28541, 1), (47423310787, 1)] : List FactorBlock).map factorBlockValue).prod) = 35191226542465943 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_13
      · exact prime_oneHundredTwentyFiveDS_28541
      · exact prime_oneHundredTwentyFiveDS_47423310787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 35191226542465943) ^ 17595613271232971 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 35191226542465943) ^ 2707017426343534 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 35191226542465943) ^ 1233006080462 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 35191226542465943) ^ 742066 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_40938186534773471 : Nat.Prime 40938186534773471 := by
  apply lucas_primality 40938186534773471 (11 : ZMod 40938186534773471)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (41, 1), (761, 1), (31379, 1), (4181393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (41, 1), (761, 1), (31379, 1), (4181393, 1)] : List FactorBlock).map factorBlockValue).prod) = 40938186534773471 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_5
      · exact prime_oneHundredTwentyFiveDS_41
      · exact prime_oneHundredTwentyFiveDS_761
      · exact prime_oneHundredTwentyFiveDS_31379
      · exact prime_oneHundredTwentyFiveDS_4181393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 40938186534773471) ^ 20469093267386735 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (11 : ZMod 40938186534773471) ^ 8187637306954694 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (11 : ZMod 40938186534773471) ^ 998492354506670 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (11 : ZMod 40938186534773471) ^ 53795251688270 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (11 : ZMod 40938186534773471) ^ 1304636429930 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (11 : ZMod 40938186534773471) ^ 9790561790 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_44106504087195793 : Nat.Prime 44106504087195793 := by
  apply lucas_primality 44106504087195793 (7 : ZMod 44106504087195793)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 4), (11, 1), (67, 1), (4289, 1), (10766489, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 4), (11, 1), (67, 1), (4289, 1), (10766489, 1)] : List FactorBlock).map factorBlockValue).prod) = 44106504087195793 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_11
      · exact prime_oneHundredTwentyFiveDS_67
      · exact prime_oneHundredTwentyFiveDS_4289
      · exact prime_oneHundredTwentyFiveDS_10766489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 44106504087195793) ^ 22053252043597896 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (7 : ZMod 44106504087195793) ^ 14702168029065264 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (7 : ZMod 44106504087195793) ^ 4009682189745072 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (7 : ZMod 44106504087195793) ^ 658306031152176 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (7 : ZMod 44106504087195793) ^ 10283633501328 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (7 : ZMod 44106504087195793) ^ 4096646928 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_47327626420465679 : Nat.Prime 47327626420465679 := by
  apply lucas_primality 47327626420465679 (7 : ZMod 47327626420465679)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (787, 1), (2797, 1), (1535746343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (787, 1), (2797, 1), (1535746343, 1)] : List FactorBlock).map factorBlockValue).prod) = 47327626420465679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_7
      · exact prime_oneHundredTwentyFiveDS_787
      · exact prime_oneHundredTwentyFiveDS_2797
      · exact prime_oneHundredTwentyFiveDS_1535746343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 47327626420465679) ^ 23663813210232839 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (7 : ZMod 47327626420465679) ^ 6761089488637954 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (7 : ZMod 47327626420465679) ^ 60136755299194 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (7 : ZMod 47327626420465679) ^ 16920853207174 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (7 : ZMod 47327626420465679) ^ 30817346 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_55361039681334193 : Nat.Prime 55361039681334193 := by
  apply lucas_primality 55361039681334193 (5 : ZMod 55361039681334193)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (13, 1), (157, 1), (163, 1), (3466828763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (13, 1), (157, 1), (163, 1), (3466828763, 1)] : List FactorBlock).map factorBlockValue).prod) = 55361039681334193 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_13
      · exact prime_oneHundredTwentyFiveDS_157
      · exact prime_oneHundredTwentyFiveDS_163
      · exact prime_oneHundredTwentyFiveDS_3466828763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 55361039681334193) ^ 27680519840667096 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 55361039681334193) ^ 18453679893778064 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 55361039681334193) ^ 4258541513948784 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 55361039681334193) ^ 352618087142256 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 55361039681334193) ^ 339638280253584 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 55361039681334193) ^ 15968784 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_87993771862869487 : Nat.Prime 87993771862869487 := by
  apply lucas_primality 87993771862869487 (3 : ZMod 87993771862869487)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (8863, 1), (30983, 1), (17802263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (8863, 1), (30983, 1), (17802263, 1)] : List FactorBlock).map factorBlockValue).prod) = 87993771862869487 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_8863
      · exact prime_oneHundredTwentyFiveDS_30983
      · exact prime_oneHundredTwentyFiveDS_17802263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 87993771862869487) ^ 43996885931434743 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 87993771862869487) ^ 29331257287623162 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 87993771862869487) ^ 9928215261522 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 87993771862869487) ^ 2840066225442 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 87993771862869487) ^ 4942841922 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_90271424483937779 : Nat.Prime 90271424483937779 := by
  apply lucas_primality 90271424483937779 (2 : ZMod 90271424483937779)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (131, 1), (771643, 1), (446511433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (131, 1), (771643, 1), (446511433, 1)] : List FactorBlock).map factorBlockValue).prod) = 90271424483937779 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_131
      · exact prime_oneHundredTwentyFiveDS_771643
      · exact prime_oneHundredTwentyFiveDS_446511433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 90271424483937779) ^ 45135712241968889 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 90271424483937779) ^ 689094843388838 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 90271424483937779) ^ 116985995446 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 90271424483937779) ^ 202170466 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_91950427801125241 : Nat.Prime 91950427801125241 := by
  apply lucas_primality 91950427801125241 (14 : ZMod 91950427801125241)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (766253565009377, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (766253565009377, 1)] : List FactorBlock).map factorBlockValue).prod) = 91950427801125241 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_5
      · exact prime_oneHundredTwentyFiveDS_766253565009377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 91950427801125241) ^ 45975213900562620 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (14 : ZMod 91950427801125241) ^ 30650142600375080 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (14 : ZMod 91950427801125241) ^ 18390085560225048 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (14 : ZMod 91950427801125241) ^ 120 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_110956271390377723 : Nat.Prime 110956271390377723 := by
  apply lucas_primality 110956271390377723 (2 : ZMod 110956271390377723)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (6164237299465429, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (6164237299465429, 1)] : List FactorBlock).map factorBlockValue).prod) = 110956271390377723 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_6164237299465429
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 110956271390377723) ^ 55478135695188861 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 110956271390377723) ^ 36985423796792574 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 110956271390377723) ^ 18 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_137768808036741779 : Nat.Prime 137768808036741779 := by
  apply lucas_primality 137768808036741779 (2 : ZMod 137768808036741779)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (2857, 1), (72139, 1), (25709711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (2857, 1), (72139, 1), (25709711, 1)] : List FactorBlock).map factorBlockValue).prod) = 137768808036741779 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_13
      · exact prime_oneHundredTwentyFiveDS_2857
      · exact prime_oneHundredTwentyFiveDS_72139
      · exact prime_oneHundredTwentyFiveDS_25709711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 137768808036741779) ^ 68884404018370889 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 137768808036741779) ^ 10597600618210906 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 137768808036741779) ^ 48221493887554 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 137768808036741779) ^ 1909768752502 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 137768808036741779) ^ 5358629198 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_255819697353228889 : Nat.Prime 255819697353228889 := by
  apply lucas_primality 255819697353228889 (14 : ZMod 255819697353228889)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (11, 1), (29, 1), (73, 1), (89, 1), (181, 1), (3157171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (11, 1), (29, 1), (73, 1), (89, 1), (181, 1), (3157171, 1)] : List FactorBlock).map factorBlockValue).prod) = 255819697353228889 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_11
      · exact prime_oneHundredTwentyFiveDS_29
      · exact prime_oneHundredTwentyFiveDS_73
      · exact prime_oneHundredTwentyFiveDS_89
      · exact prime_oneHundredTwentyFiveDS_181
      · exact prime_oneHundredTwentyFiveDS_3157171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 255819697353228889) ^ 127909848676614444 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (14 : ZMod 255819697353228889) ^ 85273232451076296 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (14 : ZMod 255819697353228889) ^ 23256336123020808 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (14 : ZMod 255819697353228889) ^ 8821368874249272 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (14 : ZMod 255819697353228889) ^ 3504379415797656 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (14 : ZMod 255819697353228889) ^ 2874378621946392 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (14 : ZMod 255819697353228889) ^ 1413368493664248 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (14 : ZMod 255819697353228889) ^ 81028141128 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_258268827641370407 : Nat.Prime 258268827641370407 := by
  apply lucas_primality 258268827641370407 (7 : ZMod 258268827641370407)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (19, 1), (138705063180113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (19, 1), (138705063180113, 1)] : List FactorBlock).map factorBlockValue).prod) = 258268827641370407 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_7
      · exact prime_oneHundredTwentyFiveDS_19
      · exact prime_oneHundredTwentyFiveDS_138705063180113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 258268827641370407) ^ 129134413820685203 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (7 : ZMod 258268827641370407) ^ 36895546805910058 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (7 : ZMod 258268827641370407) ^ 13593096191651074 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (7 : ZMod 258268827641370407) ^ 1862 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_402066494964423857 : Nat.Prime 402066494964423857 := by
  apply lucas_primality 402066494964423857 (3 : ZMod 402066494964423857)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 2), (181, 1), (277, 1), (10228771507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 2), (181, 1), (277, 1), (10228771507, 1)] : List FactorBlock).map factorBlockValue).prod) = 402066494964423857 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_7
      · exact prime_oneHundredTwentyFiveDS_181
      · exact prime_oneHundredTwentyFiveDS_277
      · exact prime_oneHundredTwentyFiveDS_10228771507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 402066494964423857) ^ 201033247482211928 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 402066494964423857) ^ 57438070709203408 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 402066494964423857) ^ 2221361850632176 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 402066494964423857) ^ 1451503591929328 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 402066494964423857) ^ 39307408 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_560382108122478911 : Nat.Prime 560382108122478911 := by
  apply lucas_primality 560382108122478911 (11 : ZMod 560382108122478911)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (587, 1), (12451, 1), (7667290643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (587, 1), (12451, 1), (7667290643, 1)] : List FactorBlock).map factorBlockValue).prod) = 560382108122478911 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_5
      · exact prime_oneHundredTwentyFiveDS_587
      · exact prime_oneHundredTwentyFiveDS_12451
      · exact prime_oneHundredTwentyFiveDS_7667290643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 560382108122478911) ^ 280191054061239455 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (11 : ZMod 560382108122478911) ^ 112076421624495782 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (11 : ZMod 560382108122478911) ^ 954654357959930 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (11 : ZMod 560382108122478911) ^ 45006996074410 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (11 : ZMod 560382108122478911) ^ 73087370 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_593456164007251583 : Nat.Prime 593456164007251583 := by
  apply lucas_primality 593456164007251583 (5 : ZMod 593456164007251583)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (4273, 1), (16487, 1), (4211958841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (4273, 1), (16487, 1), (4211958841, 1)] : List FactorBlock).map factorBlockValue).prod) = 593456164007251583 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_4273
      · exact prime_oneHundredTwentyFiveDS_16487
      · exact prime_oneHundredTwentyFiveDS_4211958841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 593456164007251583) ^ 296728082003625791 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 593456164007251583) ^ 138885130823134 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 593456164007251583) ^ 35995400255186 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 593456164007251583) ^ 140897902 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_1076299201028496031 : Nat.Prime 1076299201028496031 := by
  apply lucas_primality 1076299201028496031 (3 : ZMod 1076299201028496031)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (17, 1), (91457, 1), (23075222129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (17, 1), (91457, 1), (23075222129, 1)] : List FactorBlock).map factorBlockValue).prod) = 1076299201028496031 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_5
      · exact prime_oneHundredTwentyFiveDS_17
      · exact prime_oneHundredTwentyFiveDS_91457
      · exact prime_oneHundredTwentyFiveDS_23075222129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1076299201028496031) ^ 538149600514248015 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1076299201028496031) ^ 358766400342832010 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1076299201028496031) ^ 215259840205699206 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1076299201028496031) ^ 63311717707558590 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1076299201028496031) ^ 11768363285790 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1076299201028496031) ^ 46643070 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_1125098511444920107 : Nat.Prime 1125098511444920107 := by
  apply lucas_primality 1125098511444920107 (2 : ZMod 1125098511444920107)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (1599331, 1), (39082261807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (1599331, 1), (39082261807, 1)] : List FactorBlock).map factorBlockValue).prod) = 1125098511444920107 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_1599331
      · exact prime_oneHundredTwentyFiveDS_39082261807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1125098511444920107) ^ 562549255722460053 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1125098511444920107) ^ 375032837148306702 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1125098511444920107) ^ 703480712526 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1125098511444920107) ^ 28787958 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_1820815588908354271 : Nat.Prime 1820815588908354271 := by
  apply lucas_primality 1820815588908354271 (3 : ZMod 1820815588908354271)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (31, 1), (1957866224632639, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (31, 1), (1957866224632639, 1)] : List FactorBlock).map factorBlockValue).prod) = 1820815588908354271 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_5
      · exact prime_oneHundredTwentyFiveDS_31
      · exact prime_oneHundredTwentyFiveDS_1957866224632639
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1820815588908354271) ^ 910407794454177135 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1820815588908354271) ^ 606938529636118090 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1820815588908354271) ^ 364163117781670854 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1820815588908354271) ^ 58735986738979170 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 1820815588908354271) ^ 930 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_2410219617571552777 : Nat.Prime 2410219617571552777 := by
  apply lucas_primality 2410219617571552777 (10 : ZMod 2410219617571552777)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (19, 1), (47, 1), (10223538369013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (19, 1), (47, 1), (10223538369013, 1)] : List FactorBlock).map factorBlockValue).prod) = 2410219617571552777 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_11
      · exact prime_oneHundredTwentyFiveDS_19
      · exact prime_oneHundredTwentyFiveDS_47
      · exact prime_oneHundredTwentyFiveDS_10223538369013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 2410219617571552777) ^ 1205109808785776388 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (10 : ZMod 2410219617571552777) ^ 803406539190517592 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (10 : ZMod 2410219617571552777) ^ 219110874324686616 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (10 : ZMod 2410219617571552777) ^ 126853664082713304 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (10 : ZMod 2410219617571552777) ^ 51281268458969208 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (10 : ZMod 2410219617571552777) ^ 235752 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_3560736984043509499 : Nat.Prime 3560736984043509499 := by
  apply lucas_primality 3560736984043509499 (2 : ZMod 3560736984043509499)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (593456164007251583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (593456164007251583, 1)] : List FactorBlock).map factorBlockValue).prod) = 3560736984043509499 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_593456164007251583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3560736984043509499) ^ 1780368492021754749 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 3560736984043509499) ^ 1186912328014503166 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 3560736984043509499) ^ 6 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_5882475003792681247 : Nat.Prime 5882475003792681247 := by
  apply lucas_primality 5882475003792681247 (5 : ZMod 5882475003792681247)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (136360163, 1), (7189874807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (136360163, 1), (7189874807, 1)] : List FactorBlock).map factorBlockValue).prod) = 5882475003792681247 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_136360163
      · exact prime_oneHundredTwentyFiveDS_7189874807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 5882475003792681247) ^ 2941237501896340623 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 5882475003792681247) ^ 1960825001264227082 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 5882475003792681247) ^ 43139248842 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 5882475003792681247) ^ 818160978 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_8724989038175689211 : Nat.Prime 8724989038175689211 := by
  apply lucas_primality 8724989038175689211 (2 : ZMod 8724989038175689211)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (29, 1), (16381, 1), (1836650332529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (29, 1), (16381, 1), (1836650332529, 1)] : List FactorBlock).map factorBlockValue).prod) = 8724989038175689211 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_5
      · exact prime_oneHundredTwentyFiveDS_29
      · exact prime_oneHundredTwentyFiveDS_16381
      · exact prime_oneHundredTwentyFiveDS_1836650332529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8724989038175689211) ^ 4362494519087844605 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 8724989038175689211) ^ 1744997807635137842 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 8724989038175689211) ^ 300861690971575490 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 8724989038175689211) ^ 532628596433410 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 8724989038175689211) ^ 4750490 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_9080926330120270333 : Nat.Prime 9080926330120270333 := by
  apply lucas_primality 9080926330120270333 (2 : ZMod 9080926330120270333)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (113, 1), (191, 1), (5008861874381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (113, 1), (191, 1), (5008861874381, 1)] : List FactorBlock).map factorBlockValue).prod) = 9080926330120270333 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_7
      · exact prime_oneHundredTwentyFiveDS_113
      · exact prime_oneHundredTwentyFiveDS_191
      · exact prime_oneHundredTwentyFiveDS_5008861874381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9080926330120270333) ^ 4540463165060135166 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 9080926330120270333) ^ 3026975443373423444 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 9080926330120270333) ^ 1297275190017181476 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 9080926330120270333) ^ 80362179912568764 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 9080926330120270333) ^ 47544116911624452 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 9080926330120270333) ^ 1812972 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_14461317705429316663 : Nat.Prime 14461317705429316663 := by
  apply lucas_primality 14461317705429316663 (3 : ZMod 14461317705429316663)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2410219617571552777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2410219617571552777, 1)] : List FactorBlock).map factorBlockValue).prod) = 14461317705429316663 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_2410219617571552777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 14461317705429316663) ^ 7230658852714658331 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 14461317705429316663) ^ 4820439235143105554 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 14461317705429316663) ^ 6 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_16120895465107774039 : Nat.Prime 16120895465107774039 := by
  apply lucas_primality 16120895465107774039 (3 : ZMod 16120895465107774039)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (59, 1), (2678779572134891, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (59, 1), (2678779572134891, 1)] : List FactorBlock).map factorBlockValue).prod) = 16120895465107774039 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_17
      · exact prime_oneHundredTwentyFiveDS_59
      · exact prime_oneHundredTwentyFiveDS_2678779572134891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 16120895465107774039) ^ 8060447732553887019 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 16120895465107774039) ^ 5373631821702591346 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 16120895465107774039) ^ 948287968535751414 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 16120895465107774039) ^ 273235516357758882 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 16120895465107774039) ^ 6018 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_16435385789447851757 : Nat.Prime 16435385789447851757 := by
  apply lucas_primality 16435385789447851757 (2 : ZMod 16435385789447851757)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (29, 1), (317, 1), (7477, 1), (2599006913, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (29, 1), (317, 1), (7477, 1), (2599006913, 1)] : List FactorBlock).map factorBlockValue).prod) = 16435385789447851757 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_23
      · exact prime_oneHundredTwentyFiveDS_29
      · exact prime_oneHundredTwentyFiveDS_317
      · exact prime_oneHundredTwentyFiveDS_7477
      · exact prime_oneHundredTwentyFiveDS_2599006913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 16435385789447851757) ^ 8217692894723925878 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 16435385789447851757) ^ 714581990845558772 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 16435385789447851757) ^ 566737441015443164 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 16435385789447851757) ^ 51846642868920668 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 16435385789447851757) ^ 2198125690711228 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 16435385789447851757) ^ 6323717612 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_18480303439678869149 : Nat.Prime 18480303439678869149 := by
  apply lucas_primality 18480303439678869149 (2 : ZMod 18480303439678869149)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 1), (143385917, 1), (1111078159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 1), (143385917, 1), (1111078159, 1)] : List FactorBlock).map factorBlockValue).prod) = 18480303439678869149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_29
      · exact prime_oneHundredTwentyFiveDS_143385917
      · exact prime_oneHundredTwentyFiveDS_1111078159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 18480303439678869149) ^ 9240151719839434574 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 18480303439678869149) ^ 637251842747547212 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 18480303439678869149) ^ 128885066444 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 18480303439678869149) ^ 16632766372 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_19096906877256609199 : Nat.Prime 19096906877256609199 := by
  apply lucas_primality 19096906877256609199 (6 : ZMod 19096906877256609199)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (53, 1), (6697657, 1), (426966413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (53, 1), (6697657, 1), (426966413, 1)] : List FactorBlock).map factorBlockValue).prod) = 19096906877256609199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_7
      · exact prime_oneHundredTwentyFiveDS_53
      · exact prime_oneHundredTwentyFiveDS_6697657
      · exact prime_oneHundredTwentyFiveDS_426966413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 19096906877256609199) ^ 9548453438628304599 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (6 : ZMod 19096906877256609199) ^ 6365635625752203066 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (6 : ZMod 19096906877256609199) ^ 2728129553893801314 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (6 : ZMod 19096906877256609199) ^ 360318997684086966 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (6 : ZMod 19096906877256609199) ^ 2851281706014 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (6 : ZMod 19096906877256609199) ^ 44726953446 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_23416642697890425413 : Nat.Prime 23416642697890425413 := by
  apply lucas_primality 23416642697890425413 (2 : ZMod 23416642697890425413)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (13, 1), (40938186534773471, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (13, 1), (40938186534773471, 1)] : List FactorBlock).map factorBlockValue).prod) = 23416642697890425413 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_11
      · exact prime_oneHundredTwentyFiveDS_13
      · exact prime_oneHundredTwentyFiveDS_40938186534773471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 23416642697890425413) ^ 11708321348945212706 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 23416642697890425413) ^ 2128785699808220492 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 23416642697890425413) ^ 1801280207530032724 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 23416642697890425413) ^ 572 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_28148983514129501251 : Nat.Prime 28148983514129501251 := by
  apply lucas_primality 28148983514129501251 (17 : ZMod 28148983514129501251)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 4), (37, 1), (3307, 1), (61347310813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 4), (37, 1), (3307, 1), (61347310813, 1)] : List FactorBlock).map factorBlockValue).prod) = 28148983514129501251 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_5
      · exact prime_oneHundredTwentyFiveDS_37
      · exact prime_oneHundredTwentyFiveDS_3307
      · exact prime_oneHundredTwentyFiveDS_61347310813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 28148983514129501251) ^ 14074491757064750625 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (17 : ZMod 28148983514129501251) ^ 9382994504709833750 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (17 : ZMod 28148983514129501251) ^ 5629796702825900250 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (17 : ZMod 28148983514129501251) ^ 760783338219716250 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (17 : ZMod 28148983514129501251) ^ 8511939375303750 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (17 : ZMod 28148983514129501251) ^ 458846250 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_36960606879357738299 : Nat.Prime 36960606879357738299 := by
  apply lucas_primality 36960606879357738299 (2 : ZMod 36960606879357738299)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (18480303439678869149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (18480303439678869149, 1)] : List FactorBlock).map factorBlockValue).prod) = 36960606879357738299 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_18480303439678869149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 36960606879357738299) ^ 18480303439678869149 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 36960606879357738299) ^ 2 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_52983531609217552957 : Nat.Prime 52983531609217552957 := by
  apply lucas_primality 52983531609217552957 (5 : ZMod 52983531609217552957)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (2063, 1), (15269, 1), (140168308879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (2063, 1), (15269, 1), (140168308879, 1)] : List FactorBlock).map factorBlockValue).prod) = 52983531609217552957 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_2063
      · exact prime_oneHundredTwentyFiveDS_15269
      · exact prime_oneHundredTwentyFiveDS_140168308879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 52983531609217552957) ^ 26491765804608776478 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 52983531609217552957) ^ 17661177203072517652 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 52983531609217552957) ^ 25682758899281412 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 52983531609217552957) ^ 3470006654608524 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 52983531609217552957) ^ 377999364 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_53192807511908228833 : Nat.Prime 53192807511908228833 := by
  apply lucas_primality 53192807511908228833 (5 : ZMod 53192807511908228833)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (31, 1), (131, 1), (136442192788897, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (31, 1), (131, 1), (136442192788897, 1)] : List FactorBlock).map factorBlockValue).prod) = 53192807511908228833 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_31
      · exact prime_oneHundredTwentyFiveDS_131
      · exact prime_oneHundredTwentyFiveDS_136442192788897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 53192807511908228833) ^ 26596403755954114416 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 53192807511908228833) ^ 17730935837302742944 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 53192807511908228833) ^ 1715897016513168672 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 53192807511908228833) ^ 406051965739757472 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 53192807511908228833) ^ 389856 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_64314289616386246967 : Nat.Prime 64314289616386246967 := by
  apply lucas_primality 64314289616386246967 (5 : ZMod 64314289616386246967)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1871, 1), (594179, 1), (28925867687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1871, 1), (594179, 1), (28925867687, 1)] : List FactorBlock).map factorBlockValue).prod) = 64314289616386246967 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_1871
      · exact prime_oneHundredTwentyFiveDS_594179
      · exact prime_oneHundredTwentyFiveDS_28925867687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 64314289616386246967) ^ 32157144808193123483 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 64314289616386246967) ^ 34374286272787946 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 64314289616386246967) ^ 108240596884754 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 64314289616386246967) ^ 2223417818 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_89886276795292550843 : Nat.Prime 89886276795292550843 := by
  apply lucas_primality 89886276795292550843 (2 : ZMod 89886276795292550843)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1417261, 1), (31711264472561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1417261, 1), (31711264472561, 1)] : List FactorBlock).map factorBlockValue).prod) = 89886276795292550843 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_1417261
      · exact prime_oneHundredTwentyFiveDS_31711264472561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 89886276795292550843) ^ 44943138397646275421 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 89886276795292550843) ^ 63422528945122 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 89886276795292550843) ^ 2834522 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_101928612273723395863 : Nat.Prime 101928612273723395863 := by
  apply lucas_primality 101928612273723395863 (6 : ZMod 101928612273723395863)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 3), (379, 1), (20402133931279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 3), (379, 1), (20402133931279, 1)] : List FactorBlock).map factorBlockValue).prod) = 101928612273723395863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_13
      · exact prime_oneHundredTwentyFiveDS_379
      · exact prime_oneHundredTwentyFiveDS_20402133931279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 101928612273723395863) ^ 50964306136861697931 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (6 : ZMod 101928612273723395863) ^ 33976204091241131954 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (6 : ZMod 101928612273723395863) ^ 7840662482594107374 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (6 : ZMod 101928612273723395863) ^ 268940929482119778 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (6 : ZMod 101928612273723395863) ^ 4995978 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_104179562653956463067 : Nat.Prime 104179562653956463067 := by
  apply lucas_primality 104179562653956463067 (2 : ZMod 104179562653956463067)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1181, 1), (44106504087195793, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1181, 1), (44106504087195793, 1)] : List FactorBlock).map factorBlockValue).prod) = 104179562653956463067 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_1181
      · exact prime_oneHundredTwentyFiveDS_44106504087195793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 104179562653956463067) ^ 52089781326978231533 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 104179562653956463067) ^ 88213008174391586 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 104179562653956463067) ^ 2362 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_106822109521305284971 : Nat.Prime 106822109521305284971 := by
  apply lucas_primality 106822109521305284971 (2 : ZMod 106822109521305284971)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (3560736984043509499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (3560736984043509499, 1)] : List FactorBlock).map factorBlockValue).prod) = 106822109521305284971 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_5
      · exact prime_oneHundredTwentyFiveDS_3560736984043509499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 106822109521305284971) ^ 53411054760652642485 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 106822109521305284971) ^ 35607369840435094990 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 106822109521305284971) ^ 21364421904261056994 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 106822109521305284971) ^ 30 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_131112298310369625589 : Nat.Prime 131112298310369625589 := by
  apply lucas_primality 131112298310369625589 (6 : ZMod 131112298310369625589)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (59333, 1), (184147520927603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (59333, 1), (184147520927603, 1)] : List FactorBlock).map factorBlockValue).prod) = 131112298310369625589 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_59333
      · exact prime_oneHundredTwentyFiveDS_184147520927603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 131112298310369625589) ^ 65556149155184812794 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (6 : ZMod 131112298310369625589) ^ 43704099436789875196 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (6 : ZMod 131112298310369625589) ^ 2209770251131236 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (6 : ZMod 131112298310369625589) ^ 711996 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_192011102662663881139 : Nat.Prime 192011102662663881139 := by
  apply lucas_primality 192011102662663881139 (2 : ZMod 192011102662663881139)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 2), (577, 1), (3433231, 1), (44749589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 2), (577, 1), (3433231, 1), (44749589, 1)] : List FactorBlock).map factorBlockValue).prod) = 192011102662663881139 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_19
      · exact prime_oneHundredTwentyFiveDS_577
      · exact prime_oneHundredTwentyFiveDS_3433231
      · exact prime_oneHundredTwentyFiveDS_44749589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 192011102662663881139) ^ 96005551331331940569 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 192011102662663881139) ^ 64003700887554627046 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 192011102662663881139) ^ 10105847508561256902 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 192011102662663881139) ^ 332774874631999794 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 192011102662663881139) ^ 55927230839598 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 192011102662663881139) ^ 4290790305642 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_192528784278454382173 : Nat.Prime 192528784278454382173 := by
  apply lucas_primality 192528784278454382173 (11 : ZMod 192528784278454382173)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (113, 1), (47327626420465679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (113, 1), (47327626420465679, 1)] : List FactorBlock).map factorBlockValue).prod) = 192528784278454382173 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_113
      · exact prime_oneHundredTwentyFiveDS_47327626420465679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 192528784278454382173) ^ 96264392139227191086 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (11 : ZMod 192528784278454382173) ^ 64176261426151460724 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (11 : ZMod 192528784278454382173) ^ 1703794551136764444 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (11 : ZMod 192528784278454382173) ^ 4068 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_235391415792429114277 : Nat.Prime 235391415792429114277 := by
  apply lucas_primality 235391415792429114277 (2 : ZMod 235391415792429114277)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11087, 1), (1769274945074029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11087, 1), (1769274945074029, 1)] : List FactorBlock).map factorBlockValue).prod) = 235391415792429114277 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_11087
      · exact prime_oneHundredTwentyFiveDS_1769274945074029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 235391415792429114277) ^ 117695707896214557138 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 235391415792429114277) ^ 78463805264143038092 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 235391415792429114277) ^ 21231299340888348 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 235391415792429114277) ^ 133044 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_238591027982204845399 : Nat.Prime 238591027982204845399 := by
  apply lucas_primality 238591027982204845399 (6 : ZMod 238591027982204845399)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (1453, 1), (829322224245917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (1453, 1), (829322224245917, 1)] : List FactorBlock).map factorBlockValue).prod) = 238591027982204845399 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_11
      · exact prime_oneHundredTwentyFiveDS_1453
      · exact prime_oneHundredTwentyFiveDS_829322224245917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 238591027982204845399) ^ 119295513991102422699 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (6 : ZMod 238591027982204845399) ^ 79530342660734948466 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (6 : ZMod 238591027982204845399) ^ 21690093452927713218 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (6 : ZMod 238591027982204845399) ^ 164205800400691566 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (6 : ZMod 238591027982204845399) ^ 287694 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_633940864394929895207 : Nat.Prime 633940864394929895207 := by
  apply lucas_primality 633940864394929895207 (5 : ZMod 633940864394929895207)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 2), (17, 1), (5469559, 1), (20171157229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 2), (17, 1), (5469559, 1), (20171157229, 1)] : List FactorBlock).map factorBlockValue).prod) = 633940864394929895207 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_13
      · exact prime_oneHundredTwentyFiveDS_17
      · exact prime_oneHundredTwentyFiveDS_5469559
      · exact prime_oneHundredTwentyFiveDS_20171157229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 633940864394929895207) ^ 316970432197464947603 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 633940864394929895207) ^ 48764681876533068862 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 633940864394929895207) ^ 37290639082054699718 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 633940864394929895207) ^ 115903469437834 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 633940864394929895207) ^ 31428086014 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_768044410650655524557 : Nat.Prime 768044410650655524557 := by
  apply lucas_primality 768044410650655524557 (2 : ZMod 768044410650655524557)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (192011102662663881139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (192011102662663881139, 1)] : List FactorBlock).map factorBlockValue).prod) = 768044410650655524557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_192011102662663881139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 768044410650655524557) ^ 384022205325327762278 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 768044410650655524557) ^ 4 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_877597476325376642987 : Nat.Prime 877597476325376642987 := by
  apply lucas_primality 877597476325376642987 (2 : ZMod 877597476325376642987)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1699, 1), (258268827641370407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1699, 1), (258268827641370407, 1)] : List FactorBlock).map factorBlockValue).prod) = 877597476325376642987 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_1699
      · exact prime_oneHundredTwentyFiveDS_258268827641370407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 877597476325376642987) ^ 438798738162688321493 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 877597476325376642987) ^ 516537655282740814 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 877597476325376642987) ^ 3398 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_954948171737163551917 : Nat.Prime 954948171737163551917 := by
  apply lucas_primality 954948171737163551917 (2 : ZMod 954948171737163551917)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (37, 1), (131, 1), (16418199775413719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (37, 1), (131, 1), (16418199775413719, 1)] : List FactorBlock).map factorBlockValue).prod) = 954948171737163551917 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_37
      · exact prime_oneHundredTwentyFiveDS_131
      · exact prime_oneHundredTwentyFiveDS_16418199775413719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 954948171737163551917) ^ 477474085868581775958 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 954948171737163551917) ^ 318316057245721183972 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 954948171737163551917) ^ 25809410046950366268 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 954948171737163551917) ^ 7289680700283691236 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 954948171737163551917) ^ 58164 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_1081687868363620552253 : Nat.Prime 1081687868363620552253 := by
  apply lucas_primality 1081687868363620552253 (2 : ZMod 1081687868363620552253)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (71, 1), (199, 1), (52864081, 1), (362051087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (71, 1), (199, 1), (52864081, 1), (362051087, 1)] : List FactorBlock).map factorBlockValue).prod) = 1081687868363620552253 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_71
      · exact prime_oneHundredTwentyFiveDS_199
      · exact prime_oneHundredTwentyFiveDS_52864081
      · exact prime_oneHundredTwentyFiveDS_362051087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1081687868363620552253) ^ 540843934181810276126 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1081687868363620552253) ^ 15235040399487613412 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1081687868363620552253) ^ 5435617428962917348 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1081687868363620552253) ^ 20461679232892 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1081687868363620552253) ^ 2987666401796 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_2307642263509371299503 : Nat.Prime 2307642263509371299503 := by
  apply lucas_primality 2307642263509371299503 (5 : ZMod 2307642263509371299503)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (59, 1), (77041, 1), (2729490688553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (59, 1), (77041, 1), (2729490688553, 1)] : List FactorBlock).map factorBlockValue).prod) = 2307642263509371299503 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_31
      · exact prime_oneHundredTwentyFiveDS_59
      · exact prime_oneHundredTwentyFiveDS_77041
      · exact prime_oneHundredTwentyFiveDS_2729490688553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2307642263509371299503) ^ 1153821131754685649751 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 2307642263509371299503) ^ 769214087836457099834 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 2307642263509371299503) ^ 74440073016431332242 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 2307642263509371299503) ^ 39112580737446971178 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 2307642263509371299503) ^ 29953430816180622 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 2307642263509371299503) ^ 845447934 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_2458234550212487461699 : Nat.Prime 2458234550212487461699 := by
  apply lucas_primality 2458234550212487461699 (7 : ZMod 2458234550212487461699)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1019, 1), (402066494964423857, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1019, 1), (402066494964423857, 1)] : List FactorBlock).map factorBlockValue).prod) = 2458234550212487461699 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_1019
      · exact prime_oneHundredTwentyFiveDS_402066494964423857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 2458234550212487461699) ^ 1229117275106243730849 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (7 : ZMod 2458234550212487461699) ^ 819411516737495820566 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (7 : ZMod 2458234550212487461699) ^ 2412398969786543142 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (7 : ZMod 2458234550212487461699) ^ 6114 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_2594614601358554880617 : Nat.Prime 2594614601358554880617 := by
  apply lucas_primality 2594614601358554880617 (5 : ZMod 2594614601358554880617)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 3), (43, 1), (1049, 1), (20962583569177, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 3), (43, 1), (1049, 1), (20962583569177, 1)] : List FactorBlock).map factorBlockValue).prod) = 2594614601358554880617 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_7
      · exact prime_oneHundredTwentyFiveDS_43
      · exact prime_oneHundredTwentyFiveDS_1049
      · exact prime_oneHundredTwentyFiveDS_20962583569177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2594614601358554880617) ^ 1297307300679277440308 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 2594614601358554880617) ^ 370659228765507840088 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 2594614601358554880617) ^ 60339874450198950712 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 2594614601358554880617) ^ 2473417160494332584 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 2594614601358554880617) ^ 123773608 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_4084763931355547021947 : Nat.Prime 4084763931355547021947 := by
  apply lucas_primality 4084763931355547021947 (3 : ZMod 4084763931355547021947)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (13, 1), (409, 1), (55270627, 1), (330945607, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (13, 1), (409, 1), (55270627, 1), (330945607, 1)] : List FactorBlock).map factorBlockValue).prod) = 4084763931355547021947 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_7
      · exact prime_oneHundredTwentyFiveDS_13
      · exact prime_oneHundredTwentyFiveDS_409
      · exact prime_oneHundredTwentyFiveDS_55270627
      · exact prime_oneHundredTwentyFiveDS_330945607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4084763931355547021947) ^ 2042381965677773510973 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 4084763931355547021947) ^ 1361587977118515673982 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 4084763931355547021947) ^ 583537704479363860278 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 4084763931355547021947) ^ 314212610104272847842 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 4084763931355547021947) ^ 9987197876174931594 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 4084763931355547021947) ^ 73904787281598 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 4084763931355547021947) ^ 12342704797878 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_4407467666864482351709 : Nat.Prime 4407467666864482351709 := by
  apply lucas_primality 4407467666864482351709 (2 : ZMod 4407467666864482351709)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (61931869, 1), (17791598001283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (61931869, 1), (17791598001283, 1)] : List FactorBlock).map factorBlockValue).prod) = 4407467666864482351709 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_61931869
      · exact prime_oneHundredTwentyFiveDS_17791598001283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4407467666864482351709) ^ 2203733833432241175854 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 4407467666864482351709) ^ 71166392005132 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 4407467666864482351709) ^ 247727476 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_4721282934028609449869 : Nat.Prime 4721282934028609449869 := by
  apply lucas_primality 4721282934028609449869 (2 : ZMod 4721282934028609449869)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (137, 1), (4635437, 1), (1858612209943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (137, 1), (4635437, 1), (1858612209943, 1)] : List FactorBlock).map factorBlockValue).prod) = 4721282934028609449869 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_137
      · exact prime_oneHundredTwentyFiveDS_4635437
      · exact prime_oneHundredTwentyFiveDS_1858612209943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4721282934028609449869) ^ 2360641467014304724934 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 4721282934028609449869) ^ 34461919226486200364 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 4721282934028609449869) ^ 1018519491048764 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 4721282934028609449869) ^ 2540219476 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_7389175414818054990001 : Nat.Prime 7389175414818054990001 := by
  apply lucas_primality 7389175414818054990001 (17 : ZMod 7389175414818054990001)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 4), (11, 1), (433, 1), (51712334066891, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 4), (11, 1), (433, 1), (51712334066891, 1)] : List FactorBlock).map factorBlockValue).prod) = 7389175414818054990001 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_5
      · exact prime_oneHundredTwentyFiveDS_11
      · exact prime_oneHundredTwentyFiveDS_433
      · exact prime_oneHundredTwentyFiveDS_51712334066891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 7389175414818054990001) ^ 3694587707409027495000 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (17 : ZMod 7389175414818054990001) ^ 2463058471606018330000 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (17 : ZMod 7389175414818054990001) ^ 1477835082963610998000 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (17 : ZMod 7389175414818054990001) ^ 671743219528914090000 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (17 : ZMod 7389175414818054990001) ^ 17065070242074030000 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (17 : ZMod 7389175414818054990001) ^ 142890000 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_13256972514058216452869 : Nat.Prime 13256972514058216452869 := by
  apply lucas_primality 13256972514058216452869 (2 : ZMod 13256972514058216452869)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (82829821, 1), (40012680077077, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (82829821, 1), (40012680077077, 1)] : List FactorBlock).map factorBlockValue).prod) = 13256972514058216452869 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_82829821
      · exact prime_oneHundredTwentyFiveDS_40012680077077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 13256972514058216452869) ^ 6628486257029108226434 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 13256972514058216452869) ^ 160050720308308 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 13256972514058216452869) ^ 331319284 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_13737519737159276350811 : Nat.Prime 13737519737159276350811 := by
  apply lucas_primality 13737519737159276350811 (2 : ZMod 13737519737159276350811)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (62467, 1), (3141663309578149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (62467, 1), (3141663309578149, 1)] : List FactorBlock).map factorBlockValue).prod) = 13737519737159276350811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_5
      · exact prime_oneHundredTwentyFiveDS_7
      · exact prime_oneHundredTwentyFiveDS_62467
      · exact prime_oneHundredTwentyFiveDS_3141663309578149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 13737519737159276350811) ^ 6868759868579638175405 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 13737519737159276350811) ^ 2747503947431855270162 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 13737519737159276350811) ^ 1962502819594182335830 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 13737519737159276350811) ^ 219916431670470430 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 13737519737159276350811) ^ 4372690 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_16581194394751674652333 : Nat.Prime 16581194394751674652333 := by
  apply lucas_primality 16581194394751674652333 (2 : ZMod 16581194394751674652333)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (41, 1), (383, 1), (87993771862869487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (41, 1), (383, 1), (87993771862869487, 1)] : List FactorBlock).map factorBlockValue).prod) = 16581194394751674652333 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_41
      · exact prime_oneHundredTwentyFiveDS_383
      · exact prime_oneHundredTwentyFiveDS_87993771862869487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 16581194394751674652333) ^ 8290597197375837326166 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 16581194394751674652333) ^ 5527064798250558217444 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 16581194394751674652333) ^ 404419375481748162252 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 16581194394751674652333) ^ 43292935756531787604 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 16581194394751674652333) ^ 188436 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_24561974864329305043703 : Nat.Prime 24561974864329305043703 := by
  apply lucas_primality 24561974864329305043703 (5 : ZMod 24561974864329305043703)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1867, 1), (3583, 1), (5197, 1), (353255916203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1867, 1), (3583, 1), (5197, 1), (353255916203, 1)] : List FactorBlock).map factorBlockValue).prod) = 24561974864329305043703 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_1867
      · exact prime_oneHundredTwentyFiveDS_3583
      · exact prime_oneHundredTwentyFiveDS_5197
      · exact prime_oneHundredTwentyFiveDS_353255916203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 24561974864329305043703) ^ 12280987432164652521851 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 24561974864329305043703) ^ 13155851560969097506 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 24561974864329305043703) ^ 6855142300957104394 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 24561974864329305043703) ^ 4726183348918473166 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 24561974864329305043703) ^ 69530257634 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_37535799675665555308909 : Nat.Prime 37535799675665555308909 := by
  apply lucas_primality 37535799675665555308909 (6 : ZMod 37535799675665555308909)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 5), (17, 1), (137, 1), (307, 1), (2477, 1), (21804470119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 5), (17, 1), (137, 1), (307, 1), (2477, 1), (21804470119, 1)] : List FactorBlock).map factorBlockValue).prod) = 37535799675665555308909 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_17
      · exact prime_oneHundredTwentyFiveDS_137
      · exact prime_oneHundredTwentyFiveDS_307
      · exact prime_oneHundredTwentyFiveDS_2477
      · exact prime_oneHundredTwentyFiveDS_21804470119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 37535799675665555308909) ^ 18767899837832777654454 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (6 : ZMod 37535799675665555308909) ^ 12511933225221851769636 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (6 : ZMod 37535799675665555308909) ^ 2207988216215620900524 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (6 : ZMod 37535799675665555308909) ^ 273983939238434710284 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (6 : ZMod 37535799675665555308909) ^ 122266448454936662244 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (6 : ZMod 37535799675665555308909) ^ 15153734225137487004 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (6 : ZMod 37535799675665555308909) ^ 1721472682932 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_65454120492038679608489 : Nat.Prime 65454120492038679608489 := by
  apply lucas_primality 65454120492038679608489 (3 : ZMod 65454120492038679608489)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17, 1), (89, 1), (572963, 1), (9438033162319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17, 1), (89, 1), (572963, 1), (9438033162319, 1)] : List FactorBlock).map factorBlockValue).prod) = 65454120492038679608489 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_17
      · exact prime_oneHundredTwentyFiveDS_89
      · exact prime_oneHundredTwentyFiveDS_572963
      · exact prime_oneHundredTwentyFiveDS_9438033162319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 65454120492038679608489) ^ 32727060246019339804244 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 65454120492038679608489) ^ 3850242381884628212264 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 65454120492038679608489) ^ 735439556090322242792 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 65454120492038679608489) ^ 114237953396709176 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 65454120492038679608489) ^ 6935144152 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_188615625606691890706661 : Nat.Prime 188615625606691890706661 := by
  apply lucas_primality 188615625606691890706661 (2 : ZMod 188615625606691890706661)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (11, 1), (2046553, 1), (418920864867751, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (11, 1), (2046553, 1), (418920864867751, 1)] : List FactorBlock).map factorBlockValue).prod) = 188615625606691890706661 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_5
      · exact prime_oneHundredTwentyFiveDS_11
      · exact prime_oneHundredTwentyFiveDS_2046553
      · exact prime_oneHundredTwentyFiveDS_418920864867751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 188615625606691890706661) ^ 94307812803345945353330 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 188615625606691890706661) ^ 37723125121338378141332 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 188615625606691890706661) ^ 17146875055153808246060 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 188615625606691890706661) ^ 92162590270905220 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 188615625606691890706661) ^ 450241660 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_335244975325307728377713 : Nat.Prime 335244975325307728377713 := by
  apply lucas_primality 335244975325307728377713 (3 : ZMod 335244975325307728377713)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (29, 1), (332569, 1), (2172513742062107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (29, 1), (332569, 1), (2172513742062107, 1)] : List FactorBlock).map factorBlockValue).prod) = 335244975325307728377713 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_29
      · exact prime_oneHundredTwentyFiveDS_332569
      · exact prime_oneHundredTwentyFiveDS_2172513742062107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 335244975325307728377713) ^ 167622487662653864188856 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 335244975325307728377713) ^ 11560171562941645806128 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 335244975325307728377713) ^ 1008046376316817648 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 335244975325307728377713) ^ 154312016 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_673260444059574328663351 : Nat.Prime 673260444059574328663351 := by
  apply lucas_primality 673260444059574328663351 (3 : ZMod 673260444059574328663351)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (182579, 1), (1059833, 1), (23195491427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (182579, 1), (1059833, 1), (23195491427, 1)] : List FactorBlock).map factorBlockValue).prod) = 673260444059574328663351 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_5
      · exact prime_oneHundredTwentyFiveDS_182579
      · exact prime_oneHundredTwentyFiveDS_1059833
      · exact prime_oneHundredTwentyFiveDS_23195491427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 673260444059574328663351) ^ 336630222029787164331675 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 673260444059574328663351) ^ 224420148019858109554450 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 673260444059574328663351) ^ 134652088811914865732670 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 673260444059574328663351) ^ 3687502089832753650 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 673260444059574328663351) ^ 635251444387534950 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 673260444059574328663351) ^ 29025487396050 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_1895825129731793968582207 : Nat.Prime 1895825129731793968582207 := by
  apply lucas_primality 1895825129731793968582207 (5 : ZMod 1895825129731793968582207)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (19, 1), (1735613543, 1), (1064628001417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (19, 1), (1735613543, 1), (1064628001417, 1)] : List FactorBlock).map factorBlockValue).prod) = 1895825129731793968582207 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_19
      · exact prime_oneHundredTwentyFiveDS_1735613543
      · exact prime_oneHundredTwentyFiveDS_1064628001417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1895825129731793968582207) ^ 947912564865896984291103 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 1895825129731793968582207) ^ 631941709910597989527402 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 1895825129731793968582207) ^ 99780269985883893083274 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 1895825129731793968582207) ^ 1092308329453842 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 1895825129731793968582207) ^ 1780739495118 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_2732629953455979058059581 : Nat.Prime 2732629953455979058059581 := by
  apply lucas_primality 2732629953455979058059581 (2 : ZMod 2732629953455979058059581)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (31, 1), (4407467666864482351709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (31, 1), (4407467666864482351709, 1)] : List FactorBlock).map factorBlockValue).prod) = 2732629953455979058059581 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_5
      · exact prime_oneHundredTwentyFiveDS_31
      · exact prime_oneHundredTwentyFiveDS_4407467666864482351709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2732629953455979058059581) ^ 1366314976727989529029790 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 2732629953455979058059581) ^ 546525990691195811611916 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 2732629953455979058059581) ^ 88149353337289647034180 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 2732629953455979058059581) ^ 620 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_4056193679333940918892249 : Nat.Prime 4056193679333940918892249 := by
  apply lucas_primality 4056193679333940918892249 (11 : ZMod 4056193679333940918892249)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 1), (17, 1), (43, 1), (373, 1), (5557, 1), (9067, 1), (946310957, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 1), (17, 1), (43, 1), (373, 1), (5557, 1), (9067, 1), (946310957, 1)] : List FactorBlock).map factorBlockValue).prod) = 4056193679333940918892249 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_13
      · exact prime_oneHundredTwentyFiveDS_17
      · exact prime_oneHundredTwentyFiveDS_43
      · exact prime_oneHundredTwentyFiveDS_373
      · exact prime_oneHundredTwentyFiveDS_5557
      · exact prime_oneHundredTwentyFiveDS_9067
      · exact prime_oneHundredTwentyFiveDS_946310957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 4056193679333940918892249) ^ 2028096839666970459446124 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (11 : ZMod 4056193679333940918892249) ^ 1352064559777980306297416 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (11 : ZMod 4056193679333940918892249) ^ 312014898410303147607096 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (11 : ZMod 4056193679333940918892249) ^ 238599628196114171699544 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (11 : ZMod 4056193679333940918892249) ^ 94330085565905602764936 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (11 : ZMod 4056193679333940918892249) ^ 10874513885613782624376 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (11 : ZMod 4056193679333940918892249) ^ 729925081758852063864 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (11 : ZMod 4056193679333940918892249) ^ 447357855887718199944 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (11 : ZMod 4056193679333940918892249) ^ 4286322217163064 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_10237140517653976408902757 : Nat.Prime 10237140517653976408902757 := by
  apply lucas_primality 10237140517653976408902757 (2 : ZMod 10237140517653976408902757)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (211, 1), (192528784278454382173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (211, 1), (192528784278454382173, 1)] : List FactorBlock).map factorBlockValue).prod) = 10237140517653976408902757 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_7
      · exact prime_oneHundredTwentyFiveDS_211
      · exact prime_oneHundredTwentyFiveDS_192528784278454382173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 10237140517653976408902757) ^ 5118570258826988204451378 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 10237140517653976408902757) ^ 3412380172551325469634252 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 10237140517653976408902757) ^ 1462448645379139486986108 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 10237140517653976408902757) ^ 48517253638170504307596 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 10237140517653976408902757) ^ 53172 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_37912611727258287182893843 : Nat.Prime 37912611727258287182893843 := by
  apply lucas_primality 37912611727258287182893843 (3 : ZMod 37912611727258287182893843)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (10391, 1), (9540991, 1), (9105076137821, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (10391, 1), (9540991, 1), (9105076137821, 1)] : List FactorBlock).map factorBlockValue).prod) = 37912611727258287182893843 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_7
      · exact prime_oneHundredTwentyFiveDS_10391
      · exact prime_oneHundredTwentyFiveDS_9540991
      · exact prime_oneHundredTwentyFiveDS_9105076137821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 37912611727258287182893843) ^ 18956305863629143591446921 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 37912611727258287182893843) ^ 12637537242419429060964614 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 37912611727258287182893843) ^ 5416087389608326740413406 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 37912611727258287182893843) ^ 3648600878381126665662 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 37912611727258287182893843) ^ 3973655538220116462 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 37912611727258287182893843) ^ 4163898374202 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_68672565294076581523661803 : Nat.Prime 68672565294076581523661803 := by
  apply lucas_primality 68672565294076581523661803 (2 : ZMod 68672565294076581523661803)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (673260444059574328663351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (673260444059574328663351, 1)] : List FactorBlock).map factorBlockValue).prod) = 68672565294076581523661803 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_17
      · exact prime_oneHundredTwentyFiveDS_673260444059574328663351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 68672565294076581523661803) ^ 34336282647038290761830901 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 68672565294076581523661803) ^ 22890855098025527174553934 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 68672565294076581523661803) ^ 4039562664357445971980106 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 68672565294076581523661803) ^ 102 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_82699138507472189949032009 : Nat.Prime 82699138507472189949032009 := by
  apply lucas_primality 82699138507472189949032009 (3 : ZMod 82699138507472189949032009)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (9298811, 1), (244033831, 1), (4555473661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (9298811, 1), (244033831, 1), (4555473661, 1)] : List FactorBlock).map factorBlockValue).prod) = 82699138507472189949032009 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_9298811
      · exact prime_oneHundredTwentyFiveDS_244033831
      · exact prime_oneHundredTwentyFiveDS_4555473661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 82699138507472189949032009) ^ 41349569253736094974516004 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 82699138507472189949032009) ^ 8893517516107402328 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 82699138507472189949032009) ^ 338883908712936568 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 82699138507472189949032009) ^ 18153795776599528 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_131714225056018541389411943 : Nat.Prime 131714225056018541389411943 := by
  apply lucas_primality 131714225056018541389411943 (5 : ZMod 131714225056018541389411943)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (20477, 1), (40241, 1), (495569, 1), (161273666287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (20477, 1), (40241, 1), (495569, 1), (161273666287, 1)] : List FactorBlock).map factorBlockValue).prod) = 131714225056018541389411943 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_20477
      · exact prime_oneHundredTwentyFiveDS_40241
      · exact prime_oneHundredTwentyFiveDS_495569
      · exact prime_oneHundredTwentyFiveDS_161273666287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 131714225056018541389411943) ^ 65857112528009270694705971 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 131714225056018541389411943) ^ 6432300876887168110046 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 131714225056018541389411943) ^ 3273134988097178037062 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 131714225056018541389411943) ^ 265783826381429309318 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 131714225056018541389411943) ^ 816712536451066 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_335109661026877105303673923 : Nat.Prime 335109661026877105303673923 := by
  apply lucas_primality 335109661026877105303673923 (2 : ZMod 335109661026877105303673923)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (18521, 1), (131112298310369625589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (18521, 1), (131112298310369625589, 1)] : List FactorBlock).map factorBlockValue).prod) = 335109661026877105303673923 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_23
      · exact prime_oneHundredTwentyFiveDS_18521
      · exact prime_oneHundredTwentyFiveDS_131112298310369625589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 335109661026877105303673923) ^ 167554830513438552651836961 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 335109661026877105303673923) ^ 111703220342292368434557974 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 335109661026877105303673923) ^ 14569985262038135013203214 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 335109661026877105303673923) ^ 18093497166831008331282 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 335109661026877105303673923) ^ 2555898 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_1191801294458490350313872581 : Nat.Prime 1191801294458490350313872581 := by
  apply lucas_primality 1191801294458490350313872581 (2 : ZMod 1191801294458490350313872581)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (263, 1), (8317, 1), (9080926330120270333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (263, 1), (8317, 1), (9080926330120270333, 1)] : List FactorBlock).map factorBlockValue).prod) = 1191801294458490350313872581 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_5
      · exact prime_oneHundredTwentyFiveDS_263
      · exact prime_oneHundredTwentyFiveDS_8317
      · exact prime_oneHundredTwentyFiveDS_9080926330120270333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1191801294458490350313872581) ^ 595900647229245175156936290 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1191801294458490350313872581) ^ 397267098152830116771290860 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1191801294458490350313872581) ^ 238360258891698070062774516 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1191801294458490350313872581) ^ 4531563857256617301573660 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1191801294458490350313872581) ^ 143297017489297865854740 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 1191801294458490350313872581) ^ 131242260 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_1623992972668712125702419781 : Nat.Prime 1623992972668712125702419781 := by
  apply lucas_primality 1623992972668712125702419781 (6 : ZMod 1623992972668712125702419781)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 1), (11, 1), (37, 1), (7389175414818054990001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 1), (11, 1), (37, 1), (7389175414818054990001, 1)] : List FactorBlock).map factorBlockValue).prod) = 1623992972668712125702419781 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_5
      · exact prime_oneHundredTwentyFiveDS_11
      · exact prime_oneHundredTwentyFiveDS_37
      · exact prime_oneHundredTwentyFiveDS_7389175414818054990001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1623992972668712125702419781) ^ 811996486334356062851209890 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (6 : ZMod 1623992972668712125702419781) ^ 541330990889570708567473260 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (6 : ZMod 1623992972668712125702419781) ^ 324798594533742425140483956 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (6 : ZMod 1623992972668712125702419781) ^ 147635724788064738700219980 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (6 : ZMod 1623992972668712125702419781) ^ 43891701964019246640605940 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (6 : ZMod 1623992972668712125702419781) ^ 219780 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_2273590161736196975983387693 : Nat.Prime 2273590161736196975983387693 := by
  apply lucas_primality 2273590161736196975983387693 (2 : ZMod 2273590161736196975983387693)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (7, 1), (11, 1), (37, 1), (7389175414818054990001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (7, 1), (11, 1), (37, 1), (7389175414818054990001, 1)] : List FactorBlock).map factorBlockValue).prod) = 2273590161736196975983387693 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_7
      · exact prime_oneHundredTwentyFiveDS_11
      · exact prime_oneHundredTwentyFiveDS_37
      · exact prime_oneHundredTwentyFiveDS_7389175414818054990001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2273590161736196975983387693) ^ 1136795080868098487991693846 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 2273590161736196975983387693) ^ 757863387245398991994462564 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 2273590161736196975983387693) ^ 324798594533742425140483956 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 2273590161736196975983387693) ^ 206690014703290634180307972 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 2273590161736196975983387693) ^ 61448382749626945296848316 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (2 : ZMod 2273590161736196975983387693) ^ 307692 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_2788365292695335913941890567 : Nat.Prime 2788365292695335913941890567 := by
  apply lucas_primality 2788365292695335913941890567 (5 : ZMod 2788365292695335913941890567)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (3623, 1), (772333, 1), (55361039681334193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (3623, 1), (772333, 1), (55361039681334193, 1)] : List FactorBlock).map factorBlockValue).prod) = 2788365292695335913941890567 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_3
      · exact prime_oneHundredTwentyFiveDS_3623
      · exact prime_oneHundredTwentyFiveDS_772333
      · exact prime_oneHundredTwentyFiveDS_55361039681334193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2788365292695335913941890567) ^ 1394182646347667956970945283 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 2788365292695335913941890567) ^ 929455097565111971313963522 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 2788365292695335913941890567) ^ 769628841483669863080842 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 2788365292695335913941890567) ^ 3610314841778528062302 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (5 : ZMod 2788365292695335913941890567) ^ 50366924262 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyFiveDS_73891680256426401719460100049 : Nat.Prime 73891680256426401719460100049 := by
  apply lucas_primality 73891680256426401719460100049 (3 : ZMod 73891680256426401719460100049)
  · rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (43, 1), (26293, 1), (4084763931355547021947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (43, 1), (26293, 1), (4084763931355547021947, 1)] : List FactorBlock).map factorBlockValue).prod) = 73891680256426401719460100049 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyFiveDS_2
      · exact prime_oneHundredTwentyFiveDS_43
      · exact prime_oneHundredTwentyFiveDS_26293
      · exact prime_oneHundredTwentyFiveDS_4084763931355547021947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 73891680256426401719460100049) ^ 36945840128213200859730050024 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 73891680256426401719460100049) ^ 1718411168754102365568839536 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 73891680256426401719460100049) ^ 2810317584772616351099536 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide
    · change (3 : ZMod 73891680256426401719460100049) ^ 18089584 ≠ 1
      rw [← oneHundredTwentyFiveDSFastPow_eq_pow]
      decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200000 : Nat.totient 147783360512852803438920200000 = 59112999229252342736448000000 := by
  rw [← show ((([(2, 6), (5, 5), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200000 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_2, prime_oneHundredTwentyFiveDS_5, prime_oneHundredTwentyFiveDS_171401, prime_oneHundredTwentyFiveDS_714027719, prime_oneHundredTwentyFiveDS_6037638679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200001 : Nat.totient 147783360512852803438920200001 = 83880682214526835928852967360 := by
  rw [← show ((([(3, 1), (7, 1), (149, 1), (442139, 1), (106822109521305284971, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200001 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_3, prime_oneHundredTwentyFiveDS_7, prime_oneHundredTwentyFiveDS_149, prime_oneHundredTwentyFiveDS_442139, prime_oneHundredTwentyFiveDS_106822109521305284971]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200002 : Nat.totient 147783360512852803438920200002 = 67173511723778378882929277520 := by
  rw [← show ((([(2, 1), (11, 1), (90403, 1), (49179546079, 1), (1510899225343, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200002 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_2, prime_oneHundredTwentyFiveDS_11, prime_oneHundredTwentyFiveDS_90403, prime_oneHundredTwentyFiveDS_49179546079, prime_oneHundredTwentyFiveDS_1510899225343]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200003 : Nat.totient 147783360512852803438920200003 = 147783358886553608399647851528 := by
  rw [← show ((([(96773623, 1), (1491991379, 1), (1023533882359, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200003 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_96773623, prime_oneHundredTwentyFiveDS_1491991379, prime_oneHundredTwentyFiveDS_1023533882359]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200004 : Nat.totient 147783360512852803438920200004 = 49261119811405827297921825024 := by
  rw [← show ((([(2, 2), (3, 1), (137009569, 1), (89886276795292550843, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200004 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_2, prime_oneHundredTwentyFiveDS_3, prime_oneHundredTwentyFiveDS_137009569, prime_oneHundredTwentyFiveDS_89886276795292550843]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200005 : Nat.totient 147783360512852803438920200005 = 118226636702488275176120256000 := by
  rw [← show ((([(5, 1), (4674151, 1), (6380281, 1), (22998923, 1), (43092877, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200005 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_5, prime_oneHundredTwentyFiveDS_4674151, prime_oneHundredTwentyFiveDS_6380281, prime_oneHundredTwentyFiveDS_22998923, prime_oneHundredTwentyFiveDS_43092877]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200006 : Nat.totient 147783360512852803438920200006 = 65855715029589934948317114240 := by
  rw [← show ((([(2, 1), (13, 1), (29, 1), (9191211511631, 1), (21324626424469, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200006 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_2, prime_oneHundredTwentyFiveDS_13, prime_oneHundredTwentyFiveDS_29, prime_oneHundredTwentyFiveDS_9191211511631, prime_oneHundredTwentyFiveDS_21324626424469]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200007 : Nat.totient 147783360512852803438920200007 = 98522239676610945128175242712 := by
  rw [← show ((([(3, 3), (148088959, 1), (36960606879357738299, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200007 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_3, prime_oneHundredTwentyFiveDS_148088959, prime_oneHundredTwentyFiveDS_36960606879357738299]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200008 : Nat.totient 147783360512852803438920200008 = 62551339720331726301377163264 := by
  rw [← show ((([(2, 3), (7, 1), (113, 1), (349, 1), (1423, 1), (1893799, 1), (24831037027507, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200008 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_2, prime_oneHundredTwentyFiveDS_7, prime_oneHundredTwentyFiveDS_113, prime_oneHundredTwentyFiveDS_349, prime_oneHundredTwentyFiveDS_1423, prime_oneHundredTwentyFiveDS_1893799, prime_oneHundredTwentyFiveDS_24831037027507]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200009 : Nat.totient 147783360512852803438920200009 = 144177103818916260223522909440 := by
  rw [← show ((([(41, 1), (154723, 1), (169097, 1), (137768808036741779, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200009 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_41, prime_oneHundredTwentyFiveDS_154723, prime_oneHundredTwentyFiveDS_169097, prime_oneHundredTwentyFiveDS_137768808036741779]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200010 : Nat.totient 147783360512852803438920200010 = 38095578243210111019394826240 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (43, 1), (97, 1), (12844297, 1), (91950427801125241, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200010 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_2, prime_oneHundredTwentyFiveDS_3, prime_oneHundredTwentyFiveDS_5, prime_oneHundredTwentyFiveDS_43, prime_oneHundredTwentyFiveDS_97, prime_oneHundredTwentyFiveDS_12844297, prime_oneHundredTwentyFiveDS_91950427801125241]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200011 : Nat.totient 147783360512852803438920200011 = 147776715200068073819730936360 := by
  rw [← show ((([(22247, 1), (59869031, 1), (110956271390377723, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200011 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_22247, prime_oneHundredTwentyFiveDS_59869031, prime_oneHundredTwentyFiveDS_110956271390377723]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200012 : Nat.totient 147783360512852803438920200012 = 65804592335205963369432960000 := by
  rw [← show ((([(2, 2), (17, 1), (19, 1), (821, 1), (157131497951, 1), (886658979091, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200012 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_2, prime_oneHundredTwentyFiveDS_17, prime_oneHundredTwentyFiveDS_19, prime_oneHundredTwentyFiveDS_821, prime_oneHundredTwentyFiveDS_157131497951, prime_oneHundredTwentyFiveDS_886658979091]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200013 : Nat.totient 147783360512852803438920200013 = 86676430196496943269529920000 := by
  rw [← show ((([(3, 1), (11, 1), (31, 1), (3333749, 1), (54771919, 1), (791150393801, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200013 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_3, prime_oneHundredTwentyFiveDS_11, prime_oneHundredTwentyFiveDS_31, prime_oneHundredTwentyFiveDS_3333749, prime_oneHundredTwentyFiveDS_54771919, prime_oneHundredTwentyFiveDS_791150393801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200014 : Nat.totient 147783360512852803438920200014 = 73853767644699143432277204216 := by
  rw [← show ((([(2, 1), (1949, 1), (37912611727258287182893843, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200014 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_2, prime_oneHundredTwentyFiveDS_1949, prime_oneHundredTwentyFiveDS_37912611727258287182893843]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200015 : Nat.totient 147783360512852803438920200015 = 101237122617420482358702689664 := by
  rw [← show ((([(5, 1), (7, 1), (1013, 1), (46174027, 1), (90271424483937779, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200015 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_5, prime_oneHundredTwentyFiveDS_7, prime_oneHundredTwentyFiveDS_1013, prime_oneHundredTwentyFiveDS_46174027, prime_oneHundredTwentyFiveDS_90271424483937779]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200016 : Nat.totient 147783360512852803438920200016 = 47077640849811309913977626880 := by
  rw [← show ((([(2, 4), (3, 2), (23, 1), (2179, 1), (2347, 1), (8724989038175689211, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200016 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_2, prime_oneHundredTwentyFiveDS_3, prime_oneHundredTwentyFiveDS_23, prime_oneHundredTwentyFiveDS_2179, prime_oneHundredTwentyFiveDS_2347, prime_oneHundredTwentyFiveDS_8724989038175689211]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200017 : Nat.totient 147783360512852803438920200017 = 143789215624917542327836324224 := by
  rw [← show ((([(37, 1), (15613124869, 1), (255819697353228889, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200017 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_37, prime_oneHundredTwentyFiveDS_15613124869, prime_oneHundredTwentyFiveDS_255819697353228889]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200018 : Nat.totient 147783360512852803438920200018 = 71600696576542735211468800000 := by
  rw [← show ((([(2, 1), (47, 1), (101, 1), (50411, 1), (52541, 1), (40184357, 1), (146249921, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200018 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_2, prime_oneHundredTwentyFiveDS_47, prime_oneHundredTwentyFiveDS_101, prime_oneHundredTwentyFiveDS_50411, prime_oneHundredTwentyFiveDS_52541, prime_oneHundredTwentyFiveDS_40184357, prime_oneHundredTwentyFiveDS_146249921]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200019 : Nat.totient 147783360512852803438920200019 = 90784607858740135350275885568 := by
  rw [← show ((([(3, 1), (13, 1), (823, 1), (1873, 1), (2458234550212487461699, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200019 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_3, prime_oneHundredTwentyFiveDS_13, prime_oneHundredTwentyFiveDS_823, prime_oneHundredTwentyFiveDS_1873, prime_oneHundredTwentyFiveDS_2458234550212487461699]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200020 : Nat.totient 147783360512852803438920200020 = 58725076372807273625823105024 := by
  rw [← show ((([(2, 2), (5, 1), (157, 1), (4999, 1), (87683238689, 1), (107373267763, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200020 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_2, prime_oneHundredTwentyFiveDS_5, prime_oneHundredTwentyFiveDS_157, prime_oneHundredTwentyFiveDS_4999, prime_oneHundredTwentyFiveDS_87683238689, prime_oneHundredTwentyFiveDS_107373267763]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200021 : Nat.totient 147783360512852803438920200021 = 147779299397085384651001027200 := by
  rw [← show ((([(53017, 1), (133831, 1), (1982567, 1), (2441431, 1), (4303099, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200021 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_53017, prime_oneHundredTwentyFiveDS_133831, prime_oneHundredTwentyFiveDS_1982567, prime_oneHundredTwentyFiveDS_2441431, prime_oneHundredTwentyFiveDS_4303099]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200022 : Nat.totient 147783360512852803438920200022 = 41002389496327301643181667328 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (67, 1), (73, 1), (2099, 1), (21563, 1), (15894869376766573, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200022 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_2, prime_oneHundredTwentyFiveDS_3, prime_oneHundredTwentyFiveDS_7, prime_oneHundredTwentyFiveDS_67, prime_oneHundredTwentyFiveDS_73, prime_oneHundredTwentyFiveDS_2099, prime_oneHundredTwentyFiveDS_21563, prime_oneHundredTwentyFiveDS_15894869376766573]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200023 : Nat.totient 147783360512852803438920200023 = 147445962618854945977668864000 := by
  rw [← show ((([(563, 1), (2251, 1), (15749, 1), (21989953, 1), (336716473243, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200023 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_563, prime_oneHundredTwentyFiveDS_2251, prime_oneHundredTwentyFiveDS_15749, prime_oneHundredTwentyFiveDS_21989953, prime_oneHundredTwentyFiveDS_336716473243]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200024 : Nat.totient 147783360512852803438920200024 = 67171636613749774561414725120 := by
  rw [← show ((([(2, 3), (11, 1), (25657, 1), (65454120492038679608489, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200024 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_2, prime_oneHundredTwentyFiveDS_11, prime_oneHundredTwentyFiveDS_25657, prime_oneHundredTwentyFiveDS_65454120492038679608489]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200025 : Nat.totient 147783360512852803438920200025 = 78817662470977291532884970880 := by
  rw [← show ((([(3, 2), (5, 2), (607213, 1), (1081687868363620552253, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200025 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_3, prime_oneHundredTwentyFiveDS_5, prime_oneHundredTwentyFiveDS_607213, prime_oneHundredTwentyFiveDS_1081687868363620552253]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200026 : Nat.totient 147783360512852803438920200026 = 73159721590681871470852800000 := by
  rw [← show ((([(2, 1), (107, 1), (2081, 1), (11789, 1), (28148983514129501251, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200026 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_2, prime_oneHundredTwentyFiveDS_107, prime_oneHundredTwentyFiveDS_2081, prime_oneHundredTwentyFiveDS_11789, prime_oneHundredTwentyFiveDS_28148983514129501251]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200027 : Nat.totient 147783360512852803438920200027 = 147783357918238202080308361680 := by
  rw [← show ((([(56957731, 1), (2594614601358554880617, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200027 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_56957731, prime_oneHundredTwentyFiveDS_2594614601358554880617]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200028 : Nat.totient 147783360512852803438920200028 = 49180759435555255855389784320 := by
  rw [← show ((([(2, 2), (3, 1), (613, 1), (2837014421, 1), (7081451319513653, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200028 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_2, prime_oneHundredTwentyFiveDS_3, prime_oneHundredTwentyFiveDS_613, prime_oneHundredTwentyFiveDS_2837014421, prime_oneHundredTwentyFiveDS_7081451319513653]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200029 : Nat.totient 147783360512852803438920200029 = 119209609395197073876399897600 := by
  rw [← show ((([(7, 1), (17, 1), (12071, 1), (171091, 1), (16442347, 1), (36571632973, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200029 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_7, prime_oneHundredTwentyFiveDS_17, prime_oneHundredTwentyFiveDS_12071, prime_oneHundredTwentyFiveDS_171091, prime_oneHundredTwentyFiveDS_16442347, prime_oneHundredTwentyFiveDS_36571632973]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200030 : Nat.totient 147783360512852803438920200030 = 59109728488805247745218285312 := by
  rw [← show ((([(2, 1), (5, 1), (16349, 1), (659795388823, 1), (1370014198489, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200030 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_2, prime_oneHundredTwentyFiveDS_5, prime_oneHundredTwentyFiveDS_16349, prime_oneHundredTwentyFiveDS_659795388823, prime_oneHundredTwentyFiveDS_1370014198489]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200031 : Nat.totient 147783360512852803438920200031 = 93280935448879560448895299968 := by
  rw [← show ((([(3, 1), (19, 1), (1669, 1), (639742302293, 1), (2428226959999, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200031 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_3, prime_oneHundredTwentyFiveDS_19, prime_oneHundredTwentyFiveDS_1669, prime_oneHundredTwentyFiveDS_639742302293, prime_oneHundredTwentyFiveDS_2428226959999]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200032 : Nat.totient 147783360512852803438920200032 = 67051478874262748701658812416 := by
  rw [← show ((([(2, 5), (13, 1), (59, 1), (411127, 1), (762435017, 1), (19208849867, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200032 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_2, prime_oneHundredTwentyFiveDS_13, prime_oneHundredTwentyFiveDS_59, prime_oneHundredTwentyFiveDS_411127, prime_oneHundredTwentyFiveDS_762435017, prime_oneHundredTwentyFiveDS_19208849867]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200033 : Nat.totient 147783360512852803438920200033 = 147783359444361302447200556064 := by
  rw [← show ((([(160292807, 1), (1009649983, 1), (913146925993, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200033 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_160292807, prime_oneHundredTwentyFiveDS_1009649983, prime_oneHundredTwentyFiveDS_913146925993]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200034 : Nat.totient 147783360512852803438920200034 = 49105721758193065860700954752 := by
  rw [← show ((([(2, 1), (3, 5), (317, 1), (88109039, 1), (10887033067808713, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200034 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_2, prime_oneHundredTwentyFiveDS_3, prime_oneHundredTwentyFiveDS_317, prime_oneHundredTwentyFiveDS_88109039, prime_oneHundredTwentyFiveDS_10887033067808713]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200035 : Nat.totient 147783360512852803438920200035 = 103770057305489408596005936000 := by
  rw [← show ((([(5, 1), (11, 1), (29, 1), (40151, 1), (2307642263509371299503, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200035 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_5, prime_oneHundredTwentyFiveDS_11, prime_oneHundredTwentyFiveDS_29, prime_oneHundredTwentyFiveDS_40151, prime_oneHundredTwentyFiveDS_2307642263509371299503]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200036 : Nat.totient 147783360512852803438920200036 = 63335723109382783392975934560 := by
  rw [← show ((([(2, 2), (7, 1), (22422131, 1), (235391415792429114277, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200036 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_2, prime_oneHundredTwentyFiveDS_7, prime_oneHundredTwentyFiveDS_22422131, prime_oneHundredTwentyFiveDS_235391415792429114277]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200037 : Nat.totient 147783360512852803438920200037 = 98522240295068583559291922768 := by
  rw [← show ((([(3, 1), (2103679883, 1), (23416642697890425413, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200037 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_3, prime_oneHundredTwentyFiveDS_2103679883, prime_oneHundredTwentyFiveDS_23416642697890425413]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200038 : Nat.totient 147783360512852803438920200038 = 73891680255301303142339437296 := by
  rw [← show ((([(2, 1), (65675742617, 1), (1125098511444920107, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200038 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_2, prime_oneHundredTwentyFiveDS_65675742617, prime_oneHundredTwentyFiveDS_1125098511444920107]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200039 : Nat.totient 147783360512852803438920200039 = 141357997012213367993818215576 := by
  rw [← show ((([(23, 1), (1754271617359, 1), (3662695922899327, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200039 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_23, prime_oneHundredTwentyFiveDS_1754271617359, prime_oneHundredTwentyFiveDS_3662695922899327]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200040 : Nat.totient 147783360512852803438920200040 = 39408270497107366441535539200 := by
  rw [← show ((([(2, 3), (3, 1), (5, 1), (63907, 1), (6496339, 1), (14483401, 1), (204812579, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200040 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_2, prime_oneHundredTwentyFiveDS_3, prime_oneHundredTwentyFiveDS_5, prime_oneHundredTwentyFiveDS_63907, prime_oneHundredTwentyFiveDS_6496339, prime_oneHundredTwentyFiveDS_14483401, prime_oneHundredTwentyFiveDS_204812579]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200041 : Nat.totient 147783360512852803438920200041 = 147591441713934270468246230400 := by
  rw [← show ((([(773, 1), (200201, 1), (954948171737163551917, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200041 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_773, prime_oneHundredTwentyFiveDS_200201, prime_oneHundredTwentyFiveDS_954948171737163551917]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200042 : Nat.totient 147783360512852803438920200042 = 73798939055516885691213113280 := by
  rw [← show ((([(2, 1), (797, 1), (4243511, 1), (6395869, 1), (3415956476827, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200042 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_2, prime_oneHundredTwentyFiveDS_797, prime_oneHundredTwentyFiveDS_4243511, prime_oneHundredTwentyFiveDS_6395869, prime_oneHundredTwentyFiveDS_3415956476827]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200043 : Nat.totient 147783360512852803438920200043 = 84447634578773030536525828344 := by
  rw [← show ((([(3, 2), (7, 2), (335109661026877105303673923, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200043 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_3, prime_oneHundredTwentyFiveDS_7, prime_oneHundredTwentyFiveDS_335109661026877105303673923]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200044 : Nat.totient 147783360512852803438920200044 = 71508077667509421018832354800 := by
  rw [← show ((([(2, 2), (31, 1), (1191801294458490350313872581, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200044 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_2, prime_oneHundredTwentyFiveDS_31, prime_oneHundredTwentyFiveDS_1191801294458490350313872581]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200045 : Nat.totient 147783360512852803438920200045 = 109132327763337454847202609216 := by
  rw [← show ((([(5, 1), (13, 1), (2273590161736196975983387693, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200045 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_5, prime_oneHundredTwentyFiveDS_13, prime_oneHundredTwentyFiveDS_2273590161736196975983387693]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200046 : Nat.totient 147783360512852803438920200046 = 42148552017925933244611821440 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (17, 1), (131714225056018541389411943, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200046 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_2, prime_oneHundredTwentyFiveDS_3, prime_oneHundredTwentyFiveDS_11, prime_oneHundredTwentyFiveDS_17, prime_oneHundredTwentyFiveDS_131714225056018541389411943]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200047 : Nat.totient 147783360512852803438920200047 = 147783360511776504100584754080 := by
  rw [← show ((([(137306949937, 1), (1076299201028496031, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200047 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_137306949937, prime_oneHundredTwentyFiveDS_1076299201028496031]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200048 : Nat.totient 147783360512852803438920200048 = 73891680251943344722620812160 := by
  rw [← show ((([(2, 4), (16482432073, 1), (560382108122478911, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200048 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_2, prime_oneHundredTwentyFiveDS_16482432073, prime_oneHundredTwentyFiveDS_560382108122478911]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200049 : Nat.totient 147783360512852803438920200049 = 96640728228403179411951360000 := by
  rw [← show ((([(3, 1), (89, 1), (127, 1), (19717, 1), (38351, 1), (1945483, 1), (2962549301, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200049 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_3, prime_oneHundredTwentyFiveDS_89, prime_oneHundredTwentyFiveDS_127, prime_oneHundredTwentyFiveDS_19717, prime_oneHundredTwentyFiveDS_38351, prime_oneHundredTwentyFiveDS_1945483, prime_oneHundredTwentyFiveDS_2962549301]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200050 : Nat.totient 147783360512852803438920200050 = 46713071663293406800497868800 := by
  rw [← show ((([(2, 1), (5, 2), (7, 1), (19, 1), (41, 1), (397, 1), (13617913, 1), (100257985466497, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200050 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_2, prime_oneHundredTwentyFiveDS_5, prime_oneHundredTwentyFiveDS_7, prime_oneHundredTwentyFiveDS_19, prime_oneHundredTwentyFiveDS_41, prime_oneHundredTwentyFiveDS_397, prime_oneHundredTwentyFiveDS_13617913, prime_oneHundredTwentyFiveDS_100257985466497]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200051 : Nat.totient 147783360512852803438920200051 = 144994995220157467524978309432 := by
  rw [← show ((([(53, 1), (2788365292695335913941890567, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200051 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_53, prime_oneHundredTwentyFiveDS_2788365292695335913941890567]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200052 : Nat.totient 147783360512852803438920200052 = 49138274484739086762733228800 := by
  rw [← show ((([(2, 2), (3, 2), (401, 1), (10237140517653976408902757, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200052 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_2, prime_oneHundredTwentyFiveDS_3, prime_oneHundredTwentyFiveDS_401, prime_oneHundredTwentyFiveDS_10237140517653976408902757]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200053 : Nat.totient 147783360512852803438920200053 = 144346181020926457332186362880 := by
  rw [← show ((([(43, 1), (481769, 1), (2508769, 1), (2843528309867111, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200053 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_43, prime_oneHundredTwentyFiveDS_481769, prime_oneHundredTwentyFiveDS_2508769, prime_oneHundredTwentyFiveDS_2843528309867111]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200054 : Nat.totient 147783360512852803438920200054 = 71326336765702922081969817600 := by
  rw [← show ((([(2, 1), (37, 1), (137, 1), (2203, 1), (10651, 1), (16217, 1), (38308738636183, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200054 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_2, prime_oneHundredTwentyFiveDS_37, prime_oneHundredTwentyFiveDS_137, prime_oneHundredTwentyFiveDS_2203, prime_oneHundredTwentyFiveDS_10651, prime_oneHundredTwentyFiveDS_16217, prime_oneHundredTwentyFiveDS_38308738636183]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200055 : Nat.totient 147783360512852803438920200055 = 78817686217741382701686538368 := by
  rw [← show ((([(3, 1), (5, 1), (743173, 1), (13256972514058216452869, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200055 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_3, prime_oneHundredTwentyFiveDS_5, prime_oneHundredTwentyFiveDS_743173, prime_oneHundredTwentyFiveDS_13256972514058216452869]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200056 : Nat.totient 147783360512852803438920200056 = 73616989995250095393365451744 := by
  rw [← show ((([(2, 3), (269, 1), (68672565294076581523661803, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200056 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_2, prime_oneHundredTwentyFiveDS_269, prime_oneHundredTwentyFiveDS_68672565294076581523661803]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200057 : Nat.totient 147783360512852803438920200057 = 113533728328635699744318758400 := by
  rw [← show ((([(7, 1), (11, 1), (71, 1), (508187, 1), (53192807511908228833, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200057 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_7, prime_oneHundredTwentyFiveDS_11, prime_oneHundredTwentyFiveDS_71, prime_oneHundredTwentyFiveDS_508187, prime_oneHundredTwentyFiveDS_53192807511908228833]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200058 : Nat.totient 147783360512852803438920200058 = 44876783251669276515870662400 := by
  rw [← show ((([(2, 1), (3, 1), (13, 1), (79, 1), (2311, 1), (125356541, 1), (82785999874559, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200058 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_2, prime_oneHundredTwentyFiveDS_3, prime_oneHundredTwentyFiveDS_13, prime_oneHundredTwentyFiveDS_79, prime_oneHundredTwentyFiveDS_2311, prime_oneHundredTwentyFiveDS_125356541, prime_oneHundredTwentyFiveDS_82785999874559]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200059 : Nat.totient 147783360512852803438920200059 = 147357449613097492987048289640 := by
  rw [← show ((([(347, 1), (6621991, 1), (64314289616386246967, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200059 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_347, prime_oneHundredTwentyFiveDS_6621991, prime_oneHundredTwentyFiveDS_64314289616386246967]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200060 : Nat.totient 147783360512852803438920200060 = 57409197342493262598097931520 := by
  rw [← show ((([(2, 2), (5, 1), (61, 1), (83, 1), (1663, 1), (877597476325376642987, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200060 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_2, prime_oneHundredTwentyFiveDS_5, prime_oneHundredTwentyFiveDS_61, prime_oneHundredTwentyFiveDS_83, prime_oneHundredTwentyFiveDS_1663, prime_oneHundredTwentyFiveDS_877597476325376642987]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200061 : Nat.totient 147783360512852803438920200061 = 98473053002739661336235024880 := by
  rw [← show ((([(3, 3), (2003, 1), (2732629953455979058059581, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200061 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_3, prime_oneHundredTwentyFiveDS_2003, prime_oneHundredTwentyFiveDS_2732629953455979058059581]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200062 : Nat.totient 147783360512852803438920200062 = 70095946346817543905918515680 := by
  rw [← show ((([(2, 1), (23, 1), (139, 1), (941, 1), (24561974864329305043703, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200062 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_2, prime_oneHundredTwentyFiveDS_23, prime_oneHundredTwentyFiveDS_139, prime_oneHundredTwentyFiveDS_941, prime_oneHundredTwentyFiveDS_24561974864329305043703]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200063 : Nat.totient 147783360512852803438920200063 = 139086015889307119785198259200 := by
  rw [← show ((([(17, 1), (34183, 1), (1327561, 1), (4345031, 1), (44087865863, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200063 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_17, prime_oneHundredTwentyFiveDS_34183, prime_oneHundredTwentyFiveDS_1327561, prime_oneHundredTwentyFiveDS_4345031, prime_oneHundredTwentyFiveDS_44087865863]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200064 : Nat.totient 147783360512852803438920200064 = 40767823589752497500391757824 := by
  rw [← show ((([(2, 7), (3, 1), (7, 1), (29, 1), (1895825129731793968582207, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200064 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_2, prime_oneHundredTwentyFiveDS_3, prime_oneHundredTwentyFiveDS_7, prime_oneHundredTwentyFiveDS_29, prime_oneHundredTwentyFiveDS_1895825129731793968582207]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200065 : Nat.totient 147783360512852803438920200065 = 115711061804693648171385843168 := by
  rw [← show ((([(5, 1), (47, 2), (700643, 1), (19096906877256609199, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200065 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_5, prime_oneHundredTwentyFiveDS_47, prime_oneHundredTwentyFiveDS_700643, prime_oneHundredTwentyFiveDS_19096906877256609199]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200066 : Nat.totient 147783360512852803438920200066 = 73887624062747067778541189568 := by
  rw [← show ((([(2, 1), (18217, 1), (4056193679333940918892249, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200066 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_2, prime_oneHundredTwentyFiveDS_18217, prime_oneHundredTwentyFiveDS_4056193679333940918892249]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200067 : Nat.totient 147783360512852803438920200067 = 98522240338260237727354573320 := by
  rw [← show ((([(3, 1), (27054425759, 1), (1820815588908354271, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200067 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_3, prime_oneHundredTwentyFiveDS_27054425759, prime_oneHundredTwentyFiveDS_1820815588908354271]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200068 : Nat.totient 147783360512852803438920200068 = 66520510737111831139121053440 := by
  rw [← show ((([(2, 2), (11, 1), (103, 1), (42457, 1), (768044410650655524557, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200068 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_2, prime_oneHundredTwentyFiveDS_11, prime_oneHundredTwentyFiveDS_103, prime_oneHundredTwentyFiveDS_42457, prime_oneHundredTwentyFiveDS_768044410650655524557]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200069 : Nat.totient 147783360512852803438920200069 = 139998120302357068484644853760 := by
  rw [← show ((([(19, 1), (19531, 1), (578483509, 1), (688424747690369, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200069 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_19, prime_oneHundredTwentyFiveDS_19531, prime_oneHundredTwentyFiveDS_578483509, prime_oneHundredTwentyFiveDS_688424747690369]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200070 : Nat.totient 147783360512852803438920200070 = 38993570165391703975462212864 := by
  rw [← show ((([(2, 1), (3, 2), (5, 1), (109, 1), (727, 1), (588827, 1), (35191226542465943, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200070 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_2, prime_oneHundredTwentyFiveDS_3, prime_oneHundredTwentyFiveDS_5, prime_oneHundredTwentyFiveDS_109, prime_oneHundredTwentyFiveDS_727, prime_oneHundredTwentyFiveDS_588827, prime_oneHundredTwentyFiveDS_35191226542465943]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200071 : Nat.totient 147783360512852803438920200071 = 116927494032147273050574224160 := by
  rw [← show ((([(7, 1), (13, 1), (1623992972668712125702419781, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200071 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_7, prime_oneHundredTwentyFiveDS_13, prime_oneHundredTwentyFiveDS_1623992972668712125702419781]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200072 : Nat.totient 147783360512852803438920200072 = 73891680232896501691728050064 := by
  rw [← show ((([(2, 3), (3140331247, 1), (5882475003792681247, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200072 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_2, prime_oneHundredTwentyFiveDS_3140331247, prime_oneHundredTwentyFiveDS_5882475003792681247]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200073 : Nat.totient 147783360512852803438920200073 = 98247805131561582030992745360 := by
  rw [← show ((([(3, 1), (359, 1), (207222858971, 1), (662174074879519, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200073 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_3, prime_oneHundredTwentyFiveDS_359, prime_oneHundredTwentyFiveDS_207222858971, prime_oneHundredTwentyFiveDS_662174074879519]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200074 : Nat.totient 147783360512852803438920200074 = 73142709855437371182972567552 := by
  rw [← show ((([(2, 1), (163, 1), (257, 1), (7393, 1), (238591027982204845399, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200074 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_2, prime_oneHundredTwentyFiveDS_163, prime_oneHundredTwentyFiveDS_257, prime_oneHundredTwentyFiveDS_7393, prime_oneHundredTwentyFiveDS_238591027982204845399]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200075 : Nat.totient 147783360512852803438920200075 = 114412892477896108097440588800 := by
  rw [← show ((([(5, 2), (31, 1), (3599009, 1), (52983531609217552957, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200075 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_5, prime_oneHundredTwentyFiveDS_31, prime_oneHundredTwentyFiveDS_3599009, prime_oneHundredTwentyFiveDS_52983531609217552957]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200076 : Nat.totient 147783360512852803438920200076 = 49260365708448507712076978880 := by
  rw [← show ((([(2, 2), (3, 1), (65293, 1), (188615625606691890706661, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200076 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_2, prime_oneHundredTwentyFiveDS_3, prime_oneHundredTwentyFiveDS_65293, prime_oneHundredTwentyFiveDS_188615625606691890706661]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200077 : Nat.totient 147783360512852803438920200077 = 146655243256900865656150344480 := by
  rw [← show ((([(131, 1), (1141414241159, 1), (988350429794713, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200077 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_131, prime_oneHundredTwentyFiveDS_1141414241159, prime_oneHundredTwentyFiveDS_988350429794713]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200078 : Nat.totient 147783360512852803438920200078 = 63335723802670206818207323200 := by
  rw [← show ((([(2, 1), (7, 1), (48627091, 1), (76408531, 1), (2841040091737, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200078 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_2, prime_oneHundredTwentyFiveDS_7, prime_oneHundredTwentyFiveDS_48627091, prime_oneHundredTwentyFiveDS_76408531, prime_oneHundredTwentyFiveDS_2841040091737]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200079 : Nat.totient 147783360512852803438920200079 = 89563420890112068211479200640 := by
  rw [← show ((([(3, 2), (11, 1), (39769, 1), (37535799675665555308909, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200079 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_3, prime_oneHundredTwentyFiveDS_11, prime_oneHundredTwentyFiveDS_39769, prime_oneHundredTwentyFiveDS_37535799675665555308909]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200080 : Nat.totient 147783360512852803438920200080 = 55343393444353008804754022400 := by
  rw [← show ((([(2, 4), (5, 1), (17, 1), (191, 1), (39341, 1), (14461317705429316663, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200080 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_2, prime_oneHundredTwentyFiveDS_5, prime_oneHundredTwentyFiveDS_17, prime_oneHundredTwentyFiveDS_191, prime_oneHundredTwentyFiveDS_39341, prime_oneHundredTwentyFiveDS_14461317705429316663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200081 : Nat.totient 147783360512852803438920200081 = 147783360408673240783545192372 := by
  rw [← show ((([(1418544643, 1), (104179562653956463067, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200081 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_1418544643, prime_oneHundredTwentyFiveDS_104179562653956463067]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200082 : Nat.totient 147783360512852803438920200082 = 49261120138080162897747103440 := by
  rw [← show ((([(2, 1), (3, 1), (1498629871, 1), (16435385789447851757, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200082 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_2, prime_oneHundredTwentyFiveDS_3, prime_oneHundredTwentyFiveDS_1498629871, prime_oneHundredTwentyFiveDS_16435385789447851757]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200083 : Nat.totient 147783360512852803438920200083 = 147700661374345331248971166288 := by
  rw [← show ((([(1787, 1), (82699138507472189949032009, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200083 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_1787, prime_oneHundredTwentyFiveDS_82699138507472189949032009]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200084 : Nat.totient 147783360512852803438920200084 = 68120868701598063877425328128 := by
  rw [← show ((([(2, 2), (13, 1), (787, 1), (406313, 1), (134341979, 1), (66156878033, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200084 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_2, prime_oneHundredTwentyFiveDS_13, prime_oneHundredTwentyFiveDS_787, prime_oneHundredTwentyFiveDS_406313, prime_oneHundredTwentyFiveDS_134341979, prime_oneHundredTwentyFiveDS_66156878033]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200085 : Nat.totient 147783360512852803438920200085 = 64620798634124023433277484800 := by
  rw [← show ((([(3, 1), (5, 1), (7, 1), (23, 1), (971937009349, 1), (62960806628351, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200085 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_3, prime_oneHundredTwentyFiveDS_5, prime_oneHundredTwentyFiveDS_7, prime_oneHundredTwentyFiveDS_23, prime_oneHundredTwentyFiveDS_971937009349, prime_oneHundredTwentyFiveDS_62960806628351]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200086 : Nat.totient 147783360512852803438920200086 = 73891345011451076411731501920 := by
  rw [← show ((([(2, 1), (220411, 1), (335244975325307728377713, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200086 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_2, prime_oneHundredTwentyFiveDS_220411, prime_oneHundredTwentyFiveDS_335244975325307728377713]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200087 : Nat.totient 147783360512852803438920200087 = 147783360512851239949135164360 := by
  rw [← show ((([(101052806134517, 1), (1462436978901211, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200087 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_101052806134517, prime_oneHundredTwentyFiveDS_1462436978901211]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200088 : Nat.totient 147783360512852803438920200088 = 46652352763653799552946396160 := by
  rw [← show ((([(2, 3), (3, 3), (19, 1), (2903, 1), (49613561, 1), (250017697041709, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200088 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_2, prime_oneHundredTwentyFiveDS_3, prime_oneHundredTwentyFiveDS_19, prime_oneHundredTwentyFiveDS_2903, prime_oneHundredTwentyFiveDS_49613561, prime_oneHundredTwentyFiveDS_250017697041709]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200089 : Nat.totient 147783360512852803438920200089 = 145577596874056457799602250480 := by
  rw [← show ((([(67, 1), (3479381, 1), (633940864394929895207, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200089 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_67, prime_oneHundredTwentyFiveDS_3479381, prime_oneHundredTwentyFiveDS_633940864394929895207]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200090 : Nat.totient 147783360512852803438920200090 = 53427508417542588102918144000 := by
  rw [← show ((([(2, 1), (5, 1), (11, 2), (197, 1), (2341, 1), (4889, 1), (11069, 1), (105277, 1), (46484761, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200090 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_2, prime_oneHundredTwentyFiveDS_5, prime_oneHundredTwentyFiveDS_11, prime_oneHundredTwentyFiveDS_197, prime_oneHundredTwentyFiveDS_2341, prime_oneHundredTwentyFiveDS_4889, prime_oneHundredTwentyFiveDS_11069, prime_oneHundredTwentyFiveDS_105277, prime_oneHundredTwentyFiveDS_46484761]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200091 : Nat.totient 147783360512852803438920200091 = 91794235540218627671320919040 := by
  rw [← show ((([(3, 1), (37, 1), (41, 1), (59, 1), (647, 1), (8099692019, 1), (105025293643, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200091 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_3, prime_oneHundredTwentyFiveDS_37, prime_oneHundredTwentyFiveDS_41, prime_oneHundredTwentyFiveDS_59, prime_oneHundredTwentyFiveDS_647, prime_oneHundredTwentyFiveDS_8099692019, prime_oneHundredTwentyFiveDS_105025293643]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200092 : Nat.totient 147783360512852803438920200092 = 63335724579924553829412555264 := by
  rw [← show ((([(2, 2), (7, 2), (46771393, 1), (16120895465107774039, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200092 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_2, prime_oneHundredTwentyFiveDS_7, prime_oneHundredTwentyFiveDS_46771393, prime_oneHundredTwentyFiveDS_16120895465107774039]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200093 : Nat.totient 147783360512852803438920200093 = 142687379710132597585716267888 := by
  rw [← show ((([(29, 1), (49995559, 1), (101928612273723395863, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200093 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_29, prime_oneHundredTwentyFiveDS_49995559, prime_oneHundredTwentyFiveDS_101928612273723395863]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200094 : Nat.totient 147783360512852803438920200094 = 49261110728385066422410733120 := by
  rw [← show ((([(2, 1), (3, 1), (5216921, 1), (4721282934028609449869, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200094 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_2, prime_oneHundredTwentyFiveDS_3, prime_oneHundredTwentyFiveDS_5216921, prime_oneHundredTwentyFiveDS_4721282934028609449869]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200095 : Nat.totient 147783360512852803438920200095 = 116603188327744759471988828160 := by
  rw [← show ((([(5, 1), (73, 1), (29473, 1), (13737519737159276350811, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200095 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_5, prime_oneHundredTwentyFiveDS_73, prime_oneHundredTwentyFiveDS_29473, prime_oneHundredTwentyFiveDS_13737519737159276350811]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200096 : Nat.totient 147783360512852803438920200096 = 72170524126310428426274843904 := by
  rw [← show ((([(2, 5), (43, 1), (26293, 1), (4084763931355547021947, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200096 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_2, prime_oneHundredTwentyFiveDS_43, prime_oneHundredTwentyFiveDS_26293, prime_oneHundredTwentyFiveDS_4084763931355547021947]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200097 : Nat.totient 147783360512852803438920200097 = 85574881023537602813699358720 := by
  rw [← show ((([(3, 2), (13, 1), (17, 1), (4481, 1), (16581194394751674652333, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200097 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_3, prime_oneHundredTwentyFiveDS_13, prime_oneHundredTwentyFiveDS_17, prime_oneHundredTwentyFiveDS_4481, prime_oneHundredTwentyFiveDS_16581194394751674652333]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200098 : Nat.totient 147783360512852803438920200098 = 73891680256426401719460100048 := by
  rw [← show ((([(2, 1), (73891680256426401719460100049, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200098 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_2, prime_oneHundredTwentyFiveDS_73891680256426401719460100049]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200099 : Nat.totient 147783360512852803438920200099 = 126671174121885702609737548800 := by
  rw [← show ((([(7, 1), (597593, 1), (2424341, 1), (9421309, 1), (1546739021, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200099 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_7, prime_oneHundredTwentyFiveDS_597593, prime_oneHundredTwentyFiveDS_2424341, prime_oneHundredTwentyFiveDS_9421309, prime_oneHundredTwentyFiveDS_1546739021]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200100 : Nat.totient 147783360512852803438920200100 = 39401075104513765330990579200 := by
  rw [← show ((([(2, 2), (3, 1), (5, 2), (5879, 1), (35267, 1), (88812211, 1), (26752207429, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200100 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_2, prime_oneHundredTwentyFiveDS_3, prime_oneHundredTwentyFiveDS_5, prime_oneHundredTwentyFiveDS_5879, prime_oneHundredTwentyFiveDS_35267, prime_oneHundredTwentyFiveDS_88812211, prime_oneHundredTwentyFiveDS_26752207429]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyFiveDS_147783360512852803438920200101 : Nat.totient 147783360512852803438920200101 = 134348509557067824483545850000 := by
  rw [← show ((([(11, 1), (1890399915251, 1), (7106882965517941, 1)] : List FactorBlock).map factorBlockValue).prod) = 147783360512852803438920200101 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyFiveDS_11, prime_oneHundredTwentyFiveDS_1890399915251, prime_oneHundredTwentyFiveDS_7106882965517941]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64OneHundredTwentyFiveDS : certifiedKill 1 147783360512852803438920199999 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_oneHundredTwentyFiveDS_147783360512852803438920200000, phi_oneHundredTwentyFiveDS_147783360512852803438920200001, phi_oneHundredTwentyFiveDS_147783360512852803438920200002,
    phi_oneHundredTwentyFiveDS_147783360512852803438920200003, phi_oneHundredTwentyFiveDS_147783360512852803438920200004, phi_oneHundredTwentyFiveDS_147783360512852803438920200005,
    phi_oneHundredTwentyFiveDS_147783360512852803438920200006, phi_oneHundredTwentyFiveDS_147783360512852803438920200007, phi_oneHundredTwentyFiveDS_147783360512852803438920200008,
    phi_oneHundredTwentyFiveDS_147783360512852803438920200009, phi_oneHundredTwentyFiveDS_147783360512852803438920200010, phi_oneHundredTwentyFiveDS_147783360512852803438920200011,
    phi_oneHundredTwentyFiveDS_147783360512852803438920200012, phi_oneHundredTwentyFiveDS_147783360512852803438920200013, phi_oneHundredTwentyFiveDS_147783360512852803438920200014,
    phi_oneHundredTwentyFiveDS_147783360512852803438920200015, phi_oneHundredTwentyFiveDS_147783360512852803438920200016, phi_oneHundredTwentyFiveDS_147783360512852803438920200017,
    phi_oneHundredTwentyFiveDS_147783360512852803438920200018, phi_oneHundredTwentyFiveDS_147783360512852803438920200019, phi_oneHundredTwentyFiveDS_147783360512852803438920200020,
    phi_oneHundredTwentyFiveDS_147783360512852803438920200021, phi_oneHundredTwentyFiveDS_147783360512852803438920200022, phi_oneHundredTwentyFiveDS_147783360512852803438920200023,
    phi_oneHundredTwentyFiveDS_147783360512852803438920200024, phi_oneHundredTwentyFiveDS_147783360512852803438920200025, phi_oneHundredTwentyFiveDS_147783360512852803438920200026,
    phi_oneHundredTwentyFiveDS_147783360512852803438920200027, phi_oneHundredTwentyFiveDS_147783360512852803438920200028, phi_oneHundredTwentyFiveDS_147783360512852803438920200029,
    phi_oneHundredTwentyFiveDS_147783360512852803438920200030, phi_oneHundredTwentyFiveDS_147783360512852803438920200031, phi_oneHundredTwentyFiveDS_147783360512852803438920200032,
    phi_oneHundredTwentyFiveDS_147783360512852803438920200033, phi_oneHundredTwentyFiveDS_147783360512852803438920200034, phi_oneHundredTwentyFiveDS_147783360512852803438920200035,
    phi_oneHundredTwentyFiveDS_147783360512852803438920200036, phi_oneHundredTwentyFiveDS_147783360512852803438920200037, phi_oneHundredTwentyFiveDS_147783360512852803438920200038,
    phi_oneHundredTwentyFiveDS_147783360512852803438920200039, phi_oneHundredTwentyFiveDS_147783360512852803438920200040, phi_oneHundredTwentyFiveDS_147783360512852803438920200041,
    phi_oneHundredTwentyFiveDS_147783360512852803438920200042, phi_oneHundredTwentyFiveDS_147783360512852803438920200043, phi_oneHundredTwentyFiveDS_147783360512852803438920200044,
    phi_oneHundredTwentyFiveDS_147783360512852803438920200045, phi_oneHundredTwentyFiveDS_147783360512852803438920200046, phi_oneHundredTwentyFiveDS_147783360512852803438920200047,
    phi_oneHundredTwentyFiveDS_147783360512852803438920200048, phi_oneHundredTwentyFiveDS_147783360512852803438920200049, phi_oneHundredTwentyFiveDS_147783360512852803438920200050,
    phi_oneHundredTwentyFiveDS_147783360512852803438920200051, phi_oneHundredTwentyFiveDS_147783360512852803438920200052, phi_oneHundredTwentyFiveDS_147783360512852803438920200053,
    phi_oneHundredTwentyFiveDS_147783360512852803438920200054, phi_oneHundredTwentyFiveDS_147783360512852803438920200055, phi_oneHundredTwentyFiveDS_147783360512852803438920200056,
    phi_oneHundredTwentyFiveDS_147783360512852803438920200057, phi_oneHundredTwentyFiveDS_147783360512852803438920200058, phi_oneHundredTwentyFiveDS_147783360512852803438920200059,
    phi_oneHundredTwentyFiveDS_147783360512852803438920200060, phi_oneHundredTwentyFiveDS_147783360512852803438920200061, phi_oneHundredTwentyFiveDS_147783360512852803438920200062,
    phi_oneHundredTwentyFiveDS_147783360512852803438920200063, phi_oneHundredTwentyFiveDS_147783360512852803438920200064, phi_oneHundredTwentyFiveDS_147783360512852803438920200065,
    phi_oneHundredTwentyFiveDS_147783360512852803438920200066, phi_oneHundredTwentyFiveDS_147783360512852803438920200067, phi_oneHundredTwentyFiveDS_147783360512852803438920200068,
    phi_oneHundredTwentyFiveDS_147783360512852803438920200069, phi_oneHundredTwentyFiveDS_147783360512852803438920200070, phi_oneHundredTwentyFiveDS_147783360512852803438920200071,
    phi_oneHundredTwentyFiveDS_147783360512852803438920200072, phi_oneHundredTwentyFiveDS_147783360512852803438920200073, phi_oneHundredTwentyFiveDS_147783360512852803438920200074,
    phi_oneHundredTwentyFiveDS_147783360512852803438920200075, phi_oneHundredTwentyFiveDS_147783360512852803438920200076, phi_oneHundredTwentyFiveDS_147783360512852803438920200077,
    phi_oneHundredTwentyFiveDS_147783360512852803438920200078, phi_oneHundredTwentyFiveDS_147783360512852803438920200079, phi_oneHundredTwentyFiveDS_147783360512852803438920200080,
    phi_oneHundredTwentyFiveDS_147783360512852803438920200081, phi_oneHundredTwentyFiveDS_147783360512852803438920200082, phi_oneHundredTwentyFiveDS_147783360512852803438920200083,
    phi_oneHundredTwentyFiveDS_147783360512852803438920200084, phi_oneHundredTwentyFiveDS_147783360512852803438920200085, phi_oneHundredTwentyFiveDS_147783360512852803438920200086,
    phi_oneHundredTwentyFiveDS_147783360512852803438920200087, phi_oneHundredTwentyFiveDS_147783360512852803438920200088, phi_oneHundredTwentyFiveDS_147783360512852803438920200089,
    phi_oneHundredTwentyFiveDS_147783360512852803438920200090, phi_oneHundredTwentyFiveDS_147783360512852803438920200091, phi_oneHundredTwentyFiveDS_147783360512852803438920200092,
    phi_oneHundredTwentyFiveDS_147783360512852803438920200093, phi_oneHundredTwentyFiveDS_147783360512852803438920200094, phi_oneHundredTwentyFiveDS_147783360512852803438920200095,
    phi_oneHundredTwentyFiveDS_147783360512852803438920200096, phi_oneHundredTwentyFiveDS_147783360512852803438920200097, phi_oneHundredTwentyFiveDS_147783360512852803438920200098,
    phi_oneHundredTwentyFiveDS_147783360512852803438920200099, phi_oneHundredTwentyFiveDS_147783360512852803438920200100, phi_oneHundredTwentyFiveDS_147783360512852803438920200101]

end TotientTailPeriodKiller
end Erdos249257
