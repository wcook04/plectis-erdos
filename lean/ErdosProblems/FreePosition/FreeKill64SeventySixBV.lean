import Erdos249257.DiagonalPincerCertificatesT64

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def seventySixBVFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem seventySixBVFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : seventySixBVFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [seventySixBVFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [seventySixBVFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then seventySixBVFastPow a n * seventySixBVFastPow a n * a else seventySixBVFastPow a n * seventySixBVFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_seventySixBV_2 : Nat.Prime 2 := by norm_num
private theorem prime_seventySixBV_3 : Nat.Prime 3 := by norm_num
private theorem prime_seventySixBV_5 : Nat.Prime 5 := by norm_num
private theorem prime_seventySixBV_7 : Nat.Prime 7 := by norm_num
private theorem prime_seventySixBV_11 : Nat.Prime 11 := by norm_num
private theorem prime_seventySixBV_13 : Nat.Prime 13 := by norm_num
private theorem prime_seventySixBV_17 : Nat.Prime 17 := by norm_num
private theorem prime_seventySixBV_19 : Nat.Prime 19 := by norm_num
private theorem prime_seventySixBV_23 : Nat.Prime 23 := by norm_num
private theorem prime_seventySixBV_29 : Nat.Prime 29 := by norm_num
private theorem prime_seventySixBV_31 : Nat.Prime 31 := by norm_num
private theorem prime_seventySixBV_37 : Nat.Prime 37 := by norm_num
private theorem prime_seventySixBV_41 : Nat.Prime 41 := by norm_num
private theorem prime_seventySixBV_43 : Nat.Prime 43 := by norm_num
private theorem prime_seventySixBV_47 : Nat.Prime 47 := by norm_num
private theorem prime_seventySixBV_53 : Nat.Prime 53 := by norm_num
private theorem prime_seventySixBV_59 : Nat.Prime 59 := by norm_num
private theorem prime_seventySixBV_61 : Nat.Prime 61 := by norm_num
private theorem prime_seventySixBV_67 : Nat.Prime 67 := by norm_num
private theorem prime_seventySixBV_71 : Nat.Prime 71 := by norm_num
private theorem prime_seventySixBV_73 : Nat.Prime 73 := by norm_num
private theorem prime_seventySixBV_79 : Nat.Prime 79 := by norm_num
private theorem prime_seventySixBV_83 : Nat.Prime 83 := by norm_num
private theorem prime_seventySixBV_89 : Nat.Prime 89 := by norm_num
private theorem prime_seventySixBV_97 : Nat.Prime 97 := by norm_num
private theorem prime_seventySixBV_101 : Nat.Prime 101 := by norm_num
private theorem prime_seventySixBV_103 : Nat.Prime 103 := by norm_num
private theorem prime_seventySixBV_107 : Nat.Prime 107 := by norm_num
private theorem prime_seventySixBV_109 : Nat.Prime 109 := by norm_num
private theorem prime_seventySixBV_113 : Nat.Prime 113 := by norm_num
private theorem prime_seventySixBV_127 : Nat.Prime 127 := by norm_num
private theorem prime_seventySixBV_131 : Nat.Prime 131 := by norm_num
private theorem prime_seventySixBV_137 : Nat.Prime 137 := by norm_num
private theorem prime_seventySixBV_139 : Nat.Prime 139 := by norm_num
private theorem prime_seventySixBV_149 : Nat.Prime 149 := by norm_num
private theorem prime_seventySixBV_151 : Nat.Prime 151 := by norm_num
private theorem prime_seventySixBV_157 : Nat.Prime 157 := by norm_num
private theorem prime_seventySixBV_163 : Nat.Prime 163 := by norm_num
private theorem prime_seventySixBV_167 : Nat.Prime 167 := by norm_num
private theorem prime_seventySixBV_173 : Nat.Prime 173 := by norm_num
private theorem prime_seventySixBV_191 : Nat.Prime 191 := by norm_num
private theorem prime_seventySixBV_193 : Nat.Prime 193 := by norm_num
private theorem prime_seventySixBV_197 : Nat.Prime 197 := by norm_num
private theorem prime_seventySixBV_199 : Nat.Prime 199 := by norm_num
private theorem prime_seventySixBV_211 : Nat.Prime 211 := by norm_num
private theorem prime_seventySixBV_223 : Nat.Prime 223 := by norm_num
private theorem prime_seventySixBV_227 : Nat.Prime 227 := by norm_num
private theorem prime_seventySixBV_229 : Nat.Prime 229 := by norm_num
private theorem prime_seventySixBV_233 : Nat.Prime 233 := by norm_num
private theorem prime_seventySixBV_239 : Nat.Prime 239 := by norm_num
private theorem prime_seventySixBV_241 : Nat.Prime 241 := by norm_num
private theorem prime_seventySixBV_251 : Nat.Prime 251 := by norm_num
private theorem prime_seventySixBV_257 : Nat.Prime 257 := by norm_num
private theorem prime_seventySixBV_263 : Nat.Prime 263 := by norm_num
private theorem prime_seventySixBV_269 : Nat.Prime 269 := by norm_num
private theorem prime_seventySixBV_271 : Nat.Prime 271 := by norm_num
private theorem prime_seventySixBV_277 : Nat.Prime 277 := by norm_num
private theorem prime_seventySixBV_281 : Nat.Prime 281 := by norm_num
private theorem prime_seventySixBV_283 : Nat.Prime 283 := by norm_num
private theorem prime_seventySixBV_293 : Nat.Prime 293 := by norm_num
private theorem prime_seventySixBV_307 : Nat.Prime 307 := by norm_num
private theorem prime_seventySixBV_311 : Nat.Prime 311 := by norm_num
private theorem prime_seventySixBV_313 : Nat.Prime 313 := by norm_num
private theorem prime_seventySixBV_317 : Nat.Prime 317 := by norm_num
private theorem prime_seventySixBV_331 : Nat.Prime 331 := by norm_num
private theorem prime_seventySixBV_337 : Nat.Prime 337 := by norm_num
private theorem prime_seventySixBV_347 : Nat.Prime 347 := by norm_num
private theorem prime_seventySixBV_353 : Nat.Prime 353 := by norm_num
private theorem prime_seventySixBV_359 : Nat.Prime 359 := by norm_num
private theorem prime_seventySixBV_367 : Nat.Prime 367 := by norm_num
private theorem prime_seventySixBV_373 : Nat.Prime 373 := by norm_num
private theorem prime_seventySixBV_383 : Nat.Prime 383 := by norm_num
private theorem prime_seventySixBV_389 : Nat.Prime 389 := by norm_num
private theorem prime_seventySixBV_409 : Nat.Prime 409 := by norm_num
private theorem prime_seventySixBV_419 : Nat.Prime 419 := by norm_num
private theorem prime_seventySixBV_431 : Nat.Prime 431 := by norm_num
private theorem prime_seventySixBV_439 : Nat.Prime 439 := by norm_num
private theorem prime_seventySixBV_443 : Nat.Prime 443 := by norm_num
private theorem prime_seventySixBV_457 : Nat.Prime 457 := by norm_num
private theorem prime_seventySixBV_461 : Nat.Prime 461 := by norm_num
private theorem prime_seventySixBV_467 : Nat.Prime 467 := by norm_num
private theorem prime_seventySixBV_479 : Nat.Prime 479 := by norm_num
private theorem prime_seventySixBV_491 : Nat.Prime 491 := by norm_num
private theorem prime_seventySixBV_499 : Nat.Prime 499 := by norm_num
private theorem prime_seventySixBV_541 : Nat.Prime 541 := by norm_num
private theorem prime_seventySixBV_587 : Nat.Prime 587 := by norm_num
private theorem prime_seventySixBV_617 : Nat.Prime 617 := by norm_num
private theorem prime_seventySixBV_641 : Nat.Prime 641 := by norm_num
private theorem prime_seventySixBV_643 : Nat.Prime 643 := by norm_num
private theorem prime_seventySixBV_653 : Nat.Prime 653 := by norm_num
private theorem prime_seventySixBV_659 : Nat.Prime 659 := by norm_num
private theorem prime_seventySixBV_673 : Nat.Prime 673 := by norm_num
private theorem prime_seventySixBV_683 : Nat.Prime 683 := by norm_num
private theorem prime_seventySixBV_739 : Nat.Prime 739 := by norm_num
private theorem prime_seventySixBV_811 : Nat.Prime 811 := by norm_num
private theorem prime_seventySixBV_827 : Nat.Prime 827 := by norm_num
private theorem prime_seventySixBV_877 : Nat.Prime 877 := by norm_num
private theorem prime_seventySixBV_883 : Nat.Prime 883 := by norm_num
private theorem prime_seventySixBV_907 : Nat.Prime 907 := by norm_num
private theorem prime_seventySixBV_953 : Nat.Prime 953 := by norm_num
private theorem prime_seventySixBV_977 : Nat.Prime 977 := by norm_num
private theorem prime_seventySixBV_1009 : Nat.Prime 1009 := by norm_num
private theorem prime_seventySixBV_1049 : Nat.Prime 1049 := by norm_num
private theorem prime_seventySixBV_1063 : Nat.Prime 1063 := by norm_num
private theorem prime_seventySixBV_1069 : Nat.Prime 1069 := by norm_num
private theorem prime_seventySixBV_1087 : Nat.Prime 1087 := by norm_num
private theorem prime_seventySixBV_1117 : Nat.Prime 1117 := by norm_num
private theorem prime_seventySixBV_1151 : Nat.Prime 1151 := by norm_num
private theorem prime_seventySixBV_1153 : Nat.Prime 1153 := by norm_num
private theorem prime_seventySixBV_1163 : Nat.Prime 1163 := by norm_num
private theorem prime_seventySixBV_1187 : Nat.Prime 1187 := by norm_num
private theorem prime_seventySixBV_1193 : Nat.Prime 1193 := by norm_num
private theorem prime_seventySixBV_1249 : Nat.Prime 1249 := by norm_num
private theorem prime_seventySixBV_1277 : Nat.Prime 1277 := by norm_num
private theorem prime_seventySixBV_1283 : Nat.Prime 1283 := by norm_num
private theorem prime_seventySixBV_1289 : Nat.Prime 1289 := by norm_num
private theorem prime_seventySixBV_1303 : Nat.Prime 1303 := by norm_num
private theorem prime_seventySixBV_1399 : Nat.Prime 1399 := by norm_num
private theorem prime_seventySixBV_1423 : Nat.Prime 1423 := by norm_num
private theorem prime_seventySixBV_1429 : Nat.Prime 1429 := by norm_num
private theorem prime_seventySixBV_1439 : Nat.Prime 1439 := by norm_num
private theorem prime_seventySixBV_1451 : Nat.Prime 1451 := by norm_num
private theorem prime_seventySixBV_1483 : Nat.Prime 1483 := by norm_num
private theorem prime_seventySixBV_1511 : Nat.Prime 1511 := by norm_num
private theorem prime_seventySixBV_1559 : Nat.Prime 1559 := by norm_num
private theorem prime_seventySixBV_1607 : Nat.Prime 1607 := by norm_num
private theorem prime_seventySixBV_1637 : Nat.Prime 1637 := by norm_num
private theorem prime_seventySixBV_1721 : Nat.Prime 1721 := by norm_num
private theorem prime_seventySixBV_1759 : Nat.Prime 1759 := by norm_num
private theorem prime_seventySixBV_1789 : Nat.Prime 1789 := by norm_num
private theorem prime_seventySixBV_1847 : Nat.Prime 1847 := by norm_num
private theorem prime_seventySixBV_1873 : Nat.Prime 1873 := by norm_num
private theorem prime_seventySixBV_1933 : Nat.Prime 1933 := by norm_num
private theorem prime_seventySixBV_1973 : Nat.Prime 1973 := by norm_num
private theorem prime_seventySixBV_2011 : Nat.Prime 2011 := by norm_num
private theorem prime_seventySixBV_2069 : Nat.Prime 2069 := by norm_num
private theorem prime_seventySixBV_2083 : Nat.Prime 2083 := by norm_num
private theorem prime_seventySixBV_2087 : Nat.Prime 2087 := by norm_num
private theorem prime_seventySixBV_2099 : Nat.Prime 2099 := by norm_num
private theorem prime_seventySixBV_2111 : Nat.Prime 2111 := by norm_num
private theorem prime_seventySixBV_2161 : Nat.Prime 2161 := by norm_num
private theorem prime_seventySixBV_2213 : Nat.Prime 2213 := by norm_num
private theorem prime_seventySixBV_2221 : Nat.Prime 2221 := by norm_num
private theorem prime_seventySixBV_2239 : Nat.Prime 2239 := by norm_num
private theorem prime_seventySixBV_2273 : Nat.Prime 2273 := by norm_num
private theorem prime_seventySixBV_2293 : Nat.Prime 2293 := by norm_num
private theorem prime_seventySixBV_2333 : Nat.Prime 2333 := by norm_num
private theorem prime_seventySixBV_2341 : Nat.Prime 2341 := by norm_num
private theorem prime_seventySixBV_2381 : Nat.Prime 2381 := by norm_num
private theorem prime_seventySixBV_2389 : Nat.Prime 2389 := by norm_num
private theorem prime_seventySixBV_2399 : Nat.Prime 2399 := by norm_num
private theorem prime_seventySixBV_2423 : Nat.Prime 2423 := by norm_num
private theorem prime_seventySixBV_2441 : Nat.Prime 2441 := by norm_num
private theorem prime_seventySixBV_2467 : Nat.Prime 2467 := by norm_num
private theorem prime_seventySixBV_2687 : Nat.Prime 2687 := by norm_num
private theorem prime_seventySixBV_2749 : Nat.Prime 2749 := by norm_num
private theorem prime_seventySixBV_2777 : Nat.Prime 2777 := by norm_num
private theorem prime_seventySixBV_2861 : Nat.Prime 2861 := by norm_num
private theorem prime_seventySixBV_3001 : Nat.Prime 3001 := by norm_num
private theorem prime_seventySixBV_3181 : Nat.Prime 3181 := by norm_num
private theorem prime_seventySixBV_3617 : Nat.Prime 3617 := by norm_num
private theorem prime_seventySixBV_3803 : Nat.Prime 3803 := by norm_num
private theorem prime_seventySixBV_3821 : Nat.Prime 3821 := by norm_num
private theorem prime_seventySixBV_3847 : Nat.Prime 3847 := by norm_num
private theorem prime_seventySixBV_3863 : Nat.Prime 3863 := by norm_num
private theorem prime_seventySixBV_3967 : Nat.Prime 3967 := by norm_num
private theorem prime_seventySixBV_4019 : Nat.Prime 4019 := by norm_num
private theorem prime_seventySixBV_4153 : Nat.Prime 4153 := by norm_num
private theorem prime_seventySixBV_4273 : Nat.Prime 4273 := by norm_num
private theorem prime_seventySixBV_4397 : Nat.Prime 4397 := by norm_num
private theorem prime_seventySixBV_4481 : Nat.Prime 4481 := by norm_num
private theorem prime_seventySixBV_4523 : Nat.Prime 4523 := by norm_num
private theorem prime_seventySixBV_4657 : Nat.Prime 4657 := by norm_num
private theorem prime_seventySixBV_4799 : Nat.Prime 4799 := by norm_num
private theorem prime_seventySixBV_4813 : Nat.Prime 4813 := by norm_num
private theorem prime_seventySixBV_4817 : Nat.Prime 4817 := by norm_num
private theorem prime_seventySixBV_4831 : Nat.Prime 4831 := by norm_num
private theorem prime_seventySixBV_4861 : Nat.Prime 4861 := by norm_num
private theorem prime_seventySixBV_4999 : Nat.Prime 4999 := by norm_num
private theorem prime_seventySixBV_5179 : Nat.Prime 5179 := by norm_num
private theorem prime_seventySixBV_5197 : Nat.Prime 5197 := by norm_num
private theorem prime_seventySixBV_5309 : Nat.Prime 5309 := by norm_num
private theorem prime_seventySixBV_5641 : Nat.Prime 5641 := by norm_num
private theorem prime_seventySixBV_5701 : Nat.Prime 5701 := by norm_num
private theorem prime_seventySixBV_5737 : Nat.Prime 5737 := by norm_num
private theorem prime_seventySixBV_5783 : Nat.Prime 5783 := by norm_num
private theorem prime_seventySixBV_5927 : Nat.Prime 5927 := by norm_num
private theorem prime_seventySixBV_6011 : Nat.Prime 6011 := by norm_num
private theorem prime_seventySixBV_6163 : Nat.Prime 6163 := by norm_num
private theorem prime_seventySixBV_6521 : Nat.Prime 6521 := by norm_num
private theorem prime_seventySixBV_6581 : Nat.Prime 6581 := by norm_num
private theorem prime_seventySixBV_6659 : Nat.Prime 6659 := by norm_num
private theorem prime_seventySixBV_6673 : Nat.Prime 6673 := by norm_num
private theorem prime_seventySixBV_7499 : Nat.Prime 7499 := by norm_num
private theorem prime_seventySixBV_7577 : Nat.Prime 7577 := by norm_num
private theorem prime_seventySixBV_7723 : Nat.Prime 7723 := by norm_num
private theorem prime_seventySixBV_7823 : Nat.Prime 7823 := by norm_num
private theorem prime_seventySixBV_7937 : Nat.Prime 7937 := by norm_num
private theorem prime_seventySixBV_8059 : Nat.Prime 8059 := by norm_num
private theorem prime_seventySixBV_8209 : Nat.Prime 8209 := by norm_num
private theorem prime_seventySixBV_8369 : Nat.Prime 8369 := by norm_num
private theorem prime_seventySixBV_8641 : Nat.Prime 8641 := by norm_num
private theorem prime_seventySixBV_8803 : Nat.Prime 8803 := by norm_num
private theorem prime_seventySixBV_9173 : Nat.Prime 9173 := by norm_num
private theorem prime_seventySixBV_9929 : Nat.Prime 9929 := by norm_num
private theorem prime_seventySixBV_10099 : Nat.Prime 10099 := by norm_num
private theorem prime_seventySixBV_10223 : Nat.Prime 10223 := by norm_num
private theorem prime_seventySixBV_10429 : Nat.Prime 10429 := by norm_num
private theorem prime_seventySixBV_10631 : Nat.Prime 10631 := by norm_num
private theorem prime_seventySixBV_10903 : Nat.Prime 10903 := by norm_num
private theorem prime_seventySixBV_10979 : Nat.Prime 10979 := by norm_num
private theorem prime_seventySixBV_11549 : Nat.Prime 11549 := by norm_num
private theorem prime_seventySixBV_11863 : Nat.Prime 11863 := by norm_num
private theorem prime_seventySixBV_12503 : Nat.Prime 12503 := by norm_num
private theorem prime_seventySixBV_12967 : Nat.Prime 12967 := by norm_num
private theorem prime_seventySixBV_13537 : Nat.Prime 13537 := by norm_num
private theorem prime_seventySixBV_13789 : Nat.Prime 13789 := by norm_num
private theorem prime_seventySixBV_14107 : Nat.Prime 14107 := by norm_num
private theorem prime_seventySixBV_14221 : Nat.Prime 14221 := by norm_num
private theorem prime_seventySixBV_14431 : Nat.Prime 14431 := by norm_num
private theorem prime_seventySixBV_14699 : Nat.Prime 14699 := by norm_num
private theorem prime_seventySixBV_15031 : Nat.Prime 15031 := by norm_num
private theorem prime_seventySixBV_15073 : Nat.Prime 15073 := by norm_num
private theorem prime_seventySixBV_15443 : Nat.Prime 15443 := by norm_num
private theorem prime_seventySixBV_15541 : Nat.Prime 15541 := by norm_num
private theorem prime_seventySixBV_15629 : Nat.Prime 15629 := by norm_num
private theorem prime_seventySixBV_15739 : Nat.Prime 15739 := by norm_num
private theorem prime_seventySixBV_15973 : Nat.Prime 15973 := by norm_num
private theorem prime_seventySixBV_16823 : Nat.Prime 16823 := by norm_num
private theorem prime_seventySixBV_16993 : Nat.Prime 16993 := by norm_num
private theorem prime_seventySixBV_17047 : Nat.Prime 17047 := by norm_num
private theorem prime_seventySixBV_17599 : Nat.Prime 17599 := by norm_num
private theorem prime_seventySixBV_18181 : Nat.Prime 18181 := by norm_num
private theorem prime_seventySixBV_18859 : Nat.Prime 18859 := by norm_num
private theorem prime_seventySixBV_19141 : Nat.Prime 19141 := by norm_num
private theorem prime_seventySixBV_19403 : Nat.Prime 19403 := by norm_num
private theorem prime_seventySixBV_19501 : Nat.Prime 19501 := by norm_num
private theorem prime_seventySixBV_19571 : Nat.Prime 19571 := by norm_num
private theorem prime_seventySixBV_20483 : Nat.Prime 20483 := by norm_num
private theorem prime_seventySixBV_21751 : Nat.Prime 21751 := by norm_num
private theorem prime_seventySixBV_22367 : Nat.Prime 22367 := by norm_num
private theorem prime_seventySixBV_23993 : Nat.Prime 23993 := by norm_num
private theorem prime_seventySixBV_24203 : Nat.Prime 24203 := by norm_num
private theorem prime_seventySixBV_25343 : Nat.Prime 25343 := by norm_num
private theorem prime_seventySixBV_26833 : Nat.Prime 26833 := by norm_num
private theorem prime_seventySixBV_27191 : Nat.Prime 27191 := by norm_num
private theorem prime_seventySixBV_28069 : Nat.Prime 28069 := by norm_num
private theorem prime_seventySixBV_28867 : Nat.Prime 28867 := by norm_num
private theorem prime_seventySixBV_30449 : Nat.Prime 30449 := by norm_num
private theorem prime_seventySixBV_30931 : Nat.Prime 30931 := by norm_num
private theorem prime_seventySixBV_30941 : Nat.Prime 30941 := by norm_num
private theorem prime_seventySixBV_31151 : Nat.Prime 31151 := by norm_num
private theorem prime_seventySixBV_31337 : Nat.Prime 31337 := by norm_num
private theorem prime_seventySixBV_31379 : Nat.Prime 31379 := by norm_num
private theorem prime_seventySixBV_31517 : Nat.Prime 31517 := by norm_num
private theorem prime_seventySixBV_31531 : Nat.Prime 31531 := by norm_num
private theorem prime_seventySixBV_32909 : Nat.Prime 32909 := by norm_num
private theorem prime_seventySixBV_33479 : Nat.Prime 33479 := by norm_num
private theorem prime_seventySixBV_34061 : Nat.Prime 34061 := by norm_num
private theorem prime_seventySixBV_34501 : Nat.Prime 34501 := by norm_num
private theorem prime_seventySixBV_37253 : Nat.Prime 37253 := by norm_num
private theorem prime_seventySixBV_37501 : Nat.Prime 37501 := by norm_num
private theorem prime_seventySixBV_37549 : Nat.Prime 37549 := by norm_num
private theorem prime_seventySixBV_38783 : Nat.Prime 38783 := by norm_num
private theorem prime_seventySixBV_43403 : Nat.Prime 43403 := by norm_num
private theorem prime_seventySixBV_43753 : Nat.Prime 43753 := by norm_num
private theorem prime_seventySixBV_44507 : Nat.Prime 44507 := by norm_num
private theorem prime_seventySixBV_44563 : Nat.Prime 44563 := by norm_num
private theorem prime_seventySixBV_45757 : Nat.Prime 45757 := by norm_num
private theorem prime_seventySixBV_46619 : Nat.Prime 46619 := by norm_num
private theorem prime_seventySixBV_47087 : Nat.Prime 47087 := by norm_num
private theorem prime_seventySixBV_48109 : Nat.Prime 48109 := by norm_num
private theorem prime_seventySixBV_48487 : Nat.Prime 48487 := by norm_num
private theorem prime_seventySixBV_49333 : Nat.Prime 49333 := by norm_num
private theorem prime_seventySixBV_49409 : Nat.Prime 49409 := by norm_num
private theorem prime_seventySixBV_49747 : Nat.Prime 49747 := by norm_num
private theorem prime_seventySixBV_50119 : Nat.Prime 50119 := by norm_num
private theorem prime_seventySixBV_50159 : Nat.Prime 50159 := by norm_num
private theorem prime_seventySixBV_50773 : Nat.Prime 50773 := by norm_num
private theorem prime_seventySixBV_55697 : Nat.Prime 55697 := by norm_num
private theorem prime_seventySixBV_59243 : Nat.Prime 59243 := by norm_num
private theorem prime_seventySixBV_62039 : Nat.Prime 62039 := by norm_num
private theorem prime_seventySixBV_62131 : Nat.Prime 62131 := by norm_num
private theorem prime_seventySixBV_65789 : Nat.Prime 65789 := by norm_num
private theorem prime_seventySixBV_69191 : Nat.Prime 69191 := by norm_num
private theorem prime_seventySixBV_69763 : Nat.Prime 69763 := by norm_num
private theorem prime_seventySixBV_70241 : Nat.Prime 70241 := by norm_num
private theorem prime_seventySixBV_70393 : Nat.Prime 70393 := by norm_num
private theorem prime_seventySixBV_79283 : Nat.Prime 79283 := by norm_num
private theorem prime_seventySixBV_79319 : Nat.Prime 79319 := by norm_num
private theorem prime_seventySixBV_82003 : Nat.Prime 82003 := by norm_num
private theorem prime_seventySixBV_82787 : Nat.Prime 82787 := by norm_num
private theorem prime_seventySixBV_84551 : Nat.Prime 84551 := by norm_num
private theorem prime_seventySixBV_87887 : Nat.Prime 87887 := by norm_num
private theorem prime_seventySixBV_90911 : Nat.Prime 90911 := by norm_num
private theorem prime_seventySixBV_94057 : Nat.Prime 94057 := by norm_num
private theorem prime_seventySixBV_101467 : Nat.Prime 101467 := by norm_num
private theorem prime_seventySixBV_104911 : Nat.Prime 104911 := by norm_num
private theorem prime_seventySixBV_106109 : Nat.Prime 106109 := by norm_num
private theorem prime_seventySixBV_106787 : Nat.Prime 106787 := by norm_num
private theorem prime_seventySixBV_106961 : Nat.Prime 106961 := by norm_num
private theorem prime_seventySixBV_108191 : Nat.Prime 108191 := by norm_num
private theorem prime_seventySixBV_110323 : Nat.Prime 110323 := by norm_num
private theorem prime_seventySixBV_115019 : Nat.Prime 115019 := by norm_num
private theorem prime_seventySixBV_122267 : Nat.Prime 122267 := by norm_num
private theorem prime_seventySixBV_122327 : Nat.Prime 122327 := by norm_num
private theorem prime_seventySixBV_123493 : Nat.Prime 123493 := by norm_num
private theorem prime_seventySixBV_132949 : Nat.Prime 132949 := by norm_num
private theorem prime_seventySixBV_136889 : Nat.Prime 136889 := by norm_num
private theorem prime_seventySixBV_138739 : Nat.Prime 138739 := by norm_num
private theorem prime_seventySixBV_139333 : Nat.Prime 139333 := by norm_num
private theorem prime_seventySixBV_141209 : Nat.Prime 141209 := by norm_num
private theorem prime_seventySixBV_161303 : Nat.Prime 161303 := by norm_num
private theorem prime_seventySixBV_163909 : Nat.Prime 163909 := by norm_num
private theorem prime_seventySixBV_168277 : Nat.Prime 168277 := by norm_num
private theorem prime_seventySixBV_170327 : Nat.Prime 170327 := by norm_num
private theorem prime_seventySixBV_176849 : Nat.Prime 176849 := by norm_num
private theorem prime_seventySixBV_185551 : Nat.Prime 185551 := by norm_num
private theorem prime_seventySixBV_190321 : Nat.Prime 190321 := by norm_num
private theorem prime_seventySixBV_191057 : Nat.Prime 191057 := by norm_num
private theorem prime_seventySixBV_203549 : Nat.Prime 203549 := by norm_num
private theorem prime_seventySixBV_223637 : Nat.Prime 223637 := by norm_num
private theorem prime_seventySixBV_230693 : Nat.Prime 230693 := by norm_num
private theorem prime_seventySixBV_243851 : Nat.Prime 243851 := by norm_num
private theorem prime_seventySixBV_244939 : Nat.Prime 244939 := by norm_num
private theorem prime_seventySixBV_263953 : Nat.Prime 263953 := by norm_num
private theorem prime_seventySixBV_315247 : Nat.Prime 315247 := by norm_num
private theorem prime_seventySixBV_318743 : Nat.Prime 318743 := by norm_num
private theorem prime_seventySixBV_328579 : Nat.Prime 328579 := by norm_num
private theorem prime_seventySixBV_340789 : Nat.Prime 340789 := by norm_num
private theorem prime_seventySixBV_349933 : Nat.Prime 349933 := by norm_num
private theorem prime_seventySixBV_350783 : Nat.Prime 350783 := by norm_num
private theorem prime_seventySixBV_366161 : Nat.Prime 366161 := by norm_num
private theorem prime_seventySixBV_369961 : Nat.Prime 369961 := by norm_num
private theorem prime_seventySixBV_372871 : Nat.Prime 372871 := by norm_num
private theorem prime_seventySixBV_378283 : Nat.Prime 378283 := by norm_num
private theorem prime_seventySixBV_400391 : Nat.Prime 400391 := by norm_num
private theorem prime_seventySixBV_414607 : Nat.Prime 414607 := by norm_num
private theorem prime_seventySixBV_418993 : Nat.Prime 418993 := by norm_num
private theorem prime_seventySixBV_421177 : Nat.Prime 421177 := by norm_num
private theorem prime_seventySixBV_437629 : Nat.Prime 437629 := by norm_num
private theorem prime_seventySixBV_441257 : Nat.Prime 441257 := by norm_num
private theorem prime_seventySixBV_447779 : Nat.Prime 447779 := by norm_num
private theorem prime_seventySixBV_487307 : Nat.Prime 487307 := by norm_num
private theorem prime_seventySixBV_504197 : Nat.Prime 504197 := by norm_num
private theorem prime_seventySixBV_535391 : Nat.Prime 535391 := by norm_num
private theorem prime_seventySixBV_592157 : Nat.Prime 592157 := by norm_num
private theorem prime_seventySixBV_594827 : Nat.Prime 594827 := by norm_num
private theorem prime_seventySixBV_607493 : Nat.Prime 607493 := by norm_num
private theorem prime_seventySixBV_615269 : Nat.Prime 615269 := by norm_num
private theorem prime_seventySixBV_619589 : Nat.Prime 619589 := by norm_num
private theorem prime_seventySixBV_664973 : Nat.Prime 664973 := by norm_num
private theorem prime_seventySixBV_666269 : Nat.Prime 666269 := by norm_num
private theorem prime_seventySixBV_691693 : Nat.Prime 691693 := by norm_num
private theorem prime_seventySixBV_697397 : Nat.Prime 697397 := by norm_num
private theorem prime_seventySixBV_699649 : Nat.Prime 699649 := by norm_num
private theorem prime_seventySixBV_703331 : Nat.Prime 703331 := by norm_num
private theorem prime_seventySixBV_725519 : Nat.Prime 725519 := by norm_num
private theorem prime_seventySixBV_735019 : Nat.Prime 735019 := by norm_num
private theorem prime_seventySixBV_780211 : Nat.Prime 780211 := by norm_num
private theorem prime_seventySixBV_811919 : Nat.Prime 811919 := by norm_num
private theorem prime_seventySixBV_862559 : Nat.Prime 862559 := by norm_num
private theorem prime_seventySixBV_891629 : Nat.Prime 891629 := by norm_num
private theorem prime_seventySixBV_896101 : Nat.Prime 896101 := by norm_num
private theorem prime_seventySixBV_974177 : Nat.Prime 974177 := by norm_num
private theorem prime_seventySixBV_974749 : Nat.Prime 974749 := by norm_num
private theorem prime_seventySixBV_997097 : Nat.Prime 997097 := by norm_num
private theorem prime_seventySixBV_1009747 : Nat.Prime 1009747 := by norm_num
private theorem prime_seventySixBV_1026947 : Nat.Prime 1026947 := by norm_num
private theorem prime_seventySixBV_1064473 : Nat.Prime 1064473 := by norm_num
private theorem prime_seventySixBV_1145533 : Nat.Prime 1145533 := by norm_num
private theorem prime_seventySixBV_1189919 : Nat.Prime 1189919 := by norm_num
private theorem prime_seventySixBV_1217813 : Nat.Prime 1217813 := by norm_num
private theorem prime_seventySixBV_1220777 : Nat.Prime 1220777 := by norm_num
private theorem prime_seventySixBV_1362997 : Nat.Prime 1362997 := by norm_num
private theorem prime_seventySixBV_1405007 : Nat.Prime 1405007 := by norm_num
private theorem prime_seventySixBV_1463773 : Nat.Prime 1463773 := by norm_num
private theorem prime_seventySixBV_1466719 : Nat.Prime 1466719 := by norm_num
private theorem prime_seventySixBV_1490639 : Nat.Prime 1490639 := by norm_num
private theorem prime_seventySixBV_1535041 : Nat.Prime 1535041 := by norm_num
private theorem prime_seventySixBV_1653599 : Nat.Prime 1653599 := by norm_num
private theorem prime_seventySixBV_1670303 : Nat.Prime 1670303 := by norm_num
private theorem prime_seventySixBV_1699499 : Nat.Prime 1699499 := by norm_num
private theorem prime_seventySixBV_1783009 : Nat.Prime 1783009 := by norm_num
private theorem prime_seventySixBV_1794349 : Nat.Prime 1794349 := by norm_num
private theorem prime_seventySixBV_1881641 : Nat.Prime 1881641 := by norm_num
private theorem prime_seventySixBV_1913959 : Nat.Prime 1913959 := by norm_num
private theorem prime_seventySixBV_2006891 : Nat.Prime 2006891 := by norm_num
private theorem prime_seventySixBV_2123141 : Nat.Prime 2123141 := by norm_num
private theorem prime_seventySixBV_2255899 : Nat.Prime 2255899 := by norm_num
private theorem prime_seventySixBV_2515673 : Nat.Prime 2515673 := by norm_num
private theorem prime_seventySixBV_2517061 : Nat.Prime 2517061 := by norm_num
private theorem prime_seventySixBV_2636453 : Nat.Prime 2636453 := by norm_num
private theorem prime_seventySixBV_2696779 : Nat.Prime 2696779 := by norm_num
private theorem prime_seventySixBV_2766713 : Nat.Prime 2766713 := by norm_num
private theorem prime_seventySixBV_2816269 : Nat.Prime 2816269 := by norm_num
private theorem prime_seventySixBV_3125051 : Nat.Prime 3125051 := by norm_num
private theorem prime_seventySixBV_3370957 : Nat.Prime 3370957 := by norm_num
private theorem prime_seventySixBV_3653603 : Nat.Prime 3653603 := by norm_num
private theorem prime_seventySixBV_3991807 : Nat.Prime 3991807 := by norm_num
private theorem prime_seventySixBV_4003361 : Nat.Prime 4003361 := by norm_num
private theorem prime_seventySixBV_4088957 : Nat.Prime 4088957 := by norm_num
private theorem prime_seventySixBV_5200451 : Nat.Prime 5200451 := by norm_num
private theorem prime_seventySixBV_5394097 : Nat.Prime 5394097 := by norm_num
private theorem prime_seventySixBV_5527901 : Nat.Prime 5527901 := by norm_num
private theorem prime_seventySixBV_5653601 : Nat.Prime 5653601 := by norm_num
private theorem prime_seventySixBV_6192113 : Nat.Prime 6192113 := by norm_num
private theorem prime_seventySixBV_6982793 : Nat.Prime 6982793 := by norm_num
private theorem prime_seventySixBV_7100383 : Nat.Prime 7100383 := by norm_num
private theorem prime_seventySixBV_7384877 : Nat.Prime 7384877 := by norm_num
private theorem prime_seventySixBV_7528363 : Nat.Prime 7528363 := by norm_num
private theorem prime_seventySixBV_7681939 : Nat.Prime 7681939 := by norm_num
private theorem prime_seventySixBV_7888607 : Nat.Prime 7888607 := by norm_num
private theorem prime_seventySixBV_8112493 : Nat.Prime 8112493 := by norm_num
private theorem prime_seventySixBV_9048163 : Nat.Prime 9048163 := by norm_num
private theorem prime_seventySixBV_9145291 : Nat.Prime 9145291 := by norm_num
private theorem prime_seventySixBV_9361459 : Nat.Prime 9361459 := by norm_num
private theorem prime_seventySixBV_10796459 : Nat.Prime 10796459 := by norm_num
private theorem prime_seventySixBV_10877693 : Nat.Prime 10877693 := by norm_num
private theorem prime_seventySixBV_11572261 : Nat.Prime 11572261 := by norm_num
private theorem prime_seventySixBV_11686303 : Nat.Prime 11686303 := by norm_num
private theorem prime_seventySixBV_11918981 : Nat.Prime 11918981 := by norm_num
private theorem prime_seventySixBV_13000187 : Nat.Prime 13000187 := by norm_num
private theorem prime_seventySixBV_14373659 : Nat.Prime 14373659 := by norm_num
private theorem prime_seventySixBV_17901113 : Nat.Prime 17901113 := by norm_num
private theorem prime_seventySixBV_17943511 : Nat.Prime 17943511 := by norm_num
private theorem prime_seventySixBV_17973443 : Nat.Prime 17973443 := by norm_num
private theorem prime_seventySixBV_18177881 : Nat.Prime 18177881 := by norm_num
private theorem prime_seventySixBV_18294803 : Nat.Prime 18294803 := by norm_num
private theorem prime_seventySixBV_18321839 : Nat.Prime 18321839 := by norm_num
private theorem prime_seventySixBV_18688399 : Nat.Prime 18688399 := by norm_num
private theorem prime_seventySixBV_18704263 : Nat.Prime 18704263 := by norm_num
private theorem prime_seventySixBV_20932981 : Nat.Prime 20932981 := by norm_num
private theorem prime_seventySixBV_21414277 : Nat.Prime 21414277 := by norm_num
private theorem prime_seventySixBV_22605857 : Nat.Prime 22605857 := by norm_num
private theorem prime_seventySixBV_22810441 : Nat.Prime 22810441 := by norm_num
private theorem prime_seventySixBV_22937623 : Nat.Prime 22937623 := by norm_num
private theorem prime_seventySixBV_28856209 : Nat.Prime 28856209 := by norm_num
private theorem prime_seventySixBV_29510917 : Nat.Prime 29510917 := by norm_num
private theorem prime_seventySixBV_30192251 : Nat.Prime 30192251 := by
  apply lucas_primality 30192251 (6 : ZMod 30192251)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 3), (11, 1), (10979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 3), (11, 1), (10979, 1)] : List FactorBlock).map factorBlockValue).prod) = 30192251 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_5
      · exact prime_seventySixBV_11
      · exact prime_seventySixBV_10979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 30192251) ^ 15096125 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (6 : ZMod 30192251) ^ 6038450 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (6 : ZMod 30192251) ^ 2744750 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (6 : ZMod 30192251) ^ 2750 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_30241459 : Nat.Prime 30241459 := by
  apply lucas_primality 30241459 (3 : ZMod 30241459)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (13, 1), (23, 1), (1873, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (13, 1), (23, 1), (1873, 1)] : List FactorBlock).map factorBlockValue).prod) = 30241459 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_13
      · exact prime_seventySixBV_23
      · exact prime_seventySixBV_1873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 30241459) ^ 15120729 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 30241459) ^ 10080486 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 30241459) ^ 2326266 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 30241459) ^ 1314846 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 30241459) ^ 16146 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_30870799 : Nat.Prime 30870799 := by
  apply lucas_primality 30870799 (3 : ZMod 30870799)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (735019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (735019, 1)] : List FactorBlock).map factorBlockValue).prod) = 30870799 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_7
      · exact prime_seventySixBV_735019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 30870799) ^ 15435399 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 30870799) ^ 10290266 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 30870799) ^ 4410114 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 30870799) ^ 42 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_34441261 : Nat.Prime 34441261 := by
  apply lucas_primality 34441261 (2 : ZMod 34441261)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (82003, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (82003, 1)] : List FactorBlock).map factorBlockValue).prod) = 34441261 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_5
      · exact prime_seventySixBV_7
      · exact prime_seventySixBV_82003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 34441261) ^ 17220630 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 34441261) ^ 11480420 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 34441261) ^ 6888252 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 34441261) ^ 4920180 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 34441261) ^ 420 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_35016103 : Nat.Prime 35016103 := by
  apply lucas_primality 35016103 (5 : ZMod 35016103)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (176849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (176849, 1)] : List FactorBlock).map factorBlockValue).prod) = 35016103 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_11
      · exact prime_seventySixBV_176849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 35016103) ^ 17508051 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 35016103) ^ 11672034 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 35016103) ^ 3183282 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 35016103) ^ 198 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_38065309 : Nat.Prime 38065309 := by
  apply lucas_primality 38065309 (10 : ZMod 38065309)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (877, 1), (3617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (877, 1), (3617, 1)] : List FactorBlock).map factorBlockValue).prod) = 38065309 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_877
      · exact prime_seventySixBV_3617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 38065309) ^ 19032654 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (10 : ZMod 38065309) ^ 12688436 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (10 : ZMod 38065309) ^ 43404 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (10 : ZMod 38065309) ^ 10524 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_40051933 : Nat.Prime 40051933 := by
  apply lucas_primality 40051933 (6 : ZMod 40051933)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 2), (11549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 2), (11549, 1)] : List FactorBlock).map factorBlockValue).prod) = 40051933 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_17
      · exact prime_seventySixBV_11549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 40051933) ^ 20025966 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (6 : ZMod 40051933) ^ 13350644 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (6 : ZMod 40051933) ^ 2355996 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (6 : ZMod 40051933) ^ 3468 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_43562557 : Nat.Prime 43562557 := by
  apply lucas_primality 43562557 (2 : ZMod 43562557)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (251, 1), (1607, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (251, 1), (1607, 1)] : List FactorBlock).map factorBlockValue).prod) = 43562557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_251
      · exact prime_seventySixBV_1607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 43562557) ^ 21781278 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 43562557) ^ 14520852 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 43562557) ^ 173556 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 43562557) ^ 27108 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_49375483 : Nat.Prime 49375483 := by
  apply lucas_primality 49375483 (12 : ZMod 49375483)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (199, 1), (3181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (199, 1), (3181, 1)] : List FactorBlock).map factorBlockValue).prod) = 49375483 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_13
      · exact prime_seventySixBV_199
      · exact prime_seventySixBV_3181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (12 : ZMod 49375483) ^ 24687741 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (12 : ZMod 49375483) ^ 16458494 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (12 : ZMod 49375483) ^ 3798114 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (12 : ZMod 49375483) ^ 248118 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (12 : ZMod 49375483) ^ 15522 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_58831103 : Nat.Prime 58831103 := by
  apply lucas_primality 58831103 (7 : ZMod 58831103)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (23, 1), (233, 1), (499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (23, 1), (233, 1), (499, 1)] : List FactorBlock).map factorBlockValue).prod) = 58831103 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_11
      · exact prime_seventySixBV_23
      · exact prime_seventySixBV_233
      · exact prime_seventySixBV_499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 58831103) ^ 29415551 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (7 : ZMod 58831103) ^ 5348282 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (7 : ZMod 58831103) ^ 2557874 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (7 : ZMod 58831103) ^ 252494 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (7 : ZMod 58831103) ^ 117898 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_59079017 : Nat.Prime 59079017 := by
  apply lucas_primality 59079017 (3 : ZMod 59079017)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7384877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7384877, 1)] : List FactorBlock).map factorBlockValue).prod) = 59079017 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_7384877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 59079017) ^ 29539508 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 59079017) ^ 8 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_59761717 : Nat.Prime 59761717 := by
  apply lucas_primality 59761717 (2 : ZMod 59761717)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (313, 1), (2273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (313, 1), (2273, 1)] : List FactorBlock).map factorBlockValue).prod) = 59761717 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_7
      · exact prime_seventySixBV_313
      · exact prime_seventySixBV_2273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 59761717) ^ 29880858 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 59761717) ^ 19920572 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 59761717) ^ 8537388 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 59761717) ^ 190932 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 59761717) ^ 26292 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_65731691 : Nat.Prime 65731691 := by
  apply lucas_primality 65731691 (2 : ZMod 65731691)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (29, 1), (67, 1), (199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (29, 1), (67, 1), (199, 1)] : List FactorBlock).map factorBlockValue).prod) = 65731691 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_5
      · exact prime_seventySixBV_17
      · exact prime_seventySixBV_29
      · exact prime_seventySixBV_67
      · exact prime_seventySixBV_199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 65731691) ^ 32865845 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 65731691) ^ 13146338 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 65731691) ^ 3866570 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 65731691) ^ 2266610 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 65731691) ^ 981070 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 65731691) ^ 330310 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_66199877 : Nat.Prime 66199877 := by
  apply lucas_primality 66199877 (3 : ZMod 66199877)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (43, 1), (47, 1), (431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (43, 1), (47, 1), (431, 1)] : List FactorBlock).map factorBlockValue).prod) = 66199877 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_19
      · exact prime_seventySixBV_43
      · exact prime_seventySixBV_47
      · exact prime_seventySixBV_431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 66199877) ^ 33099938 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 66199877) ^ 3484204 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 66199877) ^ 1539532 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 66199877) ^ 1408508 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 66199877) ^ 153596 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_66950113 : Nat.Prime 66950113 := by
  apply lucas_primality 66950113 (10 : ZMod 66950113)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (697397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (697397, 1)] : List FactorBlock).map factorBlockValue).prod) = 66950113 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_697397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 66950113) ^ 33475056 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (10 : ZMod 66950113) ^ 22316704 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (10 : ZMod 66950113) ^ 96 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_69170917 : Nat.Prime 69170917 := by
  apply lucas_primality 69170917 (2 : ZMod 69170917)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (29, 1), (113, 1), (1759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (29, 1), (113, 1), (1759, 1)] : List FactorBlock).map factorBlockValue).prod) = 69170917 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_29
      · exact prime_seventySixBV_113
      · exact prime_seventySixBV_1759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 69170917) ^ 34585458 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 69170917) ^ 23056972 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 69170917) ^ 2385204 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 69170917) ^ 612132 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 69170917) ^ 39324 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_70386301 : Nat.Prime 70386301 := by
  apply lucas_primality 70386301 (2 : ZMod 70386301)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 2), (131, 1), (199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 2), (131, 1), (199, 1)] : List FactorBlock).map factorBlockValue).prod) = 70386301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_5
      · exact prime_seventySixBV_131
      · exact prime_seventySixBV_199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 70386301) ^ 35193150 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 70386301) ^ 23462100 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 70386301) ^ 14077260 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 70386301) ^ 537300 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 70386301) ^ 353700 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_72957697 : Nat.Prime 72957697 := by
  apply lucas_primality 72957697 (11 : ZMod 72957697)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 1), (7, 1), (41, 1), (331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 1), (7, 1), (41, 1), (331, 1)] : List FactorBlock).map factorBlockValue).prod) = 72957697 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_7
      · exact prime_seventySixBV_41
      · exact prime_seventySixBV_331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 72957697) ^ 36478848 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (11 : ZMod 72957697) ^ 24319232 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (11 : ZMod 72957697) ^ 10422528 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (11 : ZMod 72957697) ^ 1779456 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (11 : ZMod 72957697) ^ 220416 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_74350681 : Nat.Prime 74350681 := by
  apply lucas_primality 74350681 (7 : ZMod 74350681)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (619589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (619589, 1)] : List FactorBlock).map factorBlockValue).prod) = 74350681 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_5
      · exact prime_seventySixBV_619589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 74350681) ^ 37175340 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (7 : ZMod 74350681) ^ 24783560 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (7 : ZMod 74350681) ^ 14870136 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (7 : ZMod 74350681) ^ 120 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_76378979 : Nat.Prime 76378979 := by
  apply lucas_primality 76378979 (2 : ZMod 76378979)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (31, 1), (193, 1), (491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (31, 1), (193, 1), (491, 1)] : List FactorBlock).map factorBlockValue).prod) = 76378979 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_13
      · exact prime_seventySixBV_31
      · exact prime_seventySixBV_193
      · exact prime_seventySixBV_491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 76378979) ^ 38189489 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 76378979) ^ 5875306 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 76378979) ^ 2463838 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 76378979) ^ 395746 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 76378979) ^ 155558 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_81933277 : Nat.Prime 81933277 := by
  apply lucas_primality 81933277 (5 : ZMod 81933277)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (157, 2), (277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (157, 2), (277, 1)] : List FactorBlock).map factorBlockValue).prod) = 81933277 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_157
      · exact prime_seventySixBV_277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 81933277) ^ 40966638 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 81933277) ^ 27311092 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 81933277) ^ 521868 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 81933277) ^ 295788 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_82086127 : Nat.Prime 82086127 := by
  apply lucas_primality 82086127 (7 : ZMod 82086127)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (594827, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (594827, 1)] : List FactorBlock).map factorBlockValue).prod) = 82086127 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_23
      · exact prime_seventySixBV_594827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 82086127) ^ 41043063 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (7 : ZMod 82086127) ^ 27362042 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (7 : ZMod 82086127) ^ 3568962 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (7 : ZMod 82086127) ^ 138 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_85236787 : Nat.Prime 85236787 := by
  apply lucas_primality 85236787 (2 : ZMod 85236787)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (41, 2), (313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (41, 2), (313, 1)] : List FactorBlock).map factorBlockValue).prod) = 85236787 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_41
      · exact prime_seventySixBV_313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 85236787) ^ 42618393 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 85236787) ^ 28412262 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 85236787) ^ 2078946 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 85236787) ^ 272322 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_90481631 : Nat.Prime 90481631 := by
  apply lucas_primality 90481631 (7 : ZMod 90481631)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (9048163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (9048163, 1)] : List FactorBlock).map factorBlockValue).prod) = 90481631 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_5
      · exact prime_seventySixBV_9048163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 90481631) ^ 45240815 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (7 : ZMod 90481631) ^ 18096326 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (7 : ZMod 90481631) ^ 10 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_96078893 : Nat.Prime 96078893 := by
  apply lucas_primality 96078893 (3 : ZMod 96078893)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (13, 1), (263953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (13, 1), (263953, 1)] : List FactorBlock).map factorBlockValue).prod) = 96078893 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_7
      · exact prime_seventySixBV_13
      · exact prime_seventySixBV_263953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 96078893) ^ 48039446 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 96078893) ^ 13725556 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 96078893) ^ 7390684 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 96078893) ^ 364 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_97206377 : Nat.Prime 97206377 := by
  apply lucas_primality 97206377 (3 : ZMod 97206377)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (29, 1), (418993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (29, 1), (418993, 1)] : List FactorBlock).map factorBlockValue).prod) = 97206377 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_29
      · exact prime_seventySixBV_418993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 97206377) ^ 48603188 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 97206377) ^ 3351944 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 97206377) ^ 232 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_106003939 : Nat.Prime 106003939 := by
  apply lucas_primality 106003939 (2 : ZMod 106003939)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (79, 1), (223637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (79, 1), (223637, 1)] : List FactorBlock).map factorBlockValue).prod) = 106003939 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_79
      · exact prime_seventySixBV_223637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 106003939) ^ 53001969 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 106003939) ^ 35334646 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 106003939) ^ 1341822 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 106003939) ^ 474 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_112224899 : Nat.Prime 112224899 := by
  apply lucas_primality 112224899 (2 : ZMod 112224899)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (313, 1), (5783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (313, 1), (5783, 1)] : List FactorBlock).map factorBlockValue).prod) = 112224899 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_31
      · exact prime_seventySixBV_313
      · exact prime_seventySixBV_5783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 112224899) ^ 56112449 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 112224899) ^ 3620158 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 112224899) ^ 358546 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 112224899) ^ 19406 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_114553301 : Nat.Prime 114553301 := by
  apply lucas_primality 114553301 (2 : ZMod 114553301)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (1145533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (1145533, 1)] : List FactorBlock).map factorBlockValue).prod) = 114553301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_5
      · exact prime_seventySixBV_1145533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 114553301) ^ 57276650 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 114553301) ^ 22910660 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 114553301) ^ 100 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_123483197 : Nat.Prime 123483197 := by
  apply lucas_primality 123483197 (2 : ZMod 123483197)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (30870799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (30870799, 1)] : List FactorBlock).map factorBlockValue).prod) = 123483197 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_30870799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 123483197) ^ 61741598 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 123483197) ^ 4 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_132379151 : Nat.Prime 132379151 := by
  apply lucas_primality 132379151 (7 : ZMod 132379151)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (61, 1), (43403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (61, 1), (43403, 1)] : List FactorBlock).map factorBlockValue).prod) = 132379151 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_5
      · exact prime_seventySixBV_61
      · exact prime_seventySixBV_43403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 132379151) ^ 66189575 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (7 : ZMod 132379151) ^ 26475830 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (7 : ZMod 132379151) ^ 2170150 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (7 : ZMod 132379151) ^ 3050 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_138335651 : Nat.Prime 138335651 := by
  apply lucas_primality 138335651 (2 : ZMod 138335651)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (2766713, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (2766713, 1)] : List FactorBlock).map factorBlockValue).prod) = 138335651 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_5
      · exact prime_seventySixBV_2766713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 138335651) ^ 69167825 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 138335651) ^ 27667130 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 138335651) ^ 50 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_140064413 : Nat.Prime 140064413 := by
  apply lucas_primality 140064413 (2 : ZMod 140064413)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (35016103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (35016103, 1)] : List FactorBlock).map factorBlockValue).prod) = 140064413 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_35016103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 140064413) ^ 70032206 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 140064413) ^ 4 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_144901709 : Nat.Prime 144901709 := by
  apply lucas_primality 144901709 (2 : ZMod 144901709)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (41, 1), (113, 1), (1117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (41, 1), (113, 1), (1117, 1)] : List FactorBlock).map factorBlockValue).prod) = 144901709 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_7
      · exact prime_seventySixBV_41
      · exact prime_seventySixBV_113
      · exact prime_seventySixBV_1117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 144901709) ^ 72450854 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 144901709) ^ 20700244 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 144901709) ^ 3534188 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 144901709) ^ 1282316 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 144901709) ^ 129724 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_150761669 : Nat.Prime 150761669 := by
  apply lucas_primality 150761669 (2 : ZMod 150761669)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (97, 1), (337, 1), (1153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (97, 1), (337, 1), (1153, 1)] : List FactorBlock).map factorBlockValue).prod) = 150761669 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_97
      · exact prime_seventySixBV_337
      · exact prime_seventySixBV_1153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 150761669) ^ 75380834 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 150761669) ^ 1554244 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 150761669) ^ 447364 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 150761669) ^ 130756 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_152757959 : Nat.Prime 152757959 := by
  apply lucas_primality 152757959 (7 : ZMod 152757959)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (76378979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (76378979, 1)] : List FactorBlock).map factorBlockValue).prod) = 152757959 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_76378979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (7 : ZMod 152757959) ^ 76378979 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (7 : ZMod 152757959) ^ 2 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_162551611 : Nat.Prime 162551611 := by
  apply lucas_primality 162551611 (2 : ZMod 162551611)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (5, 1), (13, 1), (43, 1), (359, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (5, 1), (13, 1), (43, 1), (359, 1)] : List FactorBlock).map factorBlockValue).prod) = 162551611 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_5
      · exact prime_seventySixBV_13
      · exact prime_seventySixBV_43
      · exact prime_seventySixBV_359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 162551611) ^ 81275805 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 162551611) ^ 54183870 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 162551611) ^ 32510322 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 162551611) ^ 12503970 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 162551611) ^ 3780270 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 162551611) ^ 452790 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_171348337 : Nat.Prime 171348337 := by
  apply lucas_primality 171348337 (5 : ZMod 171348337)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (1189919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (1189919, 1)] : List FactorBlock).map factorBlockValue).prod) = 171348337 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_1189919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 171348337) ^ 85674168 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 171348337) ^ 57116112 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 171348337) ^ 144 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_179154791 : Nat.Prime 179154791 := by
  apply lucas_primality 179154791 (7 : ZMod 179154791)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (3847, 1), (4657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (3847, 1), (4657, 1)] : List FactorBlock).map factorBlockValue).prod) = 179154791 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_5
      · exact prime_seventySixBV_3847
      · exact prime_seventySixBV_4657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 179154791) ^ 89577395 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (7 : ZMod 179154791) ^ 35830958 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (7 : ZMod 179154791) ^ 46570 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (7 : ZMod 179154791) ^ 38470 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_179928713 : Nat.Prime 179928713 := by
  apply lucas_primality 179928713 (3 : ZMod 179928713)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (31, 1), (725519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (31, 1), (725519, 1)] : List FactorBlock).map factorBlockValue).prod) = 179928713 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_31
      · exact prime_seventySixBV_725519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 179928713) ^ 89964356 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 179928713) ^ 5804152 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 179928713) ^ 248 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_180482117 : Nat.Prime 180482117 := by
  apply lucas_primality 180482117 (2 : ZMod 180482117)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (907, 1), (49747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (907, 1), (49747, 1)] : List FactorBlock).map factorBlockValue).prod) = 180482117 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_907
      · exact prime_seventySixBV_49747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 180482117) ^ 90241058 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 180482117) ^ 198988 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 180482117) ^ 3628 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_186963809 : Nat.Prime 186963809 := by
  apply lucas_primality 186963809 (3 : ZMod 186963809)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (83, 1), (70393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (83, 1), (70393, 1)] : List FactorBlock).map factorBlockValue).prod) = 186963809 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_83
      · exact prime_seventySixBV_70393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 186963809) ^ 93481904 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 186963809) ^ 2252576 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 186963809) ^ 2656 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_196845977 : Nat.Prime 196845977 := by
  apply lucas_primality 196845977 (3 : ZMod 196845977)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (1637, 1), (15031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (1637, 1), (15031, 1)] : List FactorBlock).map factorBlockValue).prod) = 196845977 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_1637
      · exact prime_seventySixBV_15031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 196845977) ^ 98422988 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 196845977) ^ 120248 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 196845977) ^ 13096 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_211351817 : Nat.Prime 211351817 := by
  apply lucas_primality 211351817 (3 : ZMod 211351817)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (271, 1), (7499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (271, 1), (7499, 1)] : List FactorBlock).map factorBlockValue).prod) = 211351817 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_13
      · exact prime_seventySixBV_271
      · exact prime_seventySixBV_7499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 211351817) ^ 105675908 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 211351817) ^ 16257832 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 211351817) ^ 779896 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 211351817) ^ 28184 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_218490499 : Nat.Prime 218490499 := by
  apply lucas_primality 218490499 (10 : ZMod 218490499)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (47, 1), (271, 1), (953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (47, 1), (271, 1), (953, 1)] : List FactorBlock).map factorBlockValue).prod) = 218490499 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_47
      · exact prime_seventySixBV_271
      · exact prime_seventySixBV_953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 218490499) ^ 109245249 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (10 : ZMod 218490499) ^ 72830166 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (10 : ZMod 218490499) ^ 4648734 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (10 : ZMod 218490499) ^ 806238 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (10 : ZMod 218490499) ^ 229266 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_224619803 : Nat.Prime 224619803 := by
  apply lucas_primality 224619803 (2 : ZMod 224619803)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 2), (89, 1), (10429, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 2), (89, 1), (10429, 1)] : List FactorBlock).map factorBlockValue).prod) = 224619803 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_11
      · exact prime_seventySixBV_89
      · exact prime_seventySixBV_10429
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 224619803) ^ 112309901 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 224619803) ^ 20419982 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 224619803) ^ 2523818 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 224619803) ^ 21538 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_249048871 : Nat.Prime 249048871 := by
  apply lucas_primality 249048871 (3 : ZMod 249048871)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 3), (24203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 3), (24203, 1)] : List FactorBlock).map factorBlockValue).prod) = 249048871 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_5
      · exact prime_seventySixBV_7
      · exact prime_seventySixBV_24203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 249048871) ^ 124524435 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 249048871) ^ 83016290 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 249048871) ^ 49809774 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 249048871) ^ 35578410 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 249048871) ^ 10290 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_283424129 : Nat.Prime 283424129 := by
  apply lucas_primality 283424129 (3 : ZMod 283424129)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (13, 1), (170327, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (13, 1), (170327, 1)] : List FactorBlock).map factorBlockValue).prod) = 283424129 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_13
      · exact prime_seventySixBV_170327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 283424129) ^ 141712064 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 283424129) ^ 21801856 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 283424129) ^ 1664 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_289803419 : Nat.Prime 289803419 := by
  apply lucas_primality 289803419 (2 : ZMod 289803419)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (144901709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (144901709, 1)] : List FactorBlock).map factorBlockValue).prod) = 289803419 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_144901709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 289803419) ^ 144901709 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 289803419) ^ 2 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_310676929 : Nat.Prime 310676929 := by
  apply lucas_primality 310676929 (11 : ZMod 310676929)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (89, 1), (18181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (89, 1), (18181, 1)] : List FactorBlock).map factorBlockValue).prod) = 310676929 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_89
      · exact prime_seventySixBV_18181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 310676929) ^ 155338464 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (11 : ZMod 310676929) ^ 103558976 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (11 : ZMod 310676929) ^ 3490752 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (11 : ZMod 310676929) ^ 17088 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_325060301 : Nat.Prime 325060301 := by
  apply lucas_primality 325060301 (2 : ZMod 325060301)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (41, 1), (79283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (41, 1), (79283, 1)] : List FactorBlock).map factorBlockValue).prod) = 325060301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_5
      · exact prime_seventySixBV_41
      · exact prime_seventySixBV_79283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 325060301) ^ 162530150 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 325060301) ^ 65012060 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 325060301) ^ 7928300 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 325060301) ^ 4100 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_327369611 : Nat.Prime 327369611 := by
  apply lucas_primality 327369611 (2 : ZMod 327369611)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (31, 1), (739, 1), (1429, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (31, 1), (739, 1), (1429, 1)] : List FactorBlock).map factorBlockValue).prod) = 327369611 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_5
      · exact prime_seventySixBV_31
      · exact prime_seventySixBV_739
      · exact prime_seventySixBV_1429
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 327369611) ^ 163684805 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 327369611) ^ 65473922 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 327369611) ^ 10560310 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 327369611) ^ 442990 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 327369611) ^ 229090 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_336373469 : Nat.Prime 336373469 := by
  apply lucas_primality 336373469 (2 : ZMod 336373469)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (79, 1), (1064473, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (79, 1), (1064473, 1)] : List FactorBlock).map factorBlockValue).prod) = 336373469 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_79
      · exact prime_seventySixBV_1064473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 336373469) ^ 168186734 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 336373469) ^ 4257892 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 336373469) ^ 316 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_393327173 : Nat.Prime 393327173 := by
  apply lucas_primality 393327173 (2 : ZMod 393327173)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (307, 1), (45757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (307, 1), (45757, 1)] : List FactorBlock).map factorBlockValue).prod) = 393327173 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_7
      · exact prime_seventySixBV_307
      · exact prime_seventySixBV_45757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 393327173) ^ 196663586 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 393327173) ^ 56189596 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 393327173) ^ 1281196 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 393327173) ^ 8596 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_402497257 : Nat.Prime 402497257 := by
  apply lucas_primality 402497257 (5 : ZMod 402497257)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (461, 1), (5197, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (461, 1), (5197, 1)] : List FactorBlock).map factorBlockValue).prod) = 402497257 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_7
      · exact prime_seventySixBV_461
      · exact prime_seventySixBV_5197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 402497257) ^ 201248628 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 402497257) ^ 134165752 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 402497257) ^ 57499608 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 402497257) ^ 873096 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 402497257) ^ 77448 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_413295133 : Nat.Prime 413295133 := by
  apply lucas_primality 413295133 (5 : ZMod 413295133)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (34441261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (34441261, 1)] : List FactorBlock).map factorBlockValue).prod) = 413295133 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_34441261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 413295133) ^ 206647566 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 413295133) ^ 137765044 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 413295133) ^ 12 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_415882073 : Nat.Prime 415882073 := by
  apply lucas_primality 415882073 (3 : ZMod 415882073)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (37, 1), (1405007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (37, 1), (1405007, 1)] : List FactorBlock).map factorBlockValue).prod) = 415882073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_37
      · exact prime_seventySixBV_1405007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 415882073) ^ 207941036 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 415882073) ^ 11240056 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 415882073) ^ 296 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_420392737 : Nat.Prime 420392737 := by
  apply lucas_primality 420392737 (5 : ZMod 420392737)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (31, 1), (47087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (31, 1), (47087, 1)] : List FactorBlock).map factorBlockValue).prod) = 420392737 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_31
      · exact prime_seventySixBV_47087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 420392737) ^ 210196368 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 420392737) ^ 140130912 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 420392737) ^ 13561056 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 420392737) ^ 8928 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_502086631 : Nat.Prime 502086631 := by
  apply lucas_primality 502086631 (3 : ZMod 502086631)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (359, 1), (46619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (359, 1), (46619, 1)] : List FactorBlock).map factorBlockValue).prod) = 502086631 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_5
      · exact prime_seventySixBV_359
      · exact prime_seventySixBV_46619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 502086631) ^ 251043315 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 502086631) ^ 167362210 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 502086631) ^ 100417326 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 502086631) ^ 1398570 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 502086631) ^ 10770 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_531258671 : Nat.Prime 531258671 := by
  apply lucas_primality 531258671 (11 : ZMod 531258671)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (3125051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (3125051, 1)] : List FactorBlock).map factorBlockValue).prod) = 531258671 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_5
      · exact prime_seventySixBV_17
      · exact prime_seventySixBV_3125051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 531258671) ^ 265629335 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (11 : ZMod 531258671) ^ 106251734 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (11 : ZMod 531258671) ^ 31250510 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (11 : ZMod 531258671) ^ 170 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_537033391 : Nat.Prime 537033391 := by
  apply lucas_primality 537033391 (6 : ZMod 537033391)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (17901113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (17901113, 1)] : List FactorBlock).map factorBlockValue).prod) = 537033391 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_5
      · exact prime_seventySixBV_17901113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 537033391) ^ 268516695 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (6 : ZMod 537033391) ^ 179011130 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (6 : ZMod 537033391) ^ 107406678 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (6 : ZMod 537033391) ^ 30 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_685393349 : Nat.Prime 685393349 := by
  apply lucas_primality 685393349 (2 : ZMod 685393349)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (171348337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (171348337, 1)] : List FactorBlock).map factorBlockValue).prod) = 685393349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_171348337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 685393349) ^ 342696674 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 685393349) ^ 4 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_686631349 : Nat.Prime 686631349 := by
  apply lucas_primality 686631349 (17 : ZMod 686631349)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (13, 1), (19, 1), (37, 1), (2087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (13, 1), (19, 1), (37, 1), (2087, 1)] : List FactorBlock).map factorBlockValue).prod) = 686631349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_13
      · exact prime_seventySixBV_19
      · exact prime_seventySixBV_37
      · exact prime_seventySixBV_2087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 686631349) ^ 343315674 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (17 : ZMod 686631349) ^ 228877116 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (17 : ZMod 686631349) ^ 52817796 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (17 : ZMod 686631349) ^ 36138492 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (17 : ZMod 686631349) ^ 18557604 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (17 : ZMod 686631349) ^ 329004 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_687640277 : Nat.Prime 687640277 := by
  apply lucas_primality 687640277 (2 : ZMod 687640277)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (163, 1), (62039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (163, 1), (62039, 1)] : List FactorBlock).map factorBlockValue).prod) = 687640277 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_17
      · exact prime_seventySixBV_163
      · exact prime_seventySixBV_62039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 687640277) ^ 343820138 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 687640277) ^ 40449428 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 687640277) ^ 4218652 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 687640277) ^ 11084 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_831764147 : Nat.Prime 831764147 := by
  apply lucas_primality 831764147 (2 : ZMod 831764147)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (415882073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (415882073, 1)] : List FactorBlock).map factorBlockValue).prod) = 831764147 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_415882073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 831764147) ^ 415882073 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 831764147) ^ 2 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_913954091 : Nat.Prime 913954091 := by
  apply lucas_primality 913954091 (2 : ZMod 913954091)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (31, 1), (421177, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (31, 1), (421177, 1)] : List FactorBlock).map factorBlockValue).prod) = 913954091 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_5
      · exact prime_seventySixBV_7
      · exact prime_seventySixBV_31
      · exact prime_seventySixBV_421177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 913954091) ^ 456977045 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 913954091) ^ 182790818 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 913954091) ^ 130564870 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 913954091) ^ 29482390 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 913954091) ^ 2170 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_917046857 : Nat.Prime 917046857 := by
  apply lucas_primality 917046857 (3 : ZMod 917046857)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (19, 2), (28867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (19, 2), (28867, 1)] : List FactorBlock).map factorBlockValue).prod) = 917046857 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_11
      · exact prime_seventySixBV_19
      · exact prime_seventySixBV_28867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 917046857) ^ 458523428 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 917046857) ^ 83367896 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 917046857) ^ 48265624 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 917046857) ^ 31768 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_1340004007 : Nat.Prime 1340004007 := by
  apply lucas_primality 1340004007 (5 : ZMod 1340004007)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (11, 1), (2255899, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (11, 1), (2255899, 1)] : List FactorBlock).map factorBlockValue).prod) = 1340004007 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_11
      · exact prime_seventySixBV_2255899
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1340004007) ^ 670002003 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 1340004007) ^ 446668002 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 1340004007) ^ 121818546 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 1340004007) ^ 594 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_1378106687 : Nat.Prime 1378106687 := by
  apply lucas_primality 1378106687 (5 : ZMod 1378106687)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (23, 1), (409, 1), (6659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (23, 1), (409, 1), (6659, 1)] : List FactorBlock).map factorBlockValue).prod) = 1378106687 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_11
      · exact prime_seventySixBV_23
      · exact prime_seventySixBV_409
      · exact prime_seventySixBV_6659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1378106687) ^ 689053343 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 1378106687) ^ 125282426 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 1378106687) ^ 59917682 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 1378106687) ^ 3369454 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 1378106687) ^ 206954 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_1423743271 : Nat.Prime 1423743271 := by
  apply lucas_primality 1423743271 (3 : ZMod 1423743271)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (47, 1), (1009747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (47, 1), (1009747, 1)] : List FactorBlock).map factorBlockValue).prod) = 1423743271 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_5
      · exact prime_seventySixBV_47
      · exact prime_seventySixBV_1009747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1423743271) ^ 711871635 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1423743271) ^ 474581090 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1423743271) ^ 284748654 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1423743271) ^ 30292410 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1423743271) ^ 1410 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_1468545787 : Nat.Prime 1468545787 := by
  apply lucas_primality 1468545787 (2 : ZMod 1468545787)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5737, 1), (14221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5737, 1), (14221, 1)] : List FactorBlock).map factorBlockValue).prod) = 1468545787 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_5737
      · exact prime_seventySixBV_14221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1468545787) ^ 734272893 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1468545787) ^ 489515262 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1468545787) ^ 255978 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1468545787) ^ 103266 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_1497208789 : Nat.Prime 1497208789 := by
  apply lucas_primality 1497208789 (2 : ZMod 1497208789)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (4813, 1), (8641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (4813, 1), (8641, 1)] : List FactorBlock).map factorBlockValue).prod) = 1497208789 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_4813
      · exact prime_seventySixBV_8641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1497208789) ^ 748604394 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1497208789) ^ 499069596 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1497208789) ^ 311076 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1497208789) ^ 173268 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_1613207191 : Nat.Prime 1613207191 := by
  apply lucas_primality 1613207191 (12 : ZMod 1613207191)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (7681939, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (7681939, 1)] : List FactorBlock).map factorBlockValue).prod) = 1613207191 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_5
      · exact prime_seventySixBV_7
      · exact prime_seventySixBV_7681939
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (12 : ZMod 1613207191) ^ 806603595 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (12 : ZMod 1613207191) ^ 537735730 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (12 : ZMod 1613207191) ^ 322641438 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (12 : ZMod 1613207191) ^ 230458170 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (12 : ZMod 1613207191) ^ 210 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_1625516111 : Nat.Prime 1625516111 := by
  apply lucas_primality 1625516111 (7 : ZMod 1625516111)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (162551611, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (162551611, 1)] : List FactorBlock).map factorBlockValue).prod) = 1625516111 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_5
      · exact prime_seventySixBV_162551611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 1625516111) ^ 812758055 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (7 : ZMod 1625516111) ^ 325103222 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (7 : ZMod 1625516111) ^ 10 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_1913722493 : Nat.Prime 1913722493 := by
  apply lucas_primality 1913722493 (2 : ZMod 1913722493)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (5197, 1), (8369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (5197, 1), (8369, 1)] : List FactorBlock).map factorBlockValue).prod) = 1913722493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_11
      · exact prime_seventySixBV_5197
      · exact prime_seventySixBV_8369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1913722493) ^ 956861246 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1913722493) ^ 173974772 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1913722493) ^ 368236 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1913722493) ^ 228668 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_2165291893 : Nat.Prime 2165291893 := by
  apply lucas_primality 2165291893 (2 : ZMod 2165291893)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (53, 1), (378283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (53, 1), (378283, 1)] : List FactorBlock).map factorBlockValue).prod) = 2165291893 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_53
      · exact prime_seventySixBV_378283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2165291893) ^ 1082645946 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2165291893) ^ 721763964 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2165291893) ^ 40854564 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2165291893) ^ 5724 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_2167266461 : Nat.Prime 2167266461 := by
  apply lucas_primality 2167266461 (2 : ZMod 2167266461)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (53, 1), (409, 1), (4999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (53, 1), (409, 1), (4999, 1)] : List FactorBlock).map factorBlockValue).prod) = 2167266461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_5
      · exact prime_seventySixBV_53
      · exact prime_seventySixBV_409
      · exact prime_seventySixBV_4999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2167266461) ^ 1083633230 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2167266461) ^ 433453292 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2167266461) ^ 40891820 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2167266461) ^ 5298940 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2167266461) ^ 433540 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_2573783231 : Nat.Prime 2573783231 := by
  apply lucas_primality 2573783231 (13 : ZMod 2573783231)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (317, 1), (811919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (317, 1), (811919, 1)] : List FactorBlock).map factorBlockValue).prod) = 2573783231 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_5
      · exact prime_seventySixBV_317
      · exact prime_seventySixBV_811919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 2573783231) ^ 1286891615 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (13 : ZMod 2573783231) ^ 514756646 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (13 : ZMod 2573783231) ^ 8119190 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (13 : ZMod 2573783231) ^ 3170 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_2988586453 : Nat.Prime 2988586453 := by
  apply lucas_primality 2988586453 (2 : ZMod 2988586453)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (249048871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (249048871, 1)] : List FactorBlock).map factorBlockValue).prod) = 2988586453 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_249048871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2988586453) ^ 1494293226 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2988586453) ^ 996195484 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2988586453) ^ 12 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_3144677243 : Nat.Prime 3144677243 := by
  apply lucas_primality 3144677243 (5 : ZMod 3144677243)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (224619803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (224619803, 1)] : List FactorBlock).map factorBlockValue).prod) = 3144677243 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_7
      · exact prime_seventySixBV_224619803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 3144677243) ^ 1572338621 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 3144677243) ^ 449239606 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 3144677243) ^ 14 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_3295014659 : Nat.Prime 3295014659 := by
  apply lucas_primality 3295014659 (2 : ZMod 3295014659)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (683, 1), (185551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (683, 1), (185551, 1)] : List FactorBlock).map factorBlockValue).prod) = 3295014659 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_13
      · exact prime_seventySixBV_683
      · exact prime_seventySixBV_185551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3295014659) ^ 1647507329 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 3295014659) ^ 253462666 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 3295014659) ^ 4824326 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 3295014659) ^ 17758 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_3550989341 : Nat.Prime 3550989341 := by
  apply lucas_primality 3550989341 (3 : ZMod 3550989341)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (59, 1), (61, 1), (49333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (59, 1), (61, 1), (49333, 1)] : List FactorBlock).map factorBlockValue).prod) = 3550989341 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_5
      · exact prime_seventySixBV_59
      · exact prime_seventySixBV_61
      · exact prime_seventySixBV_49333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3550989341) ^ 1775494670 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 3550989341) ^ 710197868 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 3550989341) ^ 60186260 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 3550989341) ^ 58212940 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 3550989341) ^ 71980 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_3750874823 : Nat.Prime 3750874823 := by
  apply lucas_primality 3750874823 (10 : ZMod 3750874823)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (31, 1), (587, 1), (4481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (31, 1), (587, 1), (4481, 1)] : List FactorBlock).map factorBlockValue).prod) = 3750874823 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_23
      · exact prime_seventySixBV_31
      · exact prime_seventySixBV_587
      · exact prime_seventySixBV_4481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 3750874823) ^ 1875437411 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (10 : ZMod 3750874823) ^ 163081514 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (10 : ZMod 3750874823) ^ 120995962 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (10 : ZMod 3750874823) ^ 6389906 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (10 : ZMod 3750874823) ^ 837062 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_3887874511 : Nat.Prime 3887874511 := by
  apply lucas_primality 3887874511 (3 : ZMod 3887874511)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (13, 1), (2333, 1), (4273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (13, 1), (2333, 1), (4273, 1)] : List FactorBlock).map factorBlockValue).prod) = 3887874511 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_5
      · exact prime_seventySixBV_13
      · exact prime_seventySixBV_2333
      · exact prime_seventySixBV_4273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3887874511) ^ 1943937255 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 3887874511) ^ 1295958170 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 3887874511) ^ 777574902 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 3887874511) ^ 299067270 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 3887874511) ^ 1666470 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 3887874511) ^ 909870 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_5746028891 : Nat.Prime 5746028891 := by
  apply lucas_primality 5746028891 (6 : ZMod 5746028891)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (82086127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (82086127, 1)] : List FactorBlock).map factorBlockValue).prod) = 5746028891 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_5
      · exact prime_seventySixBV_7
      · exact prime_seventySixBV_82086127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 5746028891) ^ 2873014445 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (6 : ZMod 5746028891) ^ 1149205778 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (6 : ZMod 5746028891) ^ 820861270 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (6 : ZMod 5746028891) ^ 70 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_5791139377 : Nat.Prime 5791139377 := by
  apply lucas_primality 5791139377 (10 : ZMod 5791139377)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (11, 2), (997097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (11, 2), (997097, 1)] : List FactorBlock).map factorBlockValue).prod) = 5791139377 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_11
      · exact prime_seventySixBV_997097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 5791139377) ^ 2895569688 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (10 : ZMod 5791139377) ^ 1930379792 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (10 : ZMod 5791139377) ^ 526467216 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (10 : ZMod 5791139377) ^ 5808 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_6188642267 : Nat.Prime 6188642267 := by
  apply lucas_primality 6188642267 (2 : ZMod 6188642267)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (2749, 1), (59243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (2749, 1), (59243, 1)] : List FactorBlock).map factorBlockValue).prod) = 6188642267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_19
      · exact prime_seventySixBV_2749
      · exact prime_seventySixBV_59243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 6188642267) ^ 3094321133 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 6188642267) ^ 325718014 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 6188642267) ^ 2251234 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 6188642267) ^ 104462 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_6383289373 : Nat.Prime 6383289373 := by
  apply lucas_primality 6383289373 (6 : ZMod 6383289373)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1283, 1), (414607, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1283, 1), (414607, 1)] : List FactorBlock).map factorBlockValue).prod) = 6383289373 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_1283
      · exact prime_seventySixBV_414607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 6383289373) ^ 3191644686 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (6 : ZMod 6383289373) ^ 2127763124 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (6 : ZMod 6383289373) ^ 4975284 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (6 : ZMod 6383289373) ^ 15396 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_7526405981 : Nat.Prime 7526405981 := by
  apply lucas_primality 7526405981 (3 : ZMod 7526405981)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (53, 1), (7100383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (53, 1), (7100383, 1)] : List FactorBlock).map factorBlockValue).prod) = 7526405981 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_5
      · exact prime_seventySixBV_53
      · exact prime_seventySixBV_7100383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 7526405981) ^ 3763202990 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 7526405981) ^ 1505281196 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 7526405981) ^ 142007660 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 7526405981) ^ 1060 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_9183839839 : Nat.Prime 9183839839 := by
  apply lucas_primality 9183839839 (3 : ZMod 9183839839)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (49375483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (49375483, 1)] : List FactorBlock).map factorBlockValue).prod) = 9183839839 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_31
      · exact prime_seventySixBV_49375483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 9183839839) ^ 4591919919 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 9183839839) ^ 3061279946 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 9183839839) ^ 296252898 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 9183839839) ^ 186 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_9763916497 : Nat.Prime 9763916497 := by
  apply lucas_primality 9763916497 (5 : ZMod 9763916497)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (227, 1), (896101, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (227, 1), (896101, 1)] : List FactorBlock).map factorBlockValue).prod) = 9763916497 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_227
      · exact prime_seventySixBV_896101
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 9763916497) ^ 4881958248 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 9763916497) ^ 3254638832 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 9763916497) ^ 43012848 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 9763916497) ^ 10896 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_12544355053 : Nat.Prime 12544355053 := by
  apply lucas_primality 12544355053 (2 : ZMod 12544355053)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (227, 1), (1535041, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (227, 1), (1535041, 1)] : List FactorBlock).map factorBlockValue).prod) = 12544355053 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_227
      · exact prime_seventySixBV_1535041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 12544355053) ^ 6272177526 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 12544355053) ^ 4181451684 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 12544355053) ^ 55261476 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 12544355053) ^ 8172 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_12659468429 : Nat.Prime 12659468429 := by
  apply lucas_primality 12659468429 (2 : ZMod 12659468429)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (83, 1), (2006891, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (83, 1), (2006891, 1)] : List FactorBlock).map factorBlockValue).prod) = 12659468429 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_19
      · exact prime_seventySixBV_83
      · exact prime_seventySixBV_2006891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 12659468429) ^ 6329734214 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 12659468429) ^ 666287812 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 12659468429) ^ 152523716 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 12659468429) ^ 6308 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_12949127923 : Nat.Prime 12949127923 := by
  apply lucas_primality 12949127923 (2 : ZMod 12949127923)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (67, 1), (73, 1), (441257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (67, 1), (73, 1), (441257, 1)] : List FactorBlock).map factorBlockValue).prod) = 12949127923 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_67
      · exact prime_seventySixBV_73
      · exact prime_seventySixBV_441257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 12949127923) ^ 6474563961 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 12949127923) ^ 4316375974 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 12949127923) ^ 193270566 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 12949127923) ^ 177385314 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 12949127923) ^ 29346 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_13829226667 : Nat.Prime 13829226667 := by
  apply lucas_primality 13829226667 (2 : ZMod 13829226667)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (74350681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (74350681, 1)] : List FactorBlock).map factorBlockValue).prod) = 13829226667 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_31
      · exact prime_seventySixBV_74350681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 13829226667) ^ 6914613333 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 13829226667) ^ 4609742222 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 13829226667) ^ 446104086 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 13829226667) ^ 186 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_14276715829 : Nat.Prime 14276715829 := by
  apply lucas_primality 14276715829 (2 : ZMod 14276715829)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13537, 1), (87887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13537, 1), (87887, 1)] : List FactorBlock).map factorBlockValue).prod) = 14276715829 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_13537
      · exact prime_seventySixBV_87887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 14276715829) ^ 7138357914 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 14276715829) ^ 4758905276 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 14276715829) ^ 1054644 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 14276715829) ^ 162444 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_14574890227 : Nat.Prime 14574890227 := by
  apply lucas_primality 14574890227 (3 : ZMod 14574890227)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 2), (14373659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 2), (14373659, 1)] : List FactorBlock).map factorBlockValue).prod) = 14574890227 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_13
      · exact prime_seventySixBV_14373659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 14574890227) ^ 7287445113 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 14574890227) ^ 4858296742 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 14574890227) ^ 1121145402 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 14574890227) ^ 1014 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_16368480551 : Nat.Prime 16368480551 := by
  apply lucas_primality 16368480551 (11 : ZMod 16368480551)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (327369611, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (327369611, 1)] : List FactorBlock).map factorBlockValue).prod) = 16368480551 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_5
      · exact prime_seventySixBV_327369611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 16368480551) ^ 8184240275 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (11 : ZMod 16368480551) ^ 3273696110 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (11 : ZMod 16368480551) ^ 50 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_16662765491 : Nat.Prime 16662765491 := by
  apply lucas_primality 16662765491 (6 : ZMod 16662765491)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (61, 1), (283, 1), (13789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (61, 1), (283, 1), (13789, 1)] : List FactorBlock).map factorBlockValue).prod) = 16662765491 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_5
      · exact prime_seventySixBV_7
      · exact prime_seventySixBV_61
      · exact prime_seventySixBV_283
      · exact prime_seventySixBV_13789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 16662765491) ^ 8331382745 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (6 : ZMod 16662765491) ^ 3332553098 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (6 : ZMod 16662765491) ^ 2380395070 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (6 : ZMod 16662765491) ^ 273160090 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (6 : ZMod 16662765491) ^ 58879030 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (6 : ZMod 16662765491) ^ 1208410 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_16744185553 : Nat.Prime 16744185553 := by
  apply lucas_primality 16744185553 (5 : ZMod 16744185553)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (43, 1), (8112493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (43, 1), (8112493, 1)] : List FactorBlock).map factorBlockValue).prod) = 16744185553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_43
      · exact prime_seventySixBV_8112493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 16744185553) ^ 8372092776 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 16744185553) ^ 5581395184 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 16744185553) ^ 389399664 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 16744185553) ^ 2064 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_17542396457 : Nat.Prime 17542396457 := by
  apply lucas_primality 17542396457 (3 : ZMod 17542396457)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (19, 2), (97, 1), (4817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (19, 2), (97, 1), (4817, 1)] : List FactorBlock).map factorBlockValue).prod) = 17542396457 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_13
      · exact prime_seventySixBV_19
      · exact prime_seventySixBV_97
      · exact prime_seventySixBV_4817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 17542396457) ^ 8771198228 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 17542396457) ^ 1349415112 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 17542396457) ^ 923284024 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 17542396457) ^ 180849448 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 17542396457) ^ 3641768 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_18331485479 : Nat.Prime 18331485479 := by
  apply lucas_primality 18331485479 (13 : ZMod 18331485479)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (157, 1), (419, 1), (139333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (157, 1), (419, 1), (139333, 1)] : List FactorBlock).map factorBlockValue).prod) = 18331485479 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_157
      · exact prime_seventySixBV_419
      · exact prime_seventySixBV_139333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 18331485479) ^ 9165742739 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (13 : ZMod 18331485479) ^ 116761054 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (13 : ZMod 18331485479) ^ 43750562 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (13 : ZMod 18331485479) ^ 131566 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_19255429561 : Nat.Prime 19255429561 := by
  apply lucas_primality 19255429561 (23 : ZMod 19255429561)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (211, 1), (317, 1), (2399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (211, 1), (317, 1), (2399, 1)] : List FactorBlock).map factorBlockValue).prod) = 19255429561 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_5
      · exact prime_seventySixBV_211
      · exact prime_seventySixBV_317
      · exact prime_seventySixBV_2399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 19255429561) ^ 9627714780 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (23 : ZMod 19255429561) ^ 6418476520 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (23 : ZMod 19255429561) ^ 3851085912 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (23 : ZMod 19255429561) ^ 91257960 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (23 : ZMod 19255429561) ^ 60742680 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (23 : ZMod 19255429561) ^ 8026440 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_22108754893 : Nat.Prime 22108754893 := by
  apply lucas_primality 22108754893 (6 : ZMod 22108754893)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (37, 1), (227, 1), (31337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (37, 1), (227, 1), (31337, 1)] : List FactorBlock).map factorBlockValue).prod) = 22108754893 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_7
      · exact prime_seventySixBV_37
      · exact prime_seventySixBV_227
      · exact prime_seventySixBV_31337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 22108754893) ^ 11054377446 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (6 : ZMod 22108754893) ^ 7369584964 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (6 : ZMod 22108754893) ^ 3158393556 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (6 : ZMod 22108754893) ^ 597533916 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (6 : ZMod 22108754893) ^ 97395396 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (6 : ZMod 22108754893) ^ 705516 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_23762806367 : Nat.Prime 23762806367 := by
  apply lucas_primality 23762806367 (5 : ZMod 23762806367)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (913954091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (913954091, 1)] : List FactorBlock).map factorBlockValue).prod) = 23762806367 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_13
      · exact prime_seventySixBV_913954091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 23762806367) ^ 11881403183 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 23762806367) ^ 1827908182 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 23762806367) ^ 26 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_24024257113 : Nat.Prime 24024257113 := by
  apply lucas_primality 24024257113 (7 : ZMod 24024257113)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (1283, 1), (780211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (1283, 1), (780211, 1)] : List FactorBlock).map factorBlockValue).prod) = 24024257113 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_1283
      · exact prime_seventySixBV_780211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 24024257113) ^ 12012128556 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (7 : ZMod 24024257113) ^ 8008085704 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (7 : ZMod 24024257113) ^ 18725064 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (7 : ZMod 24024257113) ^ 30792 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_25860525331 : Nat.Prime 25860525331 := by
  apply lucas_primality 25860525331 (3 : ZMod 25860525331)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (67, 1), (1973, 1), (6521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (67, 1), (1973, 1), (6521, 1)] : List FactorBlock).map factorBlockValue).prod) = 25860525331 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_5
      · exact prime_seventySixBV_67
      · exact prime_seventySixBV_1973
      · exact prime_seventySixBV_6521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 25860525331) ^ 12930262665 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 25860525331) ^ 8620175110 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 25860525331) ^ 5172105066 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 25860525331) ^ 385977990 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 25860525331) ^ 13107210 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 25860525331) ^ 3965730 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_27562133741 : Nat.Prime 27562133741 := by
  apply lucas_primality 27562133741 (2 : ZMod 27562133741)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (1378106687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (1378106687, 1)] : List FactorBlock).map factorBlockValue).prod) = 27562133741 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_5
      · exact prime_seventySixBV_1378106687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 27562133741) ^ 13781066870 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 27562133741) ^ 5512426748 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 27562133741) ^ 20 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_28548981751 : Nat.Prime 28548981751 := by
  apply lucas_primality 28548981751 (6 : ZMod 28548981751)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 3), (38065309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 3), (38065309, 1)] : List FactorBlock).map factorBlockValue).prod) = 28548981751 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_5
      · exact prime_seventySixBV_38065309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 28548981751) ^ 14274490875 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (6 : ZMod 28548981751) ^ 9516327250 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (6 : ZMod 28548981751) ^ 5709796350 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (6 : ZMod 28548981751) ^ 750 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_28640482477 : Nat.Prime 28640482477 := by
  apply lucas_primality 28640482477 (2 : ZMod 28640482477)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (29, 1), (43, 1), (1913959, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (29, 1), (43, 1), (1913959, 1)] : List FactorBlock).map factorBlockValue).prod) = 28640482477 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_29
      · exact prime_seventySixBV_43
      · exact prime_seventySixBV_1913959
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 28640482477) ^ 14320241238 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 28640482477) ^ 9546827492 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 28640482477) ^ 987602844 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 28640482477) ^ 666057732 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 28640482477) ^ 14964 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_28891248013 : Nat.Prime 28891248013 := by
  apply lucas_primality 28891248013 (2 : ZMod 28891248013)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (11, 1), (72957697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (11, 1), (72957697, 1)] : List FactorBlock).map factorBlockValue).prod) = 28891248013 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_11
      · exact prime_seventySixBV_72957697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 28891248013) ^ 14445624006 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 28891248013) ^ 9630416004 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 28891248013) ^ 2626477092 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 28891248013) ^ 396 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_31176654191 : Nat.Prime 31176654191 := by
  apply lucas_primality 31176654191 (11 : ZMod 31176654191)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (283424129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (283424129, 1)] : List FactorBlock).map factorBlockValue).prod) = 31176654191 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_5
      · exact prime_seventySixBV_11
      · exact prime_seventySixBV_283424129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 31176654191) ^ 15588327095 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (11 : ZMod 31176654191) ^ 6235330838 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (11 : ZMod 31176654191) ^ 2834241290 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (11 : ZMod 31176654191) ^ 110 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_32909211479 : Nat.Prime 32909211479 := by
  apply lucas_primality 32909211479 (7 : ZMod 32909211479)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (13, 2), (19, 1), (199, 1), (2341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (13, 2), (19, 1), (199, 1), (2341, 1)] : List FactorBlock).map factorBlockValue).prod) = 32909211479 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_11
      · exact prime_seventySixBV_13
      · exact prime_seventySixBV_19
      · exact prime_seventySixBV_199
      · exact prime_seventySixBV_2341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 32909211479) ^ 16454605739 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (7 : ZMod 32909211479) ^ 2991746498 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (7 : ZMod 32909211479) ^ 2531477806 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (7 : ZMod 32909211479) ^ 1732063762 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (7 : ZMod 32909211479) ^ 165372922 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (7 : ZMod 32909211479) ^ 14057758 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_38265553787 : Nat.Prime 38265553787 := by
  apply lucas_primality 38265553787 (2 : ZMod 38265553787)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (107, 1), (11863, 1), (15073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (107, 1), (11863, 1), (15073, 1)] : List FactorBlock).map factorBlockValue).prod) = 38265553787 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_107
      · exact prime_seventySixBV_11863
      · exact prime_seventySixBV_15073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 38265553787) ^ 19132776893 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 38265553787) ^ 357621998 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 38265553787) ^ 3225622 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 38265553787) ^ 2538682 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_43345329221 : Nat.Prime 43345329221 := by
  apply lucas_primality 43345329221 (2 : ZMod 43345329221)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (2167266461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (2167266461, 1)] : List FactorBlock).map factorBlockValue).prod) = 43345329221 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_5
      · exact prime_seventySixBV_2167266461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 43345329221) ^ 21672664610 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 43345329221) ^ 8669065844 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 43345329221) ^ 20 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_43749531307 : Nat.Prime 43749531307 := by
  apply lucas_primality 43749531307 (3 : ZMod 43749531307)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (186963809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (186963809, 1)] : List FactorBlock).map factorBlockValue).prod) = 43749531307 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_13
      · exact prime_seventySixBV_186963809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 43749531307) ^ 21874765653 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 43749531307) ^ 14583177102 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 43749531307) ^ 3365348562 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 43749531307) ^ 234 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_46578792233 : Nat.Prime 46578792233 := by
  apply lucas_primality 46578792233 (3 : ZMod 46578792233)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (831764147, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (831764147, 1)] : List FactorBlock).map factorBlockValue).prod) = 46578792233 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_7
      · exact prime_seventySixBV_831764147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 46578792233) ^ 23289396116 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 46578792233) ^ 6654113176 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 46578792233) ^ 56 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_46977195197 : Nat.Prime 46977195197 := by
  apply lucas_primality 46977195197 (2 : ZMod 46977195197)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (641, 1), (18321839, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (641, 1), (18321839, 1)] : List FactorBlock).map factorBlockValue).prod) = 46977195197 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_641
      · exact prime_seventySixBV_18321839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 46977195197) ^ 23488597598 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 46977195197) ^ 73287356 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 46977195197) ^ 2564 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_49128224543 : Nat.Prime 49128224543 := by
  apply lucas_primality 49128224543 (5 : ZMod 49128224543)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3967, 1), (6192113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3967, 1), (6192113, 1)] : List FactorBlock).map factorBlockValue).prod) = 49128224543 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3967
      · exact prime_seventySixBV_6192113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 49128224543) ^ 24564112271 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 49128224543) ^ 12384226 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 49128224543) ^ 7934 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_52009967419 : Nat.Prime 52009967419 := by
  apply lucas_primality 52009967419 (2 : ZMod 52009967419)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (43, 1), (4019, 1), (50159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (43, 1), (4019, 1), (50159, 1)] : List FactorBlock).map factorBlockValue).prod) = 52009967419 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_43
      · exact prime_seventySixBV_4019
      · exact prime_seventySixBV_50159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 52009967419) ^ 26004983709 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 52009967419) ^ 17336655806 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 52009967419) ^ 1209534126 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 52009967419) ^ 12941022 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 52009967419) ^ 1036902 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_64236206707 : Nat.Prime 64236206707 := by
  apply lucas_primality 64236206707 (3 : ZMod 64236206707)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (218490499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (218490499, 1)] : List FactorBlock).map factorBlockValue).prod) = 64236206707 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_7
      · exact prime_seventySixBV_218490499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 64236206707) ^ 32118103353 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 64236206707) ^ 21412068902 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 64236206707) ^ 9176600958 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 64236206707) ^ 294 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_71741035477 : Nat.Prime 71741035477 := by
  apply lucas_primality 71741035477 (5 : ZMod 71741035477)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (11, 1), (163, 1), (123493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (11, 1), (163, 1), (123493, 1)] : List FactorBlock).map factorBlockValue).prod) = 71741035477 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_11
      · exact prime_seventySixBV_163
      · exact prime_seventySixBV_123493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 71741035477) ^ 35870517738 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 71741035477) ^ 23913678492 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 71741035477) ^ 6521912316 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 71741035477) ^ 440129052 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 71741035477) ^ 580932 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_93800280491 : Nat.Prime 93800280491 := by
  apply lucas_primality 93800280491 (2 : ZMod 93800280491)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (1340004007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (1340004007, 1)] : List FactorBlock).map factorBlockValue).prod) = 93800280491 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_5
      · exact prime_seventySixBV_7
      · exact prime_seventySixBV_1340004007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 93800280491) ^ 46900140245 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 93800280491) ^ 18760056098 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 93800280491) ^ 13400040070 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 93800280491) ^ 70 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_133888841123 : Nat.Prime 133888841123 := by
  apply lucas_primality 133888841123 (2 : ZMod 133888841123)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (73, 1), (917046857, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (73, 1), (917046857, 1)] : List FactorBlock).map factorBlockValue).prod) = 133888841123 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_73
      · exact prime_seventySixBV_917046857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 133888841123) ^ 66944420561 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 133888841123) ^ 1834093714 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 133888841123) ^ 146 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_145937295593 : Nat.Prime 145937295593 := by
  apply lucas_primality 145937295593 (3 : ZMod 145937295593)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 2), (150761669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 2), (150761669, 1)] : List FactorBlock).map factorBlockValue).prod) = 145937295593 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_11
      · exact prime_seventySixBV_150761669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 145937295593) ^ 72968647796 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 145937295593) ^ 13267026872 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 145937295593) ^ 968 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_182633262523 : Nat.Prime 182633262523 := by
  apply lucas_primality 182633262523 (2 : ZMod 182633262523)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (73, 1), (827, 1), (504197, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (73, 1), (827, 1), (504197, 1)] : List FactorBlock).map factorBlockValue).prod) = 182633262523 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_73
      · exact prime_seventySixBV_827
      · exact prime_seventySixBV_504197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 182633262523) ^ 91316631261 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 182633262523) ^ 60877754174 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 182633262523) ^ 2501825514 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 182633262523) ^ 220838286 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 182633262523) ^ 362226 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_212246969593 : Nat.Prime 212246969593 := by
  apply lucas_primality 212246969593 (5 : ZMod 212246969593)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 2), (180482117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 2), (180482117, 1)] : List FactorBlock).map factorBlockValue).prod) = 212246969593 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_7
      · exact prime_seventySixBV_180482117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 212246969593) ^ 106123484796 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 212246969593) ^ 70748989864 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 212246969593) ^ 30320995656 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 212246969593) ^ 1176 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_229593322723 : Nat.Prime 229593322723 := by
  apply lucas_primality 229593322723 (2 : ZMod 229593322723)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (38265553787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (38265553787, 1)] : List FactorBlock).map factorBlockValue).prod) = 229593322723 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_38265553787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 229593322723) ^ 114796661361 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 229593322723) ^ 76531107574 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 229593322723) ^ 6 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_269586904201 : Nat.Prime 269586904201 := by
  apply lucas_primality 269586904201 (14 : ZMod 269586904201)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 2), (269, 1), (1670303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 2), (269, 1), (1670303, 1)] : List FactorBlock).map factorBlockValue).prod) = 269586904201 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_5
      · exact prime_seventySixBV_269
      · exact prime_seventySixBV_1670303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 269586904201) ^ 134793452100 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (14 : ZMod 269586904201) ^ 89862301400 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (14 : ZMod 269586904201) ^ 53917380840 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (14 : ZMod 269586904201) ^ 1002181800 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (14 : ZMod 269586904201) ^ 161400 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_328550693969 : Nat.Prime 328550693969 := by
  apply lucas_primality 328550693969 (3 : ZMod 328550693969)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (83, 1), (101, 1), (349933, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (83, 1), (101, 1), (349933, 1)] : List FactorBlock).map factorBlockValue).prod) = 328550693969 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_7
      · exact prime_seventySixBV_83
      · exact prime_seventySixBV_101
      · exact prime_seventySixBV_349933
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 328550693969) ^ 164275346984 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 328550693969) ^ 46935813424 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 328550693969) ^ 3958442096 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 328550693969) ^ 3252977168 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 328550693969) ^ 938896 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_387974416741 : Nat.Prime 387974416741 := by
  apply lucas_primality 387974416741 (6 : ZMod 387974416741)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (61, 1), (106003939, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (61, 1), (106003939, 1)] : List FactorBlock).map factorBlockValue).prod) = 387974416741 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_5
      · exact prime_seventySixBV_61
      · exact prime_seventySixBV_106003939
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 387974416741) ^ 193987208370 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (6 : ZMod 387974416741) ^ 129324805580 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (6 : ZMod 387974416741) ^ 77594883348 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (6 : ZMod 387974416741) ^ 6360236340 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (6 : ZMod 387974416741) ^ 3660 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_444848755067 : Nat.Prime 444848755067 := by
  apply lucas_primality 444848755067 (2 : ZMod 444848755067)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (443, 1), (502086631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (443, 1), (502086631, 1)] : List FactorBlock).map factorBlockValue).prod) = 444848755067 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_443
      · exact prime_seventySixBV_502086631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 444848755067) ^ 222424377533 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 444848755067) ^ 1004173262 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 444848755067) ^ 886 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_454018882529 : Nat.Prime 454018882529 := by
  apply lucas_primality 454018882529 (3 : ZMod 454018882529)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (47, 1), (9173, 1), (32909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (47, 1), (9173, 1), (32909, 1)] : List FactorBlock).map factorBlockValue).prod) = 454018882529 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_47
      · exact prime_seventySixBV_9173
      · exact prime_seventySixBV_32909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 454018882529) ^ 227009441264 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 454018882529) ^ 9659976224 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 454018882529) ^ 49495136 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 454018882529) ^ 13796192 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_458985145013 : Nat.Prime 458985145013 := by
  apply lucas_primality 458985145013 (2 : ZMod 458985145013)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (353, 1), (325060301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (353, 1), (325060301, 1)] : List FactorBlock).map factorBlockValue).prod) = 458985145013 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_353
      · exact prime_seventySixBV_325060301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 458985145013) ^ 229492572506 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 458985145013) ^ 1300241204 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 458985145013) ^ 1412 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_492862855841 : Nat.Prime 492862855841 := by
  apply lucas_primality 492862855841 (6 : ZMod 492862855841)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (43, 1), (1153, 1), (62131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (43, 1), (1153, 1), (62131, 1)] : List FactorBlock).map factorBlockValue).prod) = 492862855841 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_5
      · exact prime_seventySixBV_43
      · exact prime_seventySixBV_1153
      · exact prime_seventySixBV_62131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 492862855841) ^ 246431427920 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (6 : ZMod 492862855841) ^ 98572571168 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (6 : ZMod 492862855841) ^ 11461926880 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (6 : ZMod 492862855841) ^ 427461280 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (6 : ZMod 492862855841) ^ 7932640 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_578607040079 : Nat.Prime 578607040079 := by
  apply lucas_primality 578607040079 (23 : ZMod 578607040079)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (197, 1), (1468545787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (197, 1), (1468545787, 1)] : List FactorBlock).map factorBlockValue).prod) = 578607040079 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_197
      · exact prime_seventySixBV_1468545787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (23 : ZMod 578607040079) ^ 289303520039 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (23 : ZMod 578607040079) ^ 2937091574 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (23 : ZMod 578607040079) ^ 394 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_602633068757 : Nat.Prime 602633068757 := by
  apply lucas_primality 602633068757 (2 : ZMod 602633068757)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (227, 1), (28856209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (227, 1), (28856209, 1)] : List FactorBlock).map factorBlockValue).prod) = 602633068757 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_23
      · exact prime_seventySixBV_227
      · exact prime_seventySixBV_28856209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 602633068757) ^ 301316534378 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 602633068757) ^ 26201437772 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 602633068757) ^ 2654771228 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 602633068757) ^ 20884 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_631526272453 : Nat.Prime 631526272453 := by
  apply lucas_primality 631526272453 (6 : ZMod 631526272453)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (17542396457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (17542396457, 1)] : List FactorBlock).map factorBlockValue).prod) = 631526272453 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_17542396457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 631526272453) ^ 315763136226 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (6 : ZMod 631526272453) ^ 210508757484 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (6 : ZMod 631526272453) ^ 36 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_642362067071 : Nat.Prime 642362067071 := by
  apply lucas_primality 642362067071 (14 : ZMod 642362067071)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (64236206707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (64236206707, 1)] : List FactorBlock).map factorBlockValue).prod) = 642362067071 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_5
      · exact prime_seventySixBV_64236206707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (14 : ZMod 642362067071) ^ 321181033535 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (14 : ZMod 642362067071) ^ 128472413414 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (14 : ZMod 642362067071) ^ 10 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_705923268559 : Nat.Prime 705923268559 := by
  apply lucas_primality 705923268559 (6 : ZMod 705923268559)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (59, 1), (109, 1), (18294803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (59, 1), (109, 1), (18294803, 1)] : List FactorBlock).map factorBlockValue).prod) = 705923268559 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_59
      · exact prime_seventySixBV_109
      · exact prime_seventySixBV_18294803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 705923268559) ^ 352961634279 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (6 : ZMod 705923268559) ^ 235307756186 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (6 : ZMod 705923268559) ^ 11964801162 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (6 : ZMod 705923268559) ^ 6476360262 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (6 : ZMod 705923268559) ^ 38586 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_735104895611 : Nat.Prime 735104895611 := by
  apply lucas_primality 735104895611 (2 : ZMod 735104895611)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (50119, 1), (1466719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (50119, 1), (1466719, 1)] : List FactorBlock).map factorBlockValue).prod) = 735104895611 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_5
      · exact prime_seventySixBV_50119
      · exact prime_seventySixBV_1466719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 735104895611) ^ 367552447805 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 735104895611) ^ 147020979122 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 735104895611) ^ 14667190 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 735104895611) ^ 501190 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_754221535219 : Nat.Prime 754221535219 := by
  apply lucas_primality 754221535219 (3 : ZMod 754221535219)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 7), (1069, 1), (161303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 7), (1069, 1), (161303, 1)] : List FactorBlock).map factorBlockValue).prod) = 754221535219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_1069
      · exact prime_seventySixBV_161303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 754221535219) ^ 377110767609 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 754221535219) ^ 251407178406 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 754221535219) ^ 705539322 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 754221535219) ^ 4675806 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_757983273923 : Nat.Prime 757983273923 := by
  apply lucas_primality 757983273923 (2 : ZMod 757983273923)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (131, 1), (413295133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (131, 1), (413295133, 1)] : List FactorBlock).map factorBlockValue).prod) = 757983273923 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_7
      · exact prime_seventySixBV_131
      · exact prime_seventySixBV_413295133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 757983273923) ^ 378991636961 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 757983273923) ^ 108283324846 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 757983273923) ^ 5786131862 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 757983273923) ^ 1834 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_830194792153 : Nat.Prime 830194792153 := by
  apply lucas_primality 830194792153 (15 : ZMod 830194792153)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (3144677243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (3144677243, 1)] : List FactorBlock).map factorBlockValue).prod) = 830194792153 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_11
      · exact prime_seventySixBV_3144677243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (15 : ZMod 830194792153) ^ 415097396076 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (15 : ZMod 830194792153) ^ 276731597384 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (15 : ZMod 830194792153) ^ 75472253832 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (15 : ZMod 830194792153) ^ 264 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_844247430011 : Nat.Prime 844247430011 := by
  apply lucas_primality 844247430011 (6 : ZMod 844247430011)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (1973, 1), (2517061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (1973, 1), (2517061, 1)] : List FactorBlock).map factorBlockValue).prod) = 844247430011 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_5
      · exact prime_seventySixBV_17
      · exact prime_seventySixBV_1973
      · exact prime_seventySixBV_2517061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 844247430011) ^ 422123715005 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (6 : ZMod 844247430011) ^ 168849486002 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (6 : ZMod 844247430011) ^ 49661613530 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (6 : ZMod 844247430011) ^ 427900370 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (6 : ZMod 844247430011) ^ 335410 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_924260618929 : Nat.Prime 924260618929 := by
  apply lucas_primality 924260618929 (17 : ZMod 924260618929)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (19255429561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (19255429561, 1)] : List FactorBlock).map factorBlockValue).prod) = 924260618929 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_19255429561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (17 : ZMod 924260618929) ^ 462130309464 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (17 : ZMod 924260618929) ^ 308086872976 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (17 : ZMod 924260618929) ^ 48 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_1009793153939 : Nat.Prime 1009793153939 := by
  apply lucas_primality 1009793153939 (6 : ZMod 1009793153939)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (79, 1), (336373469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (79, 1), (336373469, 1)] : List FactorBlock).map factorBlockValue).prod) = 1009793153939 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_19
      · exact prime_seventySixBV_79
      · exact prime_seventySixBV_336373469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 1009793153939) ^ 504896576969 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (6 : ZMod 1009793153939) ^ 53147008102 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (6 : ZMod 1009793153939) ^ 12782191822 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (6 : ZMod 1009793153939) ^ 3002 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_1097347174741 : Nat.Prime 1097347174741 := by
  apply lucas_primality 1097347174741 (6 : ZMod 1097347174741)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (19, 1), (229, 1), (1087, 1), (1289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (19, 1), (229, 1), (1087, 1), (1289, 1)] : List FactorBlock).map factorBlockValue).prod) = 1097347174741 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_5
      · exact prime_seventySixBV_19
      · exact prime_seventySixBV_229
      · exact prime_seventySixBV_1087
      · exact prime_seventySixBV_1289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1097347174741) ^ 548673587370 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (6 : ZMod 1097347174741) ^ 365782391580 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (6 : ZMod 1097347174741) ^ 219469434948 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (6 : ZMod 1097347174741) ^ 57755114460 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (6 : ZMod 1097347174741) ^ 4791909060 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (6 : ZMod 1097347174741) ^ 1009519020 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (6 : ZMod 1097347174741) ^ 851316660 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_1284724134143 : Nat.Prime 1284724134143 := by
  apply lucas_primality 1284724134143 (5 : ZMod 1284724134143)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (642362067071, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (642362067071, 1)] : List FactorBlock).map factorBlockValue).prod) = 1284724134143 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_642362067071
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 1284724134143) ^ 642362067071 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 1284724134143) ^ 2 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_1639499123083 : Nat.Prime 1639499123083 := by
  apply lucas_primality 1639499123083 (2 : ZMod 1639499123083)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1249, 1), (5641, 1), (38783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1249, 1), (5641, 1), (38783, 1)] : List FactorBlock).map factorBlockValue).prod) = 1639499123083 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_1249
      · exact prime_seventySixBV_5641
      · exact prime_seventySixBV_38783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1639499123083) ^ 819749561541 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1639499123083) ^ 546499707694 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1639499123083) ^ 1312649418 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1639499123083) ^ 290639802 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1639499123083) ^ 42273654 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_1882097942167 : Nat.Prime 1882097942167 := by
  apply lucas_primality 1882097942167 (3 : ZMod 1882097942167)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 2), (347, 1), (1783009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 2), (347, 1), (1783009, 1)] : List FactorBlock).map factorBlockValue).prod) = 1882097942167 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_13
      · exact prime_seventySixBV_347
      · exact prime_seventySixBV_1783009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1882097942167) ^ 941048971083 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1882097942167) ^ 627365980722 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1882097942167) ^ 144776764782 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1882097942167) ^ 5423913378 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1882097942167) ^ 1055574 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_2056706826301 : Nat.Prime 2056706826301 := by
  apply lucas_primality 2056706826301 (2 : ZMod 2056706826301)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 5), (5, 2), (7, 2), (19, 1), (90911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 5), (5, 2), (7, 2), (19, 1), (90911, 1)] : List FactorBlock).map factorBlockValue).prod) = 2056706826301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_5
      · exact prime_seventySixBV_7
      · exact prime_seventySixBV_19
      · exact prime_seventySixBV_90911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2056706826301) ^ 1028353413150 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2056706826301) ^ 685568942100 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2056706826301) ^ 411341365260 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2056706826301) ^ 293815260900 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2056706826301) ^ 108247727700 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2056706826301) ^ 22623300 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_2152231064311 : Nat.Prime 2152231064311 := by
  apply lucas_primality 2152231064311 (3 : ZMod 2152231064311)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (71741035477, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (71741035477, 1)] : List FactorBlock).map factorBlockValue).prod) = 2152231064311 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_5
      · exact prime_seventySixBV_71741035477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2152231064311) ^ 1076115532155 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 2152231064311) ^ 717410354770 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 2152231064311) ^ 430446212862 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 2152231064311) ^ 30 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_2186993782033 : Nat.Prime 2186993782033 := by
  apply lucas_primality 2186993782033 (5 : ZMod 2186993782033)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (8059, 1), (5653601, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (8059, 1), (5653601, 1)] : List FactorBlock).map factorBlockValue).prod) = 2186993782033 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_8059
      · exact prime_seventySixBV_5653601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2186993782033) ^ 1093496891016 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 2186993782033) ^ 728997927344 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 2186993782033) ^ 271372848 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 2186993782033) ^ 386832 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_2287533000047 : Nat.Prime 2287533000047 := by
  apply lucas_primality 2287533000047 (5 : ZMod 2287533000047)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (41, 1), (2221, 1), (1794349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (41, 1), (2221, 1), (1794349, 1)] : List FactorBlock).map factorBlockValue).prod) = 2287533000047 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_7
      · exact prime_seventySixBV_41
      · exact prime_seventySixBV_2221
      · exact prime_seventySixBV_1794349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2287533000047) ^ 1143766500023 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 2287533000047) ^ 326790428578 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 2287533000047) ^ 55793487806 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 2287533000047) ^ 1029956326 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 2287533000047) ^ 1274854 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_3114418512859 : Nat.Prime 3114418512859 := by
  apply lucas_primality 3114418512859 (2 : ZMod 3114418512859)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (16744185553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (16744185553, 1)] : List FactorBlock).map factorBlockValue).prod) = 3114418512859 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_31
      · exact prime_seventySixBV_16744185553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3114418512859) ^ 1557209256429 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 3114418512859) ^ 1038139504286 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 3114418512859) ^ 100465113318 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 3114418512859) ^ 186 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_3328718959529 : Nat.Prime 3328718959529 := by
  apply lucas_primality 3328718959529 (3 : ZMod 3328718959529)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (19, 1), (79, 1), (14699, 1), (18859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (19, 1), (79, 1), (14699, 1), (18859, 1)] : List FactorBlock).map factorBlockValue).prod) = 3328718959529 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_19
      · exact prime_seventySixBV_79
      · exact prime_seventySixBV_14699
      · exact prime_seventySixBV_18859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3328718959529) ^ 1664359479764 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 3328718959529) ^ 175195734712 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 3328718959529) ^ 42135683032 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 3328718959529) ^ 226458872 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 3328718959529) ^ 176505592 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_3471530887537 : Nat.Prime 3471530887537 := by
  apply lucas_primality 3471530887537 (5 : ZMod 3471530887537)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (49409, 1), (1463773, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (49409, 1), (1463773, 1)] : List FactorBlock).map factorBlockValue).prod) = 3471530887537 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_49409
      · exact prime_seventySixBV_1463773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 3471530887537) ^ 1735765443768 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 3471530887537) ^ 1157176962512 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 3471530887537) ^ 70261104 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 3471530887537) ^ 2371632 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_6684187399289 : Nat.Prime 6684187399289 := by
  apply lucas_primality 6684187399289 (3 : ZMod 6684187399289)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (244939, 1), (487307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (244939, 1), (487307, 1)] : List FactorBlock).map factorBlockValue).prod) = 6684187399289 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_7
      · exact prime_seventySixBV_244939
      · exact prime_seventySixBV_487307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6684187399289) ^ 3342093699644 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 6684187399289) ^ 954883914184 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 6684187399289) ^ 27289192 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 6684187399289) ^ 13716584 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_7153315496917 : Nat.Prime 7153315496917 := by
  apply lucas_primality 7153315496917 (2 : ZMod 7153315496917)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (37, 1), (1721, 1), (9361459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (37, 1), (1721, 1), (9361459, 1)] : List FactorBlock).map factorBlockValue).prod) = 7153315496917 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_37
      · exact prime_seventySixBV_1721
      · exact prime_seventySixBV_9361459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7153315496917) ^ 3576657748458 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 7153315496917) ^ 2384438498972 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 7153315496917) ^ 193332851268 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 7153315496917) ^ 4156487796 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 7153315496917) ^ 764124 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_8733909400009 : Nat.Prime 8733909400009 := by
  apply lucas_primality 8733909400009 (7 : ZMod 8733909400009)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 1), (41, 1), (59, 1), (11572261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 1), (41, 1), (59, 1), (11572261, 1)] : List FactorBlock).map factorBlockValue).prod) = 8733909400009 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_13
      · exact prime_seventySixBV_41
      · exact prime_seventySixBV_59
      · exact prime_seventySixBV_11572261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 8733909400009) ^ 4366954700004 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (7 : ZMod 8733909400009) ^ 2911303133336 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (7 : ZMod 8733909400009) ^ 671839184616 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (7 : ZMod 8733909400009) ^ 213022180488 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (7 : ZMod 8733909400009) ^ 148032362712 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (7 : ZMod 8733909400009) ^ 754728 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_8856858855973 : Nat.Prime 8856858855973 := by
  apply lucas_primality 8856858855973 (5 : ZMod 8856858855973)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (29, 1), (110323, 1), (230693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (29, 1), (110323, 1), (230693, 1)] : List FactorBlock).map factorBlockValue).prod) = 8856858855973 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_29
      · exact prime_seventySixBV_110323
      · exact prime_seventySixBV_230693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 8856858855973) ^ 4428429427986 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 8856858855973) ^ 2952286285324 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 8856858855973) ^ 305408926068 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 8856858855973) ^ 80281164 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 8856858855973) ^ 38392404 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_8896213589311 : Nat.Prime 8896213589311 := by
  apply lucas_primality 8896213589311 (6 : ZMod 8896213589311)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (101467, 1), (974177, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (101467, 1), (974177, 1)] : List FactorBlock).map factorBlockValue).prod) = 8896213589311 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_5
      · exact prime_seventySixBV_101467
      · exact prime_seventySixBV_974177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 8896213589311) ^ 4448106794655 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (6 : ZMod 8896213589311) ^ 2965404529770 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (6 : ZMod 8896213589311) ^ 1779242717862 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (6 : ZMod 8896213589311) ^ 87675930 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (6 : ZMod 8896213589311) ^ 9132030 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_9051508570747 : Nat.Prime 9051508570747 := by
  apply lucas_primality 9051508570747 (2 : ZMod 9051508570747)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (23, 1), (643, 1), (1187, 1), (4523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (23, 1), (643, 1), (1187, 1), (4523, 1)] : List FactorBlock).map factorBlockValue).prod) = 9051508570747 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_19
      · exact prime_seventySixBV_23
      · exact prime_seventySixBV_643
      · exact prime_seventySixBV_1187
      · exact prime_seventySixBV_4523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9051508570747) ^ 4525754285373 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 9051508570747) ^ 3017169523582 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 9051508570747) ^ 476395187934 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 9051508570747) ^ 393543850902 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 9051508570747) ^ 14076996222 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 9051508570747) ^ 7625533758 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 9051508570747) ^ 2001217902 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_12021527966527 : Nat.Prime 12021527966527 := by
  apply lucas_primality 12021527966527 (19 : ZMod 12021527966527)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (13, 1), (199, 1), (4397, 1), (19571, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (13, 1), (199, 1), (4397, 1), (19571, 1)] : List FactorBlock).map factorBlockValue).prod) = 12021527966527 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_13
      · exact prime_seventySixBV_199
      · exact prime_seventySixBV_4397
      · exact prime_seventySixBV_19571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 12021527966527) ^ 6010763983263 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (19 : ZMod 12021527966527) ^ 4007175988842 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (19 : ZMod 12021527966527) ^ 924732920502 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (19 : ZMod 12021527966527) ^ 60409688274 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (19 : ZMod 12021527966527) ^ 2734029558 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (19 : ZMod 12021527966527) ^ 614252106 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_18136530577531 : Nat.Prime 18136530577531 := by
  apply lucas_primality 18136530577531 (2 : ZMod 18136530577531)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (41, 1), (263, 1), (18688399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (41, 1), (263, 1), (18688399, 1)] : List FactorBlock).map factorBlockValue).prod) = 18136530577531 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_5
      · exact prime_seventySixBV_41
      · exact prime_seventySixBV_263
      · exact prime_seventySixBV_18688399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 18136530577531) ^ 9068265288765 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 18136530577531) ^ 6045510192510 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 18136530577531) ^ 3627306115506 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 18136530577531) ^ 442354404330 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 18136530577531) ^ 68960192310 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 18136530577531) ^ 970470 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_18993829431361 : Nat.Prime 18993829431361 := by
  apply lucas_primality 18993829431361 (13 : ZMod 18993829431361)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (5, 1), (7, 1), (43, 1), (65731691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (5, 1), (7, 1), (43, 1), (65731691, 1)] : List FactorBlock).map factorBlockValue).prod) = 18993829431361 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_5
      · exact prime_seventySixBV_7
      · exact prime_seventySixBV_43
      · exact prime_seventySixBV_65731691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 18993829431361) ^ 9496914715680 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (13 : ZMod 18993829431361) ^ 6331276477120 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (13 : ZMod 18993829431361) ^ 3798765886272 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (13 : ZMod 18993829431361) ^ 2713404204480 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (13 : ZMod 18993829431361) ^ 441716963520 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (13 : ZMod 18993829431361) ^ 288960 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_19444913839171 : Nat.Prime 19444913839171 := by
  apply lucas_primality 19444913839171 (3 : ZMod 19444913839171)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (30941, 1), (6982793, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (30941, 1), (6982793, 1)] : List FactorBlock).map factorBlockValue).prod) = 19444913839171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_5
      · exact prime_seventySixBV_30941
      · exact prime_seventySixBV_6982793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 19444913839171) ^ 9722456919585 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 19444913839171) ^ 6481637946390 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 19444913839171) ^ 3888982767834 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 19444913839171) ^ 628451370 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 19444913839171) ^ 2784690 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_23171945260397 : Nat.Prime 23171945260397 := by
  apply lucas_primality 23171945260397 (2 : ZMod 23171945260397)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (157, 1), (683, 1), (6581, 1), (8209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (157, 1), (683, 1), (6581, 1), (8209, 1)] : List FactorBlock).map factorBlockValue).prod) = 23171945260397 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_157
      · exact prime_seventySixBV_683
      · exact prime_seventySixBV_6581
      · exact prime_seventySixBV_8209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 23171945260397) ^ 11585972630198 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 23171945260397) ^ 147592008028 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 23171945260397) ^ 33926713412 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 23171945260397) ^ 3521037116 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 23171945260397) ^ 2822748844 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_24312751353707 : Nat.Prime 24312751353707 := by
  apply lucas_primality 24312751353707 (2 : ZMod 24312751353707)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (328550693969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (328550693969, 1)] : List FactorBlock).map factorBlockValue).prod) = 24312751353707 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_37
      · exact prime_seventySixBV_328550693969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 24312751353707) ^ 12156375676853 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 24312751353707) ^ 657101387938 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 24312751353707) ^ 74 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_41175594000847 : Nat.Prime 41175594000847 := by
  apply lucas_primality 41175594000847 (3 : ZMod 41175594000847)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (2287533000047, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (2287533000047, 1)] : List FactorBlock).map factorBlockValue).prod) = 41175594000847 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_2287533000047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 41175594000847) ^ 20587797000423 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 41175594000847) ^ 13725198000282 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 41175594000847) ^ 18 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_50116432302851 : Nat.Prime 50116432302851 := by
  apply lucas_primality 50116432302851 (2 : ZMod 50116432302851)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (149, 1), (48487, 1), (138739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (149, 1), (48487, 1), (138739, 1)] : List FactorBlock).map factorBlockValue).prod) = 50116432302851 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_5
      · exact prime_seventySixBV_149
      · exact prime_seventySixBV_48487
      · exact prime_seventySixBV_138739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 50116432302851) ^ 25058216151425 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 50116432302851) ^ 10023286460570 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 50116432302851) ^ 336351894650 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 50116432302851) ^ 1033605550 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 50116432302851) ^ 361228150 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_51477321037603 : Nat.Prime 51477321037603 := by
  apply lucas_primality 51477321037603 (5 : ZMod 51477321037603)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (131, 1), (122327, 1), (535391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (131, 1), (122327, 1), (535391, 1)] : List FactorBlock).map factorBlockValue).prod) = 51477321037603 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_131
      · exact prime_seventySixBV_122327
      · exact prime_seventySixBV_535391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 51477321037603) ^ 25738660518801 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 51477321037603) ^ 17159107012534 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 51477321037603) ^ 392956649142 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 51477321037603) ^ 420817326 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 51477321037603) ^ 96149022 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_58190242878377 : Nat.Prime 58190242878377 := by
  apply lucas_primality 58190242878377 (3 : ZMod 58190242878377)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (47, 1), (22108754893, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (47, 1), (22108754893, 1)] : List FactorBlock).map factorBlockValue).prod) = 58190242878377 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_7
      · exact prime_seventySixBV_47
      · exact prime_seventySixBV_22108754893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 58190242878377) ^ 29095121439188 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 58190242878377) ^ 8312891839768 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 58190242878377) ^ 1238090274008 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 58190242878377) ^ 2632 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_65357683463239 : Nat.Prime 65357683463239 := by
  apply lucas_primality 65357683463239 (3 : ZMod 65357683463239)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (132949, 1), (81933277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (132949, 1), (81933277, 1)] : List FactorBlock).map factorBlockValue).prod) = 65357683463239 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_132949
      · exact prime_seventySixBV_81933277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 65357683463239) ^ 32678841731619 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 65357683463239) ^ 21785894487746 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 65357683463239) ^ 491599662 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 65357683463239) ^ 797694 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_66487344834077 : Nat.Prime 66487344834077 := by
  apply lucas_primality 66487344834077 (2 : ZMod 66487344834077)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 1), (31531, 1), (18177881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 1), (31531, 1), (18177881, 1)] : List FactorBlock).map factorBlockValue).prod) = 66487344834077 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_29
      · exact prime_seventySixBV_31531
      · exact prime_seventySixBV_18177881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 66487344834077) ^ 33243672417038 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 66487344834077) ^ 2292667063244 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 66487344834077) ^ 2108634196 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 66487344834077) ^ 3657596 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_69430103056571 : Nat.Prime 69430103056571 := by
  apply lucas_primality 69430103056571 (2 : ZMod 69430103056571)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 2), (24024257113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 2), (24024257113, 1)] : List FactorBlock).map factorBlockValue).prod) = 69430103056571 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_5
      · exact prime_seventySixBV_17
      · exact prime_seventySixBV_24024257113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 69430103056571) ^ 34715051528285 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 69430103056571) ^ 13886020611314 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 69430103056571) ^ 4084123709210 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 69430103056571) ^ 2890 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_76376129290429 : Nat.Prime 76376129290429 := by
  apply lucas_primality 76376129290429 (2 : ZMod 76376129290429)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (578607040079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (578607040079, 1)] : List FactorBlock).map factorBlockValue).prod) = 76376129290429 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_11
      · exact prime_seventySixBV_578607040079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 76376129290429) ^ 38188064645214 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 76376129290429) ^ 25458709763476 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 76376129290429) ^ 6943284480948 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 76376129290429) ^ 132 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_79579368663719 : Nat.Prime 79579368663719 := by
  apply lucas_primality 79579368663719 (7 : ZMod 79579368663719)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 2), (46977195197, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 2), (46977195197, 1)] : List FactorBlock).map factorBlockValue).prod) = 79579368663719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_7
      · exact prime_seventySixBV_11
      · exact prime_seventySixBV_46977195197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 79579368663719) ^ 39789684331859 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (7 : ZMod 79579368663719) ^ 11368481237674 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (7 : ZMod 79579368663719) ^ 7234488060338 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (7 : ZMod 79579368663719) ^ 1694 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_87971400763817 : Nat.Prime 87971400763817 := by
  apply lucas_primality 87971400763817 (3 : ZMod 87971400763817)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (239, 1), (69191, 1), (664973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (239, 1), (69191, 1), (664973, 1)] : List FactorBlock).map factorBlockValue).prod) = 87971400763817 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_239
      · exact prime_seventySixBV_69191
      · exact prime_seventySixBV_664973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 87971400763817) ^ 43985700381908 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 87971400763817) ^ 368081174744 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 87971400763817) ^ 1271428376 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 87971400763817) ^ 132293192 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_101003803053449 : Nat.Prime 101003803053449 := by
  apply lucas_primality 101003803053449 (3 : ZMod 101003803053449)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (19, 1), (23, 1), (28891248013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (19, 1), (23, 1), (28891248013, 1)] : List FactorBlock).map factorBlockValue).prod) = 101003803053449 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_19
      · exact prime_seventySixBV_23
      · exact prime_seventySixBV_28891248013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 101003803053449) ^ 50501901526724 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 101003803053449) ^ 5315989634392 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 101003803053449) ^ 4391469697976 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 101003803053449) ^ 3496 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_112793611200199 : Nat.Prime 112793611200199 := by
  apply lucas_primality 112793611200199 (12 : ZMod 112793611200199)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (19, 1), (30931, 1), (1881641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (19, 1), (30931, 1), (1881641, 1)] : List FactorBlock).map factorBlockValue).prod) = 112793611200199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_17
      · exact prime_seventySixBV_19
      · exact prime_seventySixBV_30931
      · exact prime_seventySixBV_1881641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (12 : ZMod 112793611200199) ^ 56396805600099 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (12 : ZMod 112793611200199) ^ 37597870400066 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (12 : ZMod 112793611200199) ^ 6634918305894 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (12 : ZMod 112793611200199) ^ 5936505852642 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (12 : ZMod 112793611200199) ^ 3646620258 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (12 : ZMod 112793611200199) ^ 59944278 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_114718636952347 : Nat.Prime 114718636952347 := by
  apply lucas_primality 114718636952347 (5 : ZMod 114718636952347)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (19501, 1), (140064413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (19501, 1), (140064413, 1)] : List FactorBlock).map factorBlockValue).prod) = 114718636952347 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_7
      · exact prime_seventySixBV_19501
      · exact prime_seventySixBV_140064413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 114718636952347) ^ 57359318476173 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 114718636952347) ^ 38239545650782 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 114718636952347) ^ 16388376707478 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 114718636952347) ^ 5882705346 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 114718636952347) ^ 819042 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_124450950496897 : Nat.Prime 124450950496897 := by
  apply lucas_primality 124450950496897 (7 : ZMod 124450950496897)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 4), (67, 1), (179154791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 4), (67, 1), (179154791, 1)] : List FactorBlock).map factorBlockValue).prod) = 124450950496897 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_67
      · exact prime_seventySixBV_179154791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 124450950496897) ^ 62225475248448 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (7 : ZMod 124450950496897) ^ 41483650165632 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (7 : ZMod 124450950496897) ^ 1857476873088 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (7 : ZMod 124450950496897) ^ 694656 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_151081075485731 : Nat.Prime 151081075485731 := by
  apply lucas_primality 151081075485731 (2 : ZMod 151081075485731)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (71, 1), (16368480551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (71, 1), (16368480551, 1)] : List FactorBlock).map factorBlockValue).prod) = 151081075485731 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_5
      · exact prime_seventySixBV_13
      · exact prime_seventySixBV_71
      · exact prime_seventySixBV_16368480551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 151081075485731) ^ 75540537742865 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 151081075485731) ^ 30216215097146 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 151081075485731) ^ 11621621191210 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 151081075485731) ^ 2127902471630 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 151081075485731) ^ 9230 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_166189573085381 : Nat.Prime 166189573085381 := by
  apply lucas_primality 166189573085381 (2 : ZMod 166189573085381)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (13, 1), (7499, 1), (85236787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (13, 1), (7499, 1), (85236787, 1)] : List FactorBlock).map factorBlockValue).prod) = 166189573085381 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_5
      · exact prime_seventySixBV_13
      · exact prime_seventySixBV_7499
      · exact prime_seventySixBV_85236787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 166189573085381) ^ 83094786542690 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 166189573085381) ^ 33237914617076 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 166189573085381) ^ 12783813314260 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 166189573085381) ^ 22161564620 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 166189573085381) ^ 1949740 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_170331589700039 : Nat.Prime 170331589700039 := by
  apply lucas_primality 170331589700039 (11 : ZMod 170331589700039)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (23, 1), (43, 2), (53, 2), (173, 1), (317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (23, 1), (43, 2), (53, 2), (173, 1), (317, 1)] : List FactorBlock).map factorBlockValue).prod) = 170331589700039 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_13
      · exact prime_seventySixBV_23
      · exact prime_seventySixBV_43
      · exact prime_seventySixBV_53
      · exact prime_seventySixBV_173
      · exact prime_seventySixBV_317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 170331589700039) ^ 85165794850019 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (11 : ZMod 170331589700039) ^ 13102429976926 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (11 : ZMod 170331589700039) ^ 7405721291306 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (11 : ZMod 170331589700039) ^ 3961199760466 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (11 : ZMod 170331589700039) ^ 3213803579246 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (11 : ZMod 170331589700039) ^ 984575663006 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (11 : ZMod 170331589700039) ^ 537323626814 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_185375562083177 : Nat.Prime 185375562083177 := by
  apply lucas_primality 185375562083177 (3 : ZMod 185375562083177)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (23171945260397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (23171945260397, 1)] : List FactorBlock).map factorBlockValue).prod) = 185375562083177 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_23171945260397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 185375562083177) ^ 92687781041588 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 185375562083177) ^ 8 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_202007606106899 : Nat.Prime 202007606106899 := by
  apply lucas_primality 202007606106899 (2 : ZMod 202007606106899)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (101003803053449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (101003803053449, 1)] : List FactorBlock).map factorBlockValue).prod) = 202007606106899 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_101003803053449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 202007606106899) ^ 101003803053449 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 202007606106899) ^ 2 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_272787705403783 : Nat.Prime 272787705403783 := by
  apply lucas_primality 272787705403783 (3 : ZMod 272787705403783)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (97, 1), (257, 1), (58831103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (97, 1), (257, 1), (58831103, 1)] : List FactorBlock).map factorBlockValue).prod) = 272787705403783 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_31
      · exact prime_seventySixBV_97
      · exact prime_seventySixBV_257
      · exact prime_seventySixBV_58831103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 272787705403783) ^ 136393852701891 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 272787705403783) ^ 90929235134594 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 272787705403783) ^ 8799603400122 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 272787705403783) ^ 2812244385606 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 272787705403783) ^ 1061430760326 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 272787705403783) ^ 4636794 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_958259400674761 : Nat.Prime 958259400674761 := by
  apply lucas_primality 958259400674761 (7 : ZMod 958259400674761)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (5, 1), (139, 1), (6383289373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (5, 1), (139, 1), (6383289373, 1)] : List FactorBlock).map factorBlockValue).prod) = 958259400674761 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_5
      · exact prime_seventySixBV_139
      · exact prime_seventySixBV_6383289373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 958259400674761) ^ 479129700337380 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (7 : ZMod 958259400674761) ^ 319419800224920 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (7 : ZMod 958259400674761) ^ 191651880134952 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (7 : ZMod 958259400674761) ^ 6893952522840 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (7 : ZMod 958259400674761) ^ 150120 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_1040898346204441 : Nat.Prime 1040898346204441 := by
  apply lucas_primality 1040898346204441 (17 : ZMod 1040898346204441)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (281, 1), (82787, 1), (372871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (281, 1), (82787, 1), (372871, 1)] : List FactorBlock).map factorBlockValue).prod) = 1040898346204441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_5
      · exact prime_seventySixBV_281
      · exact prime_seventySixBV_82787
      · exact prime_seventySixBV_372871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 1040898346204441) ^ 520449173102220 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (17 : ZMod 1040898346204441) ^ 346966115401480 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (17 : ZMod 1040898346204441) ^ 208179669240888 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (17 : ZMod 1040898346204441) ^ 3704264577240 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (17 : ZMod 1040898346204441) ^ 12573210120 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (17 : ZMod 1040898346204441) ^ 2791577640 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_1072207513634963 : Nat.Prime 1072207513634963 := by
  apply lucas_primality 1072207513634963 (2 : ZMod 1072207513634963)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1362997, 1), (393327173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1362997, 1), (393327173, 1)] : List FactorBlock).map factorBlockValue).prod) = 1072207513634963 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_1362997
      · exact prime_seventySixBV_393327173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1072207513634963) ^ 536103756817481 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1072207513634963) ^ 786654346 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1072207513634963) ^ 2725994 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_1269234822564187 : Nat.Prime 1269234822564187 := by
  apply lucas_primality 1269234822564187 (2 : ZMod 1269234822564187)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (811, 1), (6673, 1), (1699499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (811, 1), (6673, 1), (1699499, 1)] : List FactorBlock).map factorBlockValue).prod) = 1269234822564187 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_23
      · exact prime_seventySixBV_811
      · exact prime_seventySixBV_6673
      · exact prime_seventySixBV_1699499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1269234822564187) ^ 634617411282093 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1269234822564187) ^ 423078274188062 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1269234822564187) ^ 55184122720182 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1269234822564187) ^ 1565024442126 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1269234822564187) ^ 190204529082 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1269234822564187) ^ 746828814 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_1627109285643901 : Nat.Prime 1627109285643901 := by
  apply lucas_primality 1627109285643901 (6 : ZMod 1627109285643901)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 2), (602633068757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 2), (602633068757, 1)] : List FactorBlock).map factorBlockValue).prod) = 1627109285643901 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_5
      · exact prime_seventySixBV_602633068757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 1627109285643901) ^ 813554642821950 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (6 : ZMod 1627109285643901) ^ 542369761881300 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (6 : ZMod 1627109285643901) ^ 325421857128780 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (6 : ZMod 1627109285643901) ^ 2700 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_1851740460540517 : Nat.Prime 1851740460540517 := by
  apply lucas_primality 1851740460540517 (14 : ZMod 1851740460540517)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 3), (13, 1), (37, 1), (1049, 1), (891629, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 3), (13, 1), (37, 1), (1049, 1), (891629, 1)] : List FactorBlock).map factorBlockValue).prod) = 1851740460540517 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_7
      · exact prime_seventySixBV_13
      · exact prime_seventySixBV_37
      · exact prime_seventySixBV_1049
      · exact prime_seventySixBV_891629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 1851740460540517) ^ 925870230270258 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (14 : ZMod 1851740460540517) ^ 617246820180172 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (14 : ZMod 1851740460540517) ^ 264534351505788 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (14 : ZMod 1851740460540517) ^ 142441573887732 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (14 : ZMod 1851740460540517) ^ 50047039474068 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (14 : ZMod 1851740460540517) ^ 1765243527684 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (14 : ZMod 1851740460540517) ^ 2076806004 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_2030579841139217 : Nat.Prime 2030579841139217 := by
  apply lucas_primality 2030579841139217 (3 : ZMod 2030579841139217)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (67, 1), (151, 1), (12544355053, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (67, 1), (151, 1), (12544355053, 1)] : List FactorBlock).map factorBlockValue).prod) = 2030579841139217 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_67
      · exact prime_seventySixBV_151
      · exact prime_seventySixBV_12544355053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2030579841139217) ^ 1015289920569608 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 2030579841139217) ^ 30307161808048 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 2030579841139217) ^ 13447548616816 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 2030579841139217) ^ 161872 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_6767616672011941 : Nat.Prime 6767616672011941 := by
  apply lucas_primality 6767616672011941 (6 : ZMod 6767616672011941)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (112793611200199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (112793611200199, 1)] : List FactorBlock).map factorBlockValue).prod) = 6767616672011941 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_5
      · exact prime_seventySixBV_112793611200199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 6767616672011941) ^ 3383808336005970 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (6 : ZMod 6767616672011941) ^ 2255872224003980 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (6 : ZMod 6767616672011941) ^ 1353523334402388 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (6 : ZMod 6767616672011941) ^ 60 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_8671410156426349 : Nat.Prime 8671410156426349 := by
  apply lucas_primality 8671410156426349 (2 : ZMod 8671410156426349)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (653, 1), (2083, 1), (531258671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (653, 1), (2083, 1), (531258671, 1)] : List FactorBlock).map factorBlockValue).prod) = 8671410156426349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_653
      · exact prime_seventySixBV_2083
      · exact prime_seventySixBV_531258671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8671410156426349) ^ 4335705078213174 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 8671410156426349) ^ 2890470052142116 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 8671410156426349) ^ 13279341740316 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 8671410156426349) ^ 4162942945956 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 8671410156426349) ^ 16322388 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_11101014717284419 : Nat.Prime 11101014717284419 := by
  apply lucas_primality 11101014717284419 (2 : ZMod 11101014717284419)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 1), (139, 1), (458985145013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 1), (139, 1), (458985145013, 1)] : List FactorBlock).map factorBlockValue).prod) = 11101014717284419 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_29
      · exact prime_seventySixBV_139
      · exact prime_seventySixBV_458985145013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 11101014717284419) ^ 5550507358642209 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 11101014717284419) ^ 3700338239094806 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 11101014717284419) ^ 382793610940842 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 11101014717284419) ^ 79863415232262 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 11101014717284419) ^ 24186 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_14658816590487323 : Nat.Prime 14658816590487323 := by
  apply lucas_primality 14658816590487323 (2 : ZMod 14658816590487323)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 2), (89, 1), (16993, 1), (40051933, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 2), (89, 1), (16993, 1), (40051933, 1)] : List FactorBlock).map factorBlockValue).prod) = 14658816590487323 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_11
      · exact prime_seventySixBV_89
      · exact prime_seventySixBV_16993
      · exact prime_seventySixBV_40051933
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 14658816590487323) ^ 7329408295243661 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 14658816590487323) ^ 1332619690044302 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 14658816590487323) ^ 164705804387498 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 14658816590487323) ^ 862638532954 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 14658816590487323) ^ 365995234 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_17688752404466743 : Nat.Prime 17688752404466743 := by
  apply lucas_primality 17688752404466743 (3 : ZMod 17688752404466743)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (23, 1), (12967, 1), (3295014659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (23, 1), (12967, 1), (3295014659, 1)] : List FactorBlock).map factorBlockValue).prod) = 17688752404466743 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_23
      · exact prime_seventySixBV_12967
      · exact prime_seventySixBV_3295014659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 17688752404466743) ^ 8844376202233371 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 17688752404466743) ^ 5896250801488914 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 17688752404466743) ^ 769076191498554 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 17688752404466743) ^ 1364136068826 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 17688752404466743) ^ 5368338 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_19842113296580021 : Nat.Prime 19842113296580021 := by
  apply lucas_primality 19842113296580021 (3 : ZMod 19842113296580021)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (19, 1), (31, 1), (59, 1), (28548981751, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (19, 1), (31, 1), (59, 1), (28548981751, 1)] : List FactorBlock).map factorBlockValue).prod) = 19842113296580021 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_5
      · exact prime_seventySixBV_19
      · exact prime_seventySixBV_31
      · exact prime_seventySixBV_59
      · exact prime_seventySixBV_28548981751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 19842113296580021) ^ 9921056648290010 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 19842113296580021) ^ 3968422659316004 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 19842113296580021) ^ 1044321752451580 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 19842113296580021) ^ 640068170857420 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 19842113296580021) ^ 336307005026780 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 19842113296580021) ^ 695020 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_28025339390502689 : Nat.Prime 28025339390502689 := by
  apply lucas_primality 28025339390502689 (3 : ZMod 28025339390502689)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (13, 1), (31, 1), (17599, 1), (123483197, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (13, 1), (31, 1), (17599, 1), (123483197, 1)] : List FactorBlock).map factorBlockValue).prod) = 28025339390502689 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_13
      · exact prime_seventySixBV_31
      · exact prime_seventySixBV_17599
      · exact prime_seventySixBV_123483197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 28025339390502689) ^ 14012669695251344 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 28025339390502689) ^ 2155795337730976 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 28025339390502689) ^ 904043206145248 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 28025339390502689) ^ 1592439308512 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 28025339390502689) ^ 226956704 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_28666599277230773 : Nat.Prime 28666599277230773 := by
  apply lucas_primality 28666599277230773 (2 : ZMod 28666599277230773)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (13, 1), (50116432302851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (13, 1), (50116432302851, 1)] : List FactorBlock).map factorBlockValue).prod) = 28666599277230773 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_11
      · exact prime_seventySixBV_13
      · exact prime_seventySixBV_50116432302851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 28666599277230773) ^ 14333299638615386 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 28666599277230773) ^ 2606054479748252 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 28666599277230773) ^ 2205123021325444 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 28666599277230773) ^ 572 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_35476283372930051 : Nat.Prime 35476283372930051 := by
  apply lucas_primality 35476283372930051 (10 : ZMod 35476283372930051)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (7, 1), (17, 1), (37, 1), (67, 1), (101, 1), (223, 1), (106787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (7, 1), (17, 1), (37, 1), (67, 1), (101, 1), (223, 1), (106787, 1)] : List FactorBlock).map factorBlockValue).prod) = 35476283372930051 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_5
      · exact prime_seventySixBV_7
      · exact prime_seventySixBV_17
      · exact prime_seventySixBV_37
      · exact prime_seventySixBV_67
      · exact prime_seventySixBV_101
      · exact prime_seventySixBV_223
      · exact prime_seventySixBV_106787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 35476283372930051) ^ 17738141686465025 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (10 : ZMod 35476283372930051) ^ 7095256674586010 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (10 : ZMod 35476283372930051) ^ 5068040481847150 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (10 : ZMod 35476283372930051) ^ 2086840198407650 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (10 : ZMod 35476283372930051) ^ 958818469538650 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (10 : ZMod 35476283372930051) ^ 529496766760150 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (10 : ZMod 35476283372930051) ^ 351250330425050 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (10 : ZMod 35476283372930051) ^ 159086472524350 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (10 : ZMod 35476283372930051) ^ 332215376150 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_38951825938118791 : Nat.Prime 38951825938118791 := by
  apply lucas_primality 38951825938118791 (3 : ZMod 38951825938118791)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (17, 1), (76376129290429, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (17, 1), (76376129290429, 1)] : List FactorBlock).map factorBlockValue).prod) = 38951825938118791 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_5
      · exact prime_seventySixBV_17
      · exact prime_seventySixBV_76376129290429
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 38951825938118791) ^ 19475912969059395 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 38951825938118791) ^ 12983941979372930 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 38951825938118791) ^ 7790365187623758 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 38951825938118791) ^ 2291283878712870 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 38951825938118791) ^ 510 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_51344711878912163 : Nat.Prime 51344711878912163 := by
  apply lucas_primality 51344711878912163 (2 : ZMod 51344711878912163)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (311, 1), (2687, 1), (31517, 1), (974749, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (311, 1), (2687, 1), (31517, 1), (974749, 1)] : List FactorBlock).map factorBlockValue).prod) = 51344711878912163 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_311
      · exact prime_seventySixBV_2687
      · exact prime_seventySixBV_31517
      · exact prime_seventySixBV_974749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 51344711878912163) ^ 25672355939456081 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 51344711878912163) ^ 165095536588142 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 51344711878912163) ^ 19108564152926 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 51344711878912163) ^ 1629111650186 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 51344711878912163) ^ 52674803338 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_56880908907659027 : Nat.Prime 56880908907659027 := by
  apply lucas_primality 56880908907659027 (2 : ZMod 56880908907659027)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (103, 1), (5309, 1), (52009967419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (103, 1), (5309, 1), (52009967419, 1)] : List FactorBlock).map factorBlockValue).prod) = 56880908907659027 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_103
      · exact prime_seventySixBV_5309
      · exact prime_seventySixBV_52009967419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 56880908907659027) ^ 28440454453829513 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 56880908907659027) ^ 552241834054942 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 56880908907659027) ^ 10714053288314 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 56880908907659027) ^ 1093654 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_63440347007070193 : Nat.Prime 63440347007070193 := by
  apply lucas_primality 63440347007070193 (5 : ZMod 63440347007070193)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (79319, 1), (16662765491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (79319, 1), (16662765491, 1)] : List FactorBlock).map factorBlockValue).prod) = 63440347007070193 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_79319
      · exact prime_seventySixBV_16662765491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 63440347007070193) ^ 31720173503535096 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 63440347007070193) ^ 21146782335690064 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 63440347007070193) ^ 799812743568 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 63440347007070193) ^ 3807312 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_89104759254679141 : Nat.Prime 89104759254679141 := by
  apply lucas_primality 89104759254679141 (6 : ZMod 89104759254679141)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 1), (7, 1), (340789, 1), (69170917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 1), (7, 1), (340789, 1), (69170917, 1)] : List FactorBlock).map factorBlockValue).prod) = 89104759254679141 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_5
      · exact prime_seventySixBV_7
      · exact prime_seventySixBV_340789
      · exact prime_seventySixBV_69170917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 89104759254679141) ^ 44552379627339570 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (6 : ZMod 89104759254679141) ^ 29701586418226380 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (6 : ZMod 89104759254679141) ^ 17820951850935828 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (6 : ZMod 89104759254679141) ^ 12729251322097020 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (6 : ZMod 89104759254679141) ^ 261466066260 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (6 : ZMod 89104759254679141) ^ 1288182420 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_103174166011912103 : Nat.Prime 103174166011912103 := by
  apply lucas_primality 103174166011912103 (10 : ZMod 103174166011912103)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (673, 1), (34061, 1), (132379151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (673, 1), (34061, 1), (132379151, 1)] : List FactorBlock).map factorBlockValue).prod) = 103174166011912103 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_17
      · exact prime_seventySixBV_673
      · exact prime_seventySixBV_34061
      · exact prime_seventySixBV_132379151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 103174166011912103) ^ 51587083005956051 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (10 : ZMod 103174166011912103) ^ 6069068588936006 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (10 : ZMod 103174166011912103) ^ 153304852915174 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (10 : ZMod 103174166011912103) ^ 3029099733182 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (10 : ZMod 103174166011912103) ^ 779383802 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_149822539859765183 : Nat.Prime 149822539859765183 := by
  apply lucas_primality 149822539859765183 (5 : ZMod 149822539859765183)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (653, 1), (114718636952347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (653, 1), (114718636952347, 1)] : List FactorBlock).map factorBlockValue).prod) = 149822539859765183 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_653
      · exact prime_seventySixBV_114718636952347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 149822539859765183) ^ 74911269929882591 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 149822539859765183) ^ 229437273904694 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 149822539859765183) ^ 1306 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_220343997527388817 : Nat.Prime 220343997527388817 := by
  apply lucas_primality 220343997527388817 (7 : ZMod 220343997527388817)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (2099, 1), (2186993782033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (2099, 1), (2186993782033, 1)] : List FactorBlock).map factorBlockValue).prod) = 220343997527388817 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_2099
      · exact prime_seventySixBV_2186993782033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 220343997527388817) ^ 110171998763694408 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (7 : ZMod 220343997527388817) ^ 73447999175796272 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (7 : ZMod 220343997527388817) ^ 104975701537584 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (7 : ZMod 220343997527388817) ^ 100752 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_255784440221916521 : Nat.Prime 255784440221916521 := by
  apply lucas_primality 255784440221916521 (3 : ZMod 255784440221916521)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (1151, 1), (607493, 1), (9145291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (1151, 1), (607493, 1), (9145291, 1)] : List FactorBlock).map factorBlockValue).prod) = 255784440221916521 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_5
      · exact prime_seventySixBV_1151
      · exact prime_seventySixBV_607493
      · exact prime_seventySixBV_9145291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 255784440221916521) ^ 127892220110958260 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 255784440221916521) ^ 51156888044383304 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 255784440221916521) ^ 222228010618520 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 255784440221916521) ^ 421049197640 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 255784440221916521) ^ 27968977720 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_393123702240337477 : Nat.Prime 393123702240337477 := by
  apply lucas_primality 393123702240337477 (6 : ZMod 393123702240337477)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (703331, 1), (46578792233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (703331, 1), (46578792233, 1)] : List FactorBlock).map factorBlockValue).prod) = 393123702240337477 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_703331
      · exact prime_seventySixBV_46578792233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 393123702240337477) ^ 196561851120168738 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (6 : ZMod 393123702240337477) ^ 131041234080112492 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (6 : ZMod 393123702240337477) ^ 558945506796 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (6 : ZMod 393123702240337477) ^ 8439972 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_471330901677366851 : Nat.Prime 471330901677366851 := by
  apply lucas_primality 471330901677366851 (7 : ZMod 471330901677366851)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (7, 3), (23, 1), (29, 1), (229, 1), (179928713, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (7, 3), (23, 1), (29, 1), (229, 1), (179928713, 1)] : List FactorBlock).map factorBlockValue).prod) = 471330901677366851 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_5
      · exact prime_seventySixBV_7
      · exact prime_seventySixBV_23
      · exact prime_seventySixBV_29
      · exact prime_seventySixBV_229
      · exact prime_seventySixBV_179928713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 471330901677366851) ^ 235665450838683425 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (7 : ZMod 471330901677366851) ^ 94266180335473370 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (7 : ZMod 471330901677366851) ^ 67332985953909550 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (7 : ZMod 471330901677366851) ^ 20492647899015950 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (7 : ZMod 471330901677366851) ^ 16252789713012650 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (7 : ZMod 471330901677366851) ^ 2058213544442650 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (7 : ZMod 471330901677366851) ^ 2619542450 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_480770846798109653 : Nat.Prime 480770846798109653 := by
  apply lucas_primality 480770846798109653 (2 : ZMod 480770846798109653)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (190321, 1), (631526272453, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (190321, 1), (631526272453, 1)] : List FactorBlock).map factorBlockValue).prod) = 480770846798109653 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_190321
      · exact prime_seventySixBV_631526272453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 480770846798109653) ^ 240385423399054826 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 480770846798109653) ^ 2526105089812 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 480770846798109653) ^ 761284 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_715503229263626009 : Nat.Prime 715503229263626009 := by
  apply lucas_primality 715503229263626009 (3 : ZMod 715503229263626009)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (12503, 1), (7153315496917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (12503, 1), (7153315496917, 1)] : List FactorBlock).map factorBlockValue).prod) = 715503229263626009 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_12503
      · exact prime_seventySixBV_7153315496917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 715503229263626009) ^ 357751614631813004 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 715503229263626009) ^ 57226523975336 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 715503229263626009) ^ 100024 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_891047592546791411 : Nat.Prime 891047592546791411 := by
  apply lucas_primality 891047592546791411 (2 : ZMod 891047592546791411)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (89104759254679141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (89104759254679141, 1)] : List FactorBlock).map factorBlockValue).prod) = 891047592546791411 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_5
      · exact prime_seventySixBV_89104759254679141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 891047592546791411) ^ 445523796273395705 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 891047592546791411) ^ 178209518509358282 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 891047592546791411) ^ 10 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_1652207762676191029 : Nat.Prime 1652207762676191029 := by
  apply lucas_primality 1652207762676191029 (22 : ZMod 1652207762676191029)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (11, 1), (17, 1), (149, 1), (705923268559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (11, 1), (17, 1), (149, 1), (705923268559, 1)] : List FactorBlock).map factorBlockValue).prod) = 1652207762676191029 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_7
      · exact prime_seventySixBV_11
      · exact prime_seventySixBV_17
      · exact prime_seventySixBV_149
      · exact prime_seventySixBV_705923268559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (22 : ZMod 1652207762676191029) ^ 826103881338095514 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (22 : ZMod 1652207762676191029) ^ 550735920892063676 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (22 : ZMod 1652207762676191029) ^ 236029680382313004 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (22 : ZMod 1652207762676191029) ^ 150200705697835548 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (22 : ZMod 1652207762676191029) ^ 97188691922128884 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (22 : ZMod 1652207762676191029) ^ 11088642702524772 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (22 : ZMod 1652207762676191029) ^ 2340492 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_2395502047704952129 : Nat.Prime 2395502047704952129 := by
  apply lucas_primality 2395502047704952129 (7 : ZMod 2395502047704952129)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (79, 1), (4799, 1), (32909211479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (79, 1), (4799, 1), (32909211479, 1)] : List FactorBlock).map factorBlockValue).prod) = 2395502047704952129 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_79
      · exact prime_seventySixBV_4799
      · exact prime_seventySixBV_32909211479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 2395502047704952129) ^ 1197751023852476064 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (7 : ZMod 2395502047704952129) ^ 798500682568317376 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (7 : ZMod 2395502047704952129) ^ 30322810730442432 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (7 : ZMod 2395502047704952129) ^ 499166919713472 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (7 : ZMod 2395502047704952129) ^ 72791232 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_2960338771297028117 : Nat.Prime 2960338771297028117 := by
  apply lucas_primality 2960338771297028117 (2 : ZMod 2960338771297028117)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (38951825938118791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (38951825938118791, 1)] : List FactorBlock).map factorBlockValue).prod) = 2960338771297028117 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_19
      · exact prime_seventySixBV_38951825938118791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2960338771297028117) ^ 1480169385648514058 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2960338771297028117) ^ 155807303752475164 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 2960338771297028117) ^ 76 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_3630549714527432453 : Nat.Prime 3630549714527432453 := by
  apply lucas_primality 3630549714527432453 (2 : ZMod 3630549714527432453)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (29, 1), (10223, 1), (106961, 1), (4088957, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (29, 1), (10223, 1), (106961, 1), (4088957, 1)] : List FactorBlock).map factorBlockValue).prod) = 3630549714527432453 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_7
      · exact prime_seventySixBV_29
      · exact prime_seventySixBV_10223
      · exact prime_seventySixBV_106961
      · exact prime_seventySixBV_4088957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3630549714527432453) ^ 1815274857263716226 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 3630549714527432453) ^ 518649959218204636 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 3630549714527432453) ^ 125191369466463188 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 3630549714527432453) ^ 355135450897724 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 3630549714527432453) ^ 33942742817732 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 3630549714527432453) ^ 887891390036 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_6117777995774625091 : Nat.Prime 6117777995774625091 := by
  apply lucas_primality 6117777995774625091 (2 : ZMod 6117777995774625091)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (313, 1), (37501, 1), (5791139377, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (313, 1), (37501, 1), (5791139377, 1)] : List FactorBlock).map factorBlockValue).prod) = 6117777995774625091 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_5
      · exact prime_seventySixBV_313
      · exact prime_seventySixBV_37501
      · exact prime_seventySixBV_5791139377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6117777995774625091) ^ 3058888997887312545 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 6117777995774625091) ^ 2039259331924875030 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 6117777995774625091) ^ 1223555599154925018 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 6117777995774625091) ^ 19545616599918930 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 6117777995774625091) ^ 163136396250090 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 6117777995774625091) ^ 1056403170 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_11419262461272634741 : Nat.Prime 11419262461272634741 := by
  apply lucas_primality 11419262461272634741 (6 : ZMod 11419262461272634741)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (63440347007070193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (63440347007070193, 1)] : List FactorBlock).map factorBlockValue).prod) = 11419262461272634741 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_5
      · exact prime_seventySixBV_63440347007070193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 11419262461272634741) ^ 5709631230636317370 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (6 : ZMod 11419262461272634741) ^ 3806420820424211580 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (6 : ZMod 11419262461272634741) ^ 2283852492254526948 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (6 : ZMod 11419262461272634741) ^ 180 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_16158977772025661341 : Nat.Prime 16158977772025661341 := by
  apply lucas_primality 16158977772025661341 (6 : ZMod 16158977772025661341)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (71, 1), (20483, 1), (70241, 1), (2636453, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (71, 1), (20483, 1), (70241, 1), (2636453, 1)] : List FactorBlock).map factorBlockValue).prod) = 16158977772025661341 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_5
      · exact prime_seventySixBV_71
      · exact prime_seventySixBV_20483
      · exact prime_seventySixBV_70241
      · exact prime_seventySixBV_2636453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 16158977772025661341) ^ 8079488886012830670 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (6 : ZMod 16158977772025661341) ^ 5386325924008553780 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (6 : ZMod 16158977772025661341) ^ 3231795554405132268 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (6 : ZMod 16158977772025661341) ^ 227591236225713540 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (6 : ZMod 16158977772025661341) ^ 788897025436980 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (6 : ZMod 16158977772025661341) ^ 230050508563740 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (6 : ZMod 16158977772025661341) ^ 6129059676780 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_19255631005425982081 : Nat.Prime 19255631005425982081 := by
  apply lucas_primality 19255631005425982081 (17 : ZMod 19255631005425982081)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (5, 1), (41, 1), (3653603, 1), (66950113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (5, 1), (41, 1), (3653603, 1), (66950113, 1)] : List FactorBlock).map factorBlockValue).prod) = 19255631005425982081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_5
      · exact prime_seventySixBV_41
      · exact prime_seventySixBV_3653603
      · exact prime_seventySixBV_66950113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 19255631005425982081) ^ 9627815502712991040 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (17 : ZMod 19255631005425982081) ^ 6418543668475327360 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (17 : ZMod 19255631005425982081) ^ 3851126201085196416 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (17 : ZMod 19255631005425982081) ^ 469649536717706880 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (17 : ZMod 19255631005425982081) ^ 5270312895360 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (17 : ZMod 19255631005425982081) ^ 287611628160 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_20900423646780275317 : Nat.Prime 20900423646780275317 := by
  apply lucas_primality 20900423646780275317 (2 : ZMod 20900423646780275317)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (2389, 1), (2515673, 1), (289803419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (2389, 1), (2515673, 1), (289803419, 1)] : List FactorBlock).map factorBlockValue).prod) = 20900423646780275317 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_2389
      · exact prime_seventySixBV_2515673
      · exact prime_seventySixBV_289803419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 20900423646780275317) ^ 10450211823390137658 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 20900423646780275317) ^ 6966807882260091772 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 20900423646780275317) ^ 8748607637831844 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 20900423646780275317) ^ 8308084415892 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 20900423646780275317) ^ 72119313564 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_30092480235414413083 : Nat.Prime 30092480235414413083 := by
  apply lucas_primality 30092480235414413083 (2 : ZMod 30092480235414413083)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (163, 1), (1451, 1), (1009793153939, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (163, 1), (1451, 1), (1009793153939, 1)] : List FactorBlock).map factorBlockValue).prod) = 30092480235414413083 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_7
      · exact prime_seventySixBV_163
      · exact prime_seventySixBV_1451
      · exact prime_seventySixBV_1009793153939
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 30092480235414413083) ^ 15046240117707206541 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 30092480235414413083) ^ 10030826745138137694 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 30092480235414413083) ^ 4298925747916344726 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 30092480235414413083) ^ 184616443162051614 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 30092480235414413083) ^ 20739131795599182 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 30092480235414413083) ^ 29800638 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_38091824492098955741 : Nat.Prime 38091824492098955741 := by
  apply lucas_primality 38091824492098955741 (3 : ZMod 38091824492098955741)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (149, 2), (383, 1), (883, 1), (7577, 1), (33479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (149, 2), (383, 1), (883, 1), (7577, 1), (33479, 1)] : List FactorBlock).map factorBlockValue).prod) = 38091824492098955741 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_5
      · exact prime_seventySixBV_149
      · exact prime_seventySixBV_383
      · exact prime_seventySixBV_883
      · exact prime_seventySixBV_7577
      · exact prime_seventySixBV_33479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 38091824492098955741) ^ 19045912246049477870 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 38091824492098955741) ^ 7618364898419791148 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 38091824492098955741) ^ 255649828806033260 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 38091824492098955741) ^ 99456460814879780 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 38091824492098955741) ^ 43139099085049780 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 38091824492098955741) ^ 5027296356354620 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 38091824492098955741) ^ 1137782624693060 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_61375493265200888911 : Nat.Prime 61375493265200888911 := by
  apply lucas_primality 61375493265200888911 (7 : ZMod 61375493265200888911)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (73, 1), (28025339390502689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (73, 1), (28025339390502689, 1)] : List FactorBlock).map factorBlockValue).prod) = 61375493265200888911 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_5
      · exact prime_seventySixBV_73
      · exact prime_seventySixBV_28025339390502689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 61375493265200888911) ^ 30687746632600444455 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (7 : ZMod 61375493265200888911) ^ 20458497755066962970 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (7 : ZMod 61375493265200888911) ^ 12275098653040177782 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (7 : ZMod 61375493265200888911) ^ 840760181715080670 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (7 : ZMod 61375493265200888911) ^ 2190 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_62244698619035204941 : Nat.Prime 62244698619035204941 := by
  apply lucas_primality 62244698619035204941 (6 : ZMod 62244698619035204941)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (3803, 1), (272787705403783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (3803, 1), (272787705403783, 1)] : List FactorBlock).map factorBlockValue).prod) = 62244698619035204941 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_5
      · exact prime_seventySixBV_3803
      · exact prime_seventySixBV_272787705403783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 62244698619035204941) ^ 31122349309517602470 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (6 : ZMod 62244698619035204941) ^ 20748232873011734980 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (6 : ZMod 62244698619035204941) ^ 12448939723807040988 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (6 : ZMod 62244698619035204941) ^ 16367262324226980 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (6 : ZMod 62244698619035204941) ^ 228180 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_83476225741034673047 : Nat.Prime 83476225741034673047 := by
  apply lucas_primality 83476225741034673047 (5 : ZMod 83476225741034673047)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (227, 1), (96078893, 1), (1913722493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (227, 1), (96078893, 1), (1913722493, 1)] : List FactorBlock).map factorBlockValue).prod) = 83476225741034673047 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_227
      · exact prime_seventySixBV_96078893
      · exact prime_seventySixBV_1913722493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 83476225741034673047) ^ 41738112870517336523 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 83476225741034673047) ^ 367736677273280498 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 83476225741034673047) ^ 868830011822 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 83476225741034673047) ^ 43619817422 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_104866593961181589401 : Nat.Prime 104866593961181589401 := by
  apply lucas_primality 104866593961181589401 (3 : ZMod 104866593961181589401)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (73, 1), (479, 1), (2423, 1), (6188642267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (73, 1), (479, 1), (2423, 1), (6188642267, 1)] : List FactorBlock).map factorBlockValue).prod) = 104866593961181589401 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_5
      · exact prime_seventySixBV_73
      · exact prime_seventySixBV_479
      · exact prime_seventySixBV_2423
      · exact prime_seventySixBV_6188642267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 104866593961181589401) ^ 52433296980590794700 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 104866593961181589401) ^ 20973318792236317880 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 104866593961181589401) ^ 1436528684399747800 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 104866593961181589401) ^ 218928171108938600 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 104866593961181589401) ^ 43279650830037800 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 104866593961181589401) ^ 16945008200 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_110505973383968378767 : Nat.Prime 110505973383968378767 := by
  apply lucas_primality 110505973383968378767 (3 : ZMod 110505973383968378767)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (7888607, 1), (212246969593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (7888607, 1), (212246969593, 1)] : List FactorBlock).map factorBlockValue).prod) = 110505973383968378767 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_11
      · exact prime_seventySixBV_7888607
      · exact prime_seventySixBV_212246969593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 110505973383968378767) ^ 55252986691984189383 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 110505973383968378767) ^ 36835324461322792922 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 110505973383968378767) ^ 10045997580360761706 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 110505973383968378767) ^ 14008299993138 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 110505973383968378767) ^ 520648062 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_120369920941657652333 : Nat.Prime 120369920941657652333 := by
  apply lucas_primality 120369920941657652333 (2 : ZMod 120369920941657652333)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (30092480235414413083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (30092480235414413083, 1)] : List FactorBlock).map factorBlockValue).prod) = 120369920941657652333 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_30092480235414413083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 120369920941657652333) ^ 60184960470828826166 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 120369920941657652333) ^ 4 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_130859570164796682959 : Nat.Prime 130859570164796682959 := by
  apply lucas_primality 130859570164796682959 (7 : ZMod 130859570164796682959)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (439, 1), (19403, 1), (1097347174741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (439, 1), (19403, 1), (1097347174741, 1)] : List FactorBlock).map factorBlockValue).prod) = 130859570164796682959 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_7
      · exact prime_seventySixBV_439
      · exact prime_seventySixBV_19403
      · exact prime_seventySixBV_1097347174741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 130859570164796682959) ^ 65429785082398341479 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (7 : ZMod 130859570164796682959) ^ 18694224309256668994 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (7 : ZMod 130859570164796682959) ^ 298085581240994722 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (7 : ZMod 130859570164796682959) ^ 6744295735958186 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (7 : ZMod 130859570164796682959) ^ 119250838 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_137427676935044325763 : Nat.Prime 137427676935044325763 := by
  apply lucas_primality 137427676935044325763 (2 : ZMod 137427676935044325763)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (47, 1), (28666599277230773, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (47, 1), (28666599277230773, 1)] : List FactorBlock).map factorBlockValue).prod) = 137427676935044325763 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_17
      · exact prime_seventySixBV_47
      · exact prime_seventySixBV_28666599277230773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 137427676935044325763) ^ 68713838467522162881 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 137427676935044325763) ^ 45809225645014775254 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 137427676935044325763) ^ 8083980996179077986 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 137427676935044325763) ^ 2923993126277538846 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 137427676935044325763) ^ 4794 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_557061052016354145053 : Nat.Prime 557061052016354145053 := by
  apply lucas_primality 557061052016354145053 (2 : ZMod 557061052016354145053)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (163909, 1), (65357683463239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (163909, 1), (65357683463239, 1)] : List FactorBlock).map factorBlockValue).prod) = 557061052016354145053 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_13
      · exact prime_seventySixBV_163909
      · exact prime_seventySixBV_65357683463239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 557061052016354145053) ^ 278530526008177072526 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 557061052016354145053) ^ 42850850155104165004 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 557061052016354145053) ^ 3398599540088428 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 557061052016354145053) ^ 8523268 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_797671260300235466669 : Nat.Prime 797671260300235466669 := by
  apply lucas_primality 797671260300235466669 (2 : ZMod 797671260300235466669)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (317, 1), (10631, 1), (3114418512859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (317, 1), (10631, 1), (3114418512859, 1)] : List FactorBlock).map factorBlockValue).prod) = 797671260300235466669 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_19
      · exact prime_seventySixBV_317
      · exact prime_seventySixBV_10631
      · exact prime_seventySixBV_3114418512859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 797671260300235466669) ^ 398835630150117733334 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 797671260300235466669) ^ 41982697910538708772 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 797671260300235466669) ^ 2516313123975506204 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 797671260300235466669) ^ 75032570811799028 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 797671260300235466669) ^ 256122052 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_990387436794572849267 : Nat.Prime 990387436794572849267 := by
  apply lucas_primality 990387436794572849267 (2 : ZMod 990387436794572849267)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (38091824492098955741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (38091824492098955741, 1)] : List FactorBlock).map factorBlockValue).prod) = 990387436794572849267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_13
      · exact prime_seventySixBV_38091824492098955741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 990387436794572849267) ^ 495193718397286424633 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 990387436794572849267) ^ 76183648984197911482 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 990387436794572849267) ^ 26 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_1085098275304144638353 : Nat.Prime 1085098275304144638353 := by
  apply lucas_primality 1085098275304144638353 (3 : ZMod 1085098275304144638353)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (29, 1), (73, 1), (3617, 1), (8856858855973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (29, 1), (73, 1), (3617, 1), (8856858855973, 1)] : List FactorBlock).map factorBlockValue).prod) = 1085098275304144638353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_29
      · exact prime_seventySixBV_73
      · exact prime_seventySixBV_3617
      · exact prime_seventySixBV_8856858855973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1085098275304144638353) ^ 542549137652072319176 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1085098275304144638353) ^ 37417181907039470288 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1085098275304144638353) ^ 14864359935673214224 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1085098275304144638353) ^ 299999523169517456 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1085098275304144638353) ^ 122515024 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_1778797760284545349081 : Nat.Prime 1778797760284545349081 := by
  apply lucas_primality 1778797760284545349081 (7 : ZMod 1778797760284545349081)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (31, 1), (499, 1), (958259400674761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (31, 1), (499, 1), (958259400674761, 1)] : List FactorBlock).map factorBlockValue).prod) = 1778797760284545349081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_5
      · exact prime_seventySixBV_31
      · exact prime_seventySixBV_499
      · exact prime_seventySixBV_958259400674761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1778797760284545349081) ^ 889398880142272674540 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (7 : ZMod 1778797760284545349081) ^ 592932586761515116360 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (7 : ZMod 1778797760284545349081) ^ 355759552056909069816 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (7 : ZMod 1778797760284545349081) ^ 57380572912404688680 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (7 : ZMod 1778797760284545349081) ^ 3564724970510110920 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (7 : ZMod 1778797760284545349081) ^ 1856280 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_13055338435874271891817 : Nat.Prime 13055338435874271891817 := by
  apply lucas_primality 13055338435874271891817 (5 : ZMod 13055338435874271891817)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (11, 2), (617, 1), (1040898346204441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (11, 2), (617, 1), (1040898346204441, 1)] : List FactorBlock).map factorBlockValue).prod) = 13055338435874271891817 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_7
      · exact prime_seventySixBV_11
      · exact prime_seventySixBV_617
      · exact prime_seventySixBV_1040898346204441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 13055338435874271891817) ^ 6527669217937135945908 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 13055338435874271891817) ^ 4351779478624757297272 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 13055338435874271891817) ^ 1865048347982038841688 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 13055338435874271891817) ^ 1186848948715842899256 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 13055338435874271891817) ^ 21159381581643876648 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 13055338435874271891817) ^ 12542376 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_14526703912687189038763 : Nat.Prime 14526703912687189038763 := by
  apply lucas_primality 14526703912687189038763 (2 : ZMod 14526703912687189038763)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (137, 1), (22367, 1), (25343, 1), (31176654191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (137, 1), (22367, 1), (25343, 1), (31176654191, 1)] : List FactorBlock).map factorBlockValue).prod) = 14526703912687189038763 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_137
      · exact prime_seventySixBV_22367
      · exact prime_seventySixBV_25343
      · exact prime_seventySixBV_31176654191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 14526703912687189038763) ^ 7263351956343594519381 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 14526703912687189038763) ^ 4842234637562396346254 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 14526703912687189038763) ^ 106034335129103569626 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 14526703912687189038763) ^ 649470376567585686 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 14526703912687189038763) ^ 573203800366459734 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 14526703912687189038763) ^ 465948136182 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_20209144870542067854863 : Nat.Prime 20209144870542067854863 := by
  apply lucas_primality 20209144870542067854863 (7 : ZMod 20209144870542067854863)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (2861, 1), (191057, 1), (350783, 1), (7528363, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (2861, 1), (191057, 1), (350783, 1), (7528363, 1)] : List FactorBlock).map factorBlockValue).prod) = 20209144870542067854863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_7
      · exact prime_seventySixBV_2861
      · exact prime_seventySixBV_191057
      · exact prime_seventySixBV_350783
      · exact prime_seventySixBV_7528363
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 20209144870542067854863) ^ 10104572435271033927431 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (7 : ZMod 20209144870542067854863) ^ 2887020695791723979266 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (7 : ZMod 20209144870542067854863) ^ 7063664757267412742 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (7 : ZMod 20209144870542067854863) ^ 105775474704104366 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (7 : ZMod 20209144870542067854863) ^ 57611528695923314 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (7 : ZMod 20209144870542067854863) ^ 2684400960812074 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_26042358607299471320473 : Nat.Prime 26042358607299471320473 := by
  apply lucas_primality 26042358607299471320473 (5 : ZMod 26042358607299471320473)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (1085098275304144638353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (1085098275304144638353, 1)] : List FactorBlock).map factorBlockValue).prod) = 26042358607299471320473 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_1085098275304144638353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 26042358607299471320473) ^ 13021179303649735660236 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 26042358607299471320473) ^ 8680786202433157106824 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 26042358607299471320473) ^ 24 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_36801268041507375520207 : Nat.Prime 36801268041507375520207 := by
  apply lucas_primality 36801268041507375520207 (3 : ZMod 36801268041507375520207)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (197, 1), (1511, 1), (1559, 1), (691693, 1), (2123141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (197, 1), (1511, 1), (1559, 1), (691693, 1), (2123141, 1)] : List FactorBlock).map factorBlockValue).prod) = 36801268041507375520207 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_197
      · exact prime_seventySixBV_1511
      · exact prime_seventySixBV_1559
      · exact prime_seventySixBV_691693
      · exact prime_seventySixBV_2123141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 36801268041507375520207) ^ 18400634020753687760103 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 36801268041507375520207) ^ 12267089347169125173402 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 36801268041507375520207) ^ 186808467215773479798 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 36801268041507375520207) ^ 24355571172407263746 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 36801268041507375520207) ^ 23605688288330580834 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 36801268041507375520207) ^ 53204626968188742 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 36801268041507375520207) ^ 17333407456926966 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_138794799292240971200407 : Nat.Prime 138794799292240971200407 := by
  apply lucas_primality 138794799292240971200407 (3 : ZMod 138794799292240971200407)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 1), (797671260300235466669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 1), (797671260300235466669, 1)] : List FactorBlock).map factorBlockValue).prod) = 138794799292240971200407 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_29
      · exact prime_seventySixBV_797671260300235466669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 138794799292240971200407) ^ 69397399646120485600203 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 138794799292240971200407) ^ 46264933097413657066802 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 138794799292240971200407) ^ 4786027561801412800014 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 138794799292240971200407) ^ 174 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_403259579435022322244299 : Nat.Prime 403259579435022322244299 := by
  apply lucas_primality 403259579435022322244299 (2 : ZMod 403259579435022322244299)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 2), (437629, 1), (1269234822564187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 2), (437629, 1), (1269234822564187, 1)] : List FactorBlock).map factorBlockValue).prod) = 403259579435022322244299 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_11
      · exact prime_seventySixBV_437629
      · exact prime_seventySixBV_1269234822564187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 403259579435022322244299) ^ 201629789717511161122149 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 403259579435022322244299) ^ 134419859811674107414766 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 403259579435022322244299) ^ 36659961766820211113118 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 403259579435022322244299) ^ 921464481181599762 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 403259579435022322244299) ^ 317718654 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_471215338583686445133067 : Nat.Prime 471215338583686445133067 := by
  apply lucas_primality 471215338583686445133067 (5 : ZMod 471215338583686445133067)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (79, 1), (44507, 1), (2030579841139217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (79, 1), (44507, 1), (2030579841139217, 1)] : List FactorBlock).map factorBlockValue).prod) = 471215338583686445133067 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_11
      · exact prime_seventySixBV_79
      · exact prime_seventySixBV_44507
      · exact prime_seventySixBV_2030579841139217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 471215338583686445133067) ^ 235607669291843222566533 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 471215338583686445133067) ^ 157071779527895481711022 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 471215338583686445133067) ^ 42837758053062404103006 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 471215338583686445133067) ^ 5964751121312486647254 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 471215338583686445133067) ^ 10587443291699877438 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 471215338583686445133067) ^ 232059498 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_830496836075223435691171 : Nat.Prime 830496836075223435691171 := by
  apply lucas_primality 830496836075223435691171 (3 : ZMod 830496836075223435691171)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (13, 1), (43345329221, 1), (49128224543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (13, 1), (43345329221, 1), (49128224543, 1)] : List FactorBlock).map factorBlockValue).prod) = 830496836075223435691171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_5
      · exact prime_seventySixBV_13
      · exact prime_seventySixBV_43345329221
      · exact prime_seventySixBV_49128224543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 830496836075223435691171) ^ 415248418037611717845585 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 830496836075223435691171) ^ 276832278691741145230390 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 830496836075223435691171) ^ 166099367215044687138234 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 830496836075223435691171) ^ 63884372005786418130090 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 830496836075223435691171) ^ 19160007571770 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 830496836075223435691171) ^ 16904678396190 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_955743175856684700316589 : Nat.Prime 955743175856684700316589 := by
  apply lucas_primality 955743175856684700316589 (2 : ZMod 955743175856684700316589)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (659, 1), (12659468429, 1), (28640482477, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (659, 1), (12659468429, 1), (28640482477, 1)] : List FactorBlock).map factorBlockValue).prod) = 955743175856684700316589 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_659
      · exact prime_seventySixBV_12659468429
      · exact prime_seventySixBV_28640482477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 955743175856684700316589) ^ 477871587928342350158294 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 955743175856684700316589) ^ 1450293134835636874532 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 955743175856684700316589) ^ 75496311809372 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 955743175856684700316589) ^ 33370358778844 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_1437268590309912642057449 : Nat.Prime 1437268590309912642057449 := by
  apply lucas_primality 1437268590309912642057449 (3 : ZMod 1437268590309912642057449)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (101, 1), (1778797760284545349081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (101, 1), (1778797760284545349081, 1)] : List FactorBlock).map factorBlockValue).prod) = 1437268590309912642057449 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_101
      · exact prime_seventySixBV_1778797760284545349081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1437268590309912642057449) ^ 718634295154956321028724 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1437268590309912642057449) ^ 14230382082276362792648 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 1437268590309912642057449) ^ 808 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_3998766497188006174048219 : Nat.Prime 3998766497188006174048219 := by
  apply lucas_primality 3998766497188006174048219 (2 : ZMod 3998766497188006174048219)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (48109, 1), (136889, 1), (243851, 1), (138335651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (48109, 1), (136889, 1), (243851, 1), (138335651, 1)] : List FactorBlock).map factorBlockValue).prod) = 3998766497188006174048219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_48109
      · exact prime_seventySixBV_136889
      · exact prime_seventySixBV_243851
      · exact prime_seventySixBV_138335651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3998766497188006174048219) ^ 1999383248594003087024109 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 3998766497188006174048219) ^ 1332922165729335391349406 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 3998766497188006174048219) ^ 83118886220624128002 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 3998766497188006174048219) ^ 29211744531613249962 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 3998766497188006174048219) ^ 16398401061254643918 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 3998766497188006174048219) ^ 28906261461031518 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_4172577467809719454391357 : Nat.Prime 4172577467809719454391357 := by
  apply lucas_primality 4172577467809719454391357 (2 : ZMod 4172577467809719454391357)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (173, 1), (1163, 1), (471330901677366851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (173, 1), (1163, 1), (471330901677366851, 1)] : List FactorBlock).map factorBlockValue).prod) = 4172577467809719454391357 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_11
      · exact prime_seventySixBV_173
      · exact prime_seventySixBV_1163
      · exact prime_seventySixBV_471330901677366851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4172577467809719454391357) ^ 2086288733904859727195678 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 4172577467809719454391357) ^ 379325224346338132217396 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 4172577467809719454391357) ^ 24118944900634216499372 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 4172577467809719454391357) ^ 3587770823568116469812 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 4172577467809719454391357) ^ 8852756 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_4277254400524325164510091 : Nat.Prime 4277254400524325164510091 := by
  apply lucas_primality 4277254400524325164510091 (2 : ZMod 4277254400524325164510091)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (281, 1), (1277, 1), (19141, 1), (8896213589311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (281, 1), (1277, 1), (19141, 1), (8896213589311, 1)] : List FactorBlock).map factorBlockValue).prod) = 4277254400524325164510091 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_5
      · exact prime_seventySixBV_7
      · exact prime_seventySixBV_281
      · exact prime_seventySixBV_1277
      · exact prime_seventySixBV_19141
      · exact prime_seventySixBV_8896213589311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4277254400524325164510091) ^ 2138627200262162582255045 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 4277254400524325164510091) ^ 855450880104865032902018 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 4277254400524325164510091) ^ 611036342932046452072870 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 4277254400524325164510091) ^ 15221545909339235460890 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 4277254400524325164510091) ^ 3349455286236746409170 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 4277254400524325164510091) ^ 223460341702331391490 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 4277254400524325164510091) ^ 480794931190 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_5346122638889420999039893 : Nat.Prime 5346122638889420999039893 := by
  apply lucas_primality 5346122638889420999039893 (2 : ZMod 5346122638889420999039893)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1303, 1), (6011, 1), (56880908907659027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1303, 1), (6011, 1), (56880908907659027, 1)] : List FactorBlock).map factorBlockValue).prod) = 5346122638889420999039893 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_1303
      · exact prime_seventySixBV_6011
      · exact prime_seventySixBV_56880908907659027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5346122638889420999039893) ^ 2673061319444710499519946 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 5346122638889420999039893) ^ 1782040879629806999679964 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 5346122638889420999039893) ^ 4102933721327260935564 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 5346122638889420999039893) ^ 889389891680156546172 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 5346122638889420999039893) ^ 93987996 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_10243078339240138934206963 : Nat.Prime 10243078339240138934206963 := by
  apply lucas_primality 10243078339240138934206963 (11 : ZMod 10243078339240138934206963)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (37549, 1), (1490639, 1), (924260618929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (37549, 1), (1490639, 1), (924260618929, 1)] : List FactorBlock).map factorBlockValue).prod) = 10243078339240138934206963 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_11
      · exact prime_seventySixBV_37549
      · exact prime_seventySixBV_1490639
      · exact prime_seventySixBV_924260618929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 10243078339240138934206963) ^ 5121539169620069467103481 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (11 : ZMod 10243078339240138934206963) ^ 3414359446413379644735654 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (11 : ZMod 10243078339240138934206963) ^ 931188939930921721291542 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (11 : ZMod 10243078339240138934206963) ^ 272792307098461714938 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (11 : ZMod 10243078339240138934206963) ^ 6871602272072674158 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (11 : ZMod 10243078339240138934206963) ^ 11082456754578 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_40602025843567328843589463 : Nat.Prime 40602025843567328843589463 := by
  apply lucas_primality 40602025843567328843589463 (3 : ZMod 40602025843567328843589463)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (59, 1), (28069, 1), (43562557, 1), (93800280491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (59, 1), (28069, 1), (43562557, 1), (93800280491, 1)] : List FactorBlock).map factorBlockValue).prod) = 40602025843567328843589463 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_59
      · exact prime_seventySixBV_28069
      · exact prime_seventySixBV_43562557
      · exact prime_seventySixBV_93800280491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 40602025843567328843589463) ^ 20301012921783664421794731 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 40602025843567328843589463) ^ 13534008614522442947863154 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 40602025843567328843589463) ^ 688169929551988624467618 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 40602025843567328843589463) ^ 1446507743188832122398 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 40602025843567328843589463) ^ 932039545878065166 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 40602025843567328843589463) ^ 432856124001282 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_40972313356960555736827853 : Nat.Prime 40972313356960555736827853 := by
  apply lucas_primality 40972313356960555736827853 (2 : ZMod 40972313356960555736827853)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (10243078339240138934206963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (10243078339240138934206963, 1)] : List FactorBlock).map factorBlockValue).prod) = 40972313356960555736827853 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_10243078339240138934206963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 40972313356960555736827853) ^ 20486156678480277868413926 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 40972313356960555736827853) ^ 4 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_48621365363535984161722663 : Nat.Prime 48621365363535984161722663 := by
  apply lucas_primality 48621365363535984161722663 (5 : ZMod 48621365363535984161722663)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2087, 1), (447779, 1), (8671410156426349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2087, 1), (447779, 1), (8671410156426349, 1)] : List FactorBlock).map factorBlockValue).prod) = 48621365363535984161722663 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_2087
      · exact prime_seventySixBV_447779
      · exact prime_seventySixBV_8671410156426349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 48621365363535984161722663) ^ 24310682681767992080861331 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 48621365363535984161722663) ^ 16207121787845328053907554 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 48621365363535984161722663) ^ 23297252210606604773226 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 48621365363535984161722663) ^ 108583397978770742178 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 48621365363535984161722663) ^ 5607088638 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_119962994915640185221446571 : Nat.Prime 119962994915640185221446571 := by
  apply lucas_primality 119962994915640185221446571 (7 : ZMod 119962994915640185221446571)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (3998766497188006174048219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (3998766497188006174048219, 1)] : List FactorBlock).map factorBlockValue).prod) = 119962994915640185221446571 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_5
      · exact prime_seventySixBV_3998766497188006174048219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 119962994915640185221446571) ^ 59981497457820092610723285 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (7 : ZMod 119962994915640185221446571) ^ 39987664971880061740482190 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (7 : ZMod 119962994915640185221446571) ^ 23992598983128037044289314 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (7 : ZMod 119962994915640185221446571) ^ 30 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_136139823017900755652823457 : Nat.Prime 136139823017900755652823457 := by
  apply lucas_primality 136139823017900755652823457 (5 : ZMod 136139823017900755652823457)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (41, 1), (313, 1), (110505973383968378767, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (41, 1), (313, 1), (110505973383968378767, 1)] : List FactorBlock).map factorBlockValue).prod) = 136139823017900755652823457 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_41
      · exact prime_seventySixBV_313
      · exact prime_seventySixBV_110505973383968378767
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 136139823017900755652823457) ^ 68069911508950377826411728 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 136139823017900755652823457) ^ 45379941005966918550941152 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 136139823017900755652823457) ^ 3320483488241481845190816 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 136139823017900755652823457) ^ 434951511239299538826912 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (5 : ZMod 136139823017900755652823457) ^ 1231968 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_291728192181215904970335979 : Nat.Prime 291728192181215904970335979 := by
  apply lucas_primality 291728192181215904970335979 (2 : ZMod 291728192181215904970335979)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (48621365363535984161722663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (48621365363535984161722663, 1)] : List FactorBlock).map factorBlockValue).prod) = 291728192181215904970335979 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_48621365363535984161722663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 291728192181215904970335979) ^ 145864096090607952485167989 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 291728192181215904970335979) ^ 97242730727071968323445326 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 291728192181215904970335979) ^ 6 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_425840204700542648013571003 : Nat.Prime 425840204700542648013571003 := by
  apply lucas_primality 425840204700542648013571003 (2 : ZMod 425840204700542648013571003)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (13, 1), (193, 1), (366161, 1), (22605857, 1), (310676929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (13, 1), (193, 1), (366161, 1), (22605857, 1), (310676929, 1)] : List FactorBlock).map factorBlockValue).prod) = 425840204700542648013571003 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_11
      · exact prime_seventySixBV_13
      · exact prime_seventySixBV_193
      · exact prime_seventySixBV_366161
      · exact prime_seventySixBV_22605857
      · exact prime_seventySixBV_310676929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 425840204700542648013571003) ^ 212920102350271324006785501 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 425840204700542648013571003) ^ 141946734900180882671190334 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 425840204700542648013571003) ^ 38712745881867513455779182 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 425840204700542648013571003) ^ 32756938823118665231813154 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 425840204700542648013571003) ^ 2206425931090894549293114 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 425840204700542648013571003) ^ 1162986240207293097882 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 425840204700542648013571003) ^ 18837604993278628986 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 425840204700542648013571003) ^ 1370684994444961338 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_855736030398233321246318873 : Nat.Prime 855736030398233321246318873 := by
  apply lucas_primality 855736030398233321246318873 (3 : ZMod 855736030398233321246318873)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (67, 1), (79, 1), (20209144870542067854863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (67, 1), (79, 1), (20209144870542067854863, 1)] : List FactorBlock).map factorBlockValue).prod) = 855736030398233321246318873 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_67
      · exact prime_seventySixBV_79
      · exact prime_seventySixBV_20209144870542067854863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 855736030398233321246318873) ^ 427868015199116660623159436 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 855736030398233321246318873) ^ 12772179558182586884273416 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 855736030398233321246318873) ^ 10832101650610548370206568 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (3 : ZMod 855736030398233321246318873) ^ 42344 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_1166912768724863619881343917 : Nat.Prime 1166912768724863619881343917 := by
  apply lucas_primality 1166912768724863619881343917 (2 : ZMod 1166912768724863619881343917)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (291728192181215904970335979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (291728192181215904970335979, 1)] : List FactorBlock).map factorBlockValue).prod) = 1166912768724863619881343917 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_291728192181215904970335979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 1166912768724863619881343917) ^ 583456384362431809940671958 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 1166912768724863619881343917) ^ 4 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_11231535398976812341357935211 : Nat.Prime 11231535398976812341357935211 := by
  apply lucas_primality 11231535398976812341357935211 (2 : ZMod 11231535398976812341357935211)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (17, 1), (735104895611, 1), (3328718959529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (17, 1), (735104895611, 1), (3328718959529, 1)] : List FactorBlock).map factorBlockValue).prod) = 11231535398976812341357935211 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_5
      · exact prime_seventySixBV_17
      · exact prime_seventySixBV_735104895611
      · exact prime_seventySixBV_3328718959529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 11231535398976812341357935211) ^ 5615767699488406170678967605 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 11231535398976812341357935211) ^ 3743845132992270780452645070 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 11231535398976812341357935211) ^ 2246307079795362468271587042 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 11231535398976812341357935211) ^ 660678552880988961256349130 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 11231535398976812341357935211) ^ 15278820024238110 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 11231535398976812341357935211) ^ 3374131470854490 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_89852283191814498730863481603 : Nat.Prime 89852283191814498730863481603 := by
  apply lucas_primality 89852283191814498730863481603 (2 : ZMod 89852283191814498730863481603)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (47, 1), (29510917, 1), (220343997527388817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (47, 1), (29510917, 1), (220343997527388817, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481603 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_3
      · exact prime_seventySixBV_7
      · exact prime_seventySixBV_47
      · exact prime_seventySixBV_29510917
      · exact prime_seventySixBV_220343997527388817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 89852283191814498730863481603) ^ 44926141595907249365431740801 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 89852283191814498730863481603) ^ 29950761063938166243621160534 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 89852283191814498730863481603) ^ 12836040455973499818694783086 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 89852283191814498730863481603) ^ 1911750706208819121933265566 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 89852283191814498730863481603) ^ 3044713357833458673306 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 89852283191814498730863481603) ^ 407781851106 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_89852283191814498730863481613 : Nat.Prime 89852283191814498730863481613 := by
  apply lucas_primality 89852283191814498730863481613 (2 : ZMod 89852283191814498730863481613)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 3), (400391, 1), (11419262461272634741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 3), (400391, 1), (11419262461272634741, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_17
      · exact prime_seventySixBV_400391
      · exact prime_seventySixBV_11419262461272634741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 89852283191814498730863481613) ^ 44926141595907249365431740806 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 89852283191814498730863481613) ^ 5285428423047911690050793036 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 89852283191814498730863481613) ^ 224411345888929817930132 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 89852283191814498730863481613) ^ 7868483932 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem prime_seventySixBV_89852283191814498730863481667 : Nat.Prime 89852283191814498730863481667 := by
  apply lucas_primality 89852283191814498730863481667 (2 : ZMod 89852283191814498730863481667)
  · rw [← seventySixBVFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (103, 1), (373, 1), (133888841123, 1), (8733909400009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (103, 1), (373, 1), (133888841123, 1), (8733909400009, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481667 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySixBV_2
      · exact prime_seventySixBV_103
      · exact prime_seventySixBV_373
      · exact prime_seventySixBV_133888841123
      · exact prime_seventySixBV_8733909400009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 89852283191814498730863481667) ^ 44926141595907249365431740833 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 89852283191814498730863481667) ^ 872352263998199016804499822 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 89852283191814498730863481667) ^ 240890839656339138688642042 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 89852283191814498730863481667) ^ 671096130477891542 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide
    · change (2 : ZMod 89852283191814498730863481667) ^ 10287750774209074 ≠ 1
      rw [← seventySixBVFastPow_eq_pow]
      decide

private theorem phi_seventySixBV_89852283191814498730863481600 : Nat.totient 89852283191814498730863481600 = 35656742889470308289562869760 := by
  rw [← show ((([(2, 8), (5, 2), (127, 1), (30449, 1), (3630549714527432453, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481600 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_2, prime_seventySixBV_5, prime_seventySixBV_127, prime_seventySixBV_30449, prime_seventySixBV_3630549714527432453]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481601 : Nat.totient 89852283191814498730863481601 = 87423843105541536959581068528 := by
  rw [← show ((([(37, 1), (12021527966527, 1), (202007606106899, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481601 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_37, prime_seventySixBV_12021527966527, prime_seventySixBV_202007606106899]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481602 : Nat.totient 89852283191814498730863481602 = 25125865573049559042690921984 := by
  rw [← show ((([(2, 1), (3, 1), (7, 2), (47, 1), (29510917, 1), (220343997527388817, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481602 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_2, prime_seventySixBV_3, prime_seventySixBV_7, prime_seventySixBV_47, prime_seventySixBV_29510917, prime_seventySixBV_220343997527388817]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481603 : Nat.totient 89852283191814498730863481603 = 89852283191814498730863481602 := by
  rw [← show ((([(89852283191814498730863481603, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481603 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_89852283191814498730863481603]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481604 : Nat.totient 89852283191814498730863481604 = 41450009616514814747982681600 := by
  rw [← show ((([(2, 2), (13, 1), (2111, 1), (65789, 1), (2165291893, 1), (5746028891, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481604 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_2, prime_seventySixBV_13, prime_seventySixBV_2111, prime_seventySixBV_65789, prime_seventySixBV_2165291893, prime_seventySixBV_5746028891]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481605 : Nat.totient 89852283191814498730863481605 = 47886277370491106305367273280 := by
  rw [← show ((([(3, 1), (5, 1), (1399, 1), (69763, 1), (61375493265200888911, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481605 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_3, prime_seventySixBV_5, prime_seventySixBV_1399, prime_seventySixBV_69763, prime_seventySixBV_61375493265200888911]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481606 : Nat.totient 89852283191814498730863481606 = 44926128202942372713117348960 := by
  rw [← show ((([(2, 1), (3370957, 1), (685393349, 1), (19444913839171, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481606 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_2, prime_seventySixBV_3370957, prime_seventySixBV_685393349, prime_seventySixBV_19444913839171]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481607 : Nat.totient 89852283191814498730863481607 = 88379294936577908590089027360 := by
  rw [← show ((([(61, 1), (14276715829, 1), (103174166011912103, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481607 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_61, prime_seventySixBV_14276715829, prime_seventySixBV_103174166011912103]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481608 : Nat.totient 89852283191814498730863481608 = 29793950796563292092787970560 := by
  rw [← show ((([(2, 3), (3, 2), (191, 1), (1882097942167, 1), (3471530887537, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481608 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_2, prime_seventySixBV_3, prime_seventySixBV_191, prime_seventySixBV_1882097942167, prime_seventySixBV_3471530887537]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481609 : Nat.totient 89852283191814498730863481609 = 70014766123491817192880634960 := by
  rw [← show ((([(7, 1), (11, 1), (1166912768724863619881343917, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481609 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_7, prime_seventySixBV_11, prime_seventySixBV_1166912768724863619881343917]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481610 : Nat.totient 89852283191814498730863481610 = 35666219003688964869728409600 := by
  rw [← show ((([(2, 1), (5, 1), (131, 1), (106109, 1), (1423743271, 1), (454018882529, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481610 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_2, prime_seventySixBV_5, prime_seventySixBV_131, prime_seventySixBV_106109, prime_seventySixBV_1423743271, prime_seventySixBV_454018882529]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481611 : Nat.totient 89852283191814498730863481611 = 59901470328598472377894727136 := by
  rw [← show ((([(3, 1), (1217813, 1), (22937623, 1), (1072207513634963, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481611 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_3, prime_seventySixBV_1217813, prime_seventySixBV_22937623, prime_seventySixBV_1072207513634963]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481612 : Nat.totient 89852283191814498730863481612 = 42283321779044051667377452800 := by
  rw [← show ((([(2, 2), (17, 3), (400391, 1), (11419262461272634741, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481612 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_2, prime_seventySixBV_17, prime_seventySixBV_400391, prime_seventySixBV_11419262461272634741]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481613 : Nat.totient 89852283191814498730863481613 = 89852283191814498730863481612 := by
  rw [← show ((([(89852283191814498730863481613, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481613 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_89852283191814498730863481613]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481614 : Nat.totient 89852283191814498730863481614 = 29938525535350912431976565760 := by
  rw [← show ((([(2, 1), (3, 1), (2467, 1), (315247, 1), (19255631005425982081, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481614 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_2, prime_seventySixBV_3, prime_seventySixBV_2467, prime_seventySixBV_315247, prime_seventySixBV_19255631005425982081]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481615 : Nat.totient 89852283191814498730863481615 = 71402445801993442872405196800 := by
  rw [← show ((([(5, 1), (193, 1), (673, 1), (104911, 1), (90481631, 1), (14574890227, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481615 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_5, prime_seventySixBV_193, prime_seventySixBV_673, prime_seventySixBV_104911, prime_seventySixBV_90481631, prime_seventySixBV_14574890227]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481616 : Nat.totient 89852283191814498730863481616 = 35591588415435155748974438400 := by
  rw [← show ((([(2, 4), (7, 1), (19, 2), (41, 1), (2988586453, 1), (18136530577531, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481616 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_2, prime_seventySixBV_7, prime_seventySixBV_19, prime_seventySixBV_41, prime_seventySixBV_2988586453, prime_seventySixBV_18136530577531]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481617 : Nat.totient 89852283191814498730863481617 = 53317133132386450358681395200 := by
  rw [← show ((([(3, 2), (13, 1), (29, 1), (977, 1), (6163, 1), (10903, 1), (31151, 1), (12949127923, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481617 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_3, prime_seventySixBV_13, prime_seventySixBV_29, prime_seventySixBV_977, prime_seventySixBV_6163, prime_seventySixBV_10903, prime_seventySixBV_31151, prime_seventySixBV_12949127923]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481618 : Nat.totient 89852283191814498730863481618 = 42489990264574331197108384896 := by
  rw [← show ((([(2, 1), (23, 1), (89, 1), (1497208789, 1), (14658816590487323, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481618 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_2, prime_seventySixBV_23, prime_seventySixBV_89, prime_seventySixBV_1497208789, prime_seventySixBV_14658816590487323]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481619 : Nat.totient 89852283191814498730863481619 = 89811681165970931402019889944 := by
  rw [← show ((([(2213, 1), (40602025843567328843589463, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481619 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_2213, prime_seventySixBV_40602025843567328843589463]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481620 : Nat.totient 89852283191814498730863481620 = 21782371682864120904451752960 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (11, 1), (136139823017900755652823457, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481620 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_2, prime_seventySixBV_3, prime_seventySixBV_5, prime_seventySixBV_11, prime_seventySixBV_136139823017900755652823457]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481621 : Nat.totient 89852283191814498730863481621 = 89851546948728965795060852688 := by
  rw [← show ((([(122267, 1), (66199877, 1), (11101014717284419, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481621 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_122267, prime_seventySixBV_66199877, prime_seventySixBV_11101014717284419]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481622 : Nat.totient 89852283191814498730863481622 = 44926017657355580719857624000 := by
  rw [← show ((([(2, 1), (369961, 1), (17943511, 1), (6767616672011941, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481622 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_2, prime_seventySixBV_369961, prime_seventySixBV_17943511, prime_seventySixBV_6767616672011941]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481623 : Nat.totient 89852283191814498730863481623 = 51287459476183991213003827200 := by
  rw [← show ((([(3, 1), (7, 1), (1439, 1), (2441, 1), (20932981, 1), (58190242878377, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481623 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_3, prime_seventySixBV_7, prime_seventySixBV_1439, prime_seventySixBV_2441, prime_seventySixBV_20932981, prime_seventySixBV_58190242878377]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481624 : Nat.totient 89852283191814498730863481624 = 43342358531912161993569876480 := by
  rw [← show ((([(2, 3), (31, 1), (337, 1), (7823, 1), (137427676935044325763, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481624 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_2, prime_seventySixBV_31, prime_seventySixBV_337, prime_seventySixBV_7823, prime_seventySixBV_137427676935044325763]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481625 : Nat.totient 89852283191814498730863481625 = 71867947073522374887570226800 := by
  rw [← show ((([(5, 3), (5179, 1), (138794799292240971200407, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481625 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_5, prime_seventySixBV_5179, prime_seventySixBV_138794799292240971200407]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481626 : Nat.totient 89852283191814498730863481626 = 29911871504021791849084800000 := by
  rw [← show ((([(2, 1), (3, 3), (1009, 1), (3821, 1), (21751, 1), (19842113296580021, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481626 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_2, prime_seventySixBV_3, prime_seventySixBV_1009, prime_seventySixBV_3821, prime_seventySixBV_21751, prime_seventySixBV_19842113296580021]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481627 : Nat.totient 89852283191814498730863481627 = 87402394843019631736846848000 := by
  rw [← show ((([(67, 1), (83, 1), (2069, 1), (615269, 1), (30192251, 1), (420392737, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481627 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_67, prime_seventySixBV_83, prime_seventySixBV_2069, prime_seventySixBV_615269, prime_seventySixBV_30192251, prime_seventySixBV_420392737]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481628 : Nat.totient 89852283191814498730863481628 = 44926089511190034766487374752 := by
  rw [← show ((([(2, 2), (862559, 1), (26042358607299471320473, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481628 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_2, prime_seventySixBV_862559, prime_seventySixBV_26042358607299471320473]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481629 : Nat.totient 89852283191814498730863481629 = 55066789151754986910296633088 := by
  rw [← show ((([(3, 1), (17, 1), (43, 1), (40972313356960555736827853, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481629 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_3, prime_seventySixBV_17, prime_seventySixBV_43, prime_seventySixBV_40972313356960555736827853]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481630 : Nat.totient 89852283191814498730863481630 = 28436766072782379315000205824 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (13, 1), (59761717, 1), (1652207762676191029, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481630 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_2, prime_seventySixBV_5, prime_seventySixBV_7, prime_seventySixBV_13, prime_seventySixBV_59761717, prime_seventySixBV_1652207762676191029]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481631 : Nat.totient 89852283191814498730863481631 = 81683893810688647129014120120 := by
  rw [← show ((([(11, 3), (1639499123083, 1), (41175594000847, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481631 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_11, prime_seventySixBV_1639499123083, prime_seventySixBV_41175594000847]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481632 : Nat.totient 89852283191814498730863481632 = 29937172209034926400154830848 := by
  rw [← show ((([(2, 5), (3, 1), (2239, 1), (141209, 1), (2960338771297028117, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481632 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_2, prime_seventySixBV_3, prime_seventySixBV_2239, prime_seventySixBV_141209, prime_seventySixBV_2960338771297028117]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481633 : Nat.totient 89852283191814498730863481633 = 89426442987113956082849910420 := by
  rw [← show ((([(211, 1), (425840204700542648013571003, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481633 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_211, prime_seventySixBV_425840204700542648013571003]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481634 : Nat.totient 89852283191814498730863481634 = 44697505803025465697147573040 := by
  rw [← show ((([(2, 1), (199, 1), (15541, 1), (14526703912687189038763, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481634 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_2, prime_seventySixBV_199, prime_seventySixBV_15541, prime_seventySixBV_14526703912687189038763]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481635 : Nat.totient 89852283191814498730863481635 = 45299703402534002613345851904 := by
  rw [← show ((([(3, 2), (5, 1), (19, 1), (457, 1), (13000187, 1), (17688752404466743, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481635 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_3, prime_seventySixBV_5, prime_seventySixBV_19, prime_seventySixBV_457, prime_seventySixBV_13000187, prime_seventySixBV_17688752404466743]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481636 : Nat.totient 89852283191814498730863481636 = 44894196372818319520548940320 := by
  rw [← show ((([(2, 2), (1483, 1), (27191, 1), (557061052016354145053, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481636 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_2, prime_seventySixBV_1483, prime_seventySixBV_27191, prime_seventySixBV_557061052016354145053]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481637 : Nat.totient 89852283191814498730863481637 = 76990579209437852961181620000 := by
  rw [← show ((([(7, 1), (3001, 1), (4277254400524325164510091, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481637 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_7, prime_seventySixBV_3001, prime_seventySixBV_4277254400524325164510091]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481638 : Nat.totient 89852283191814498730863481638 = 28840855457500780868753052672 := by
  rw [← show ((([(2, 1), (3, 1), (37, 1), (97, 1), (4172577467809719454391357, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481638 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_2, prime_seventySixBV_3, prime_seventySixBV_37, prime_seventySixBV_97, prime_seventySixBV_4172577467809719454391357]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481639 : Nat.totient 89852283191814498730863481639 = 88714911258100124928500076000 := by
  rw [← show ((([(79, 1), (70386301, 1), (16158977772025661341, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481639 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_79, prime_seventySixBV_70386301, prime_seventySixBV_16158977772025661341]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481640 : Nat.totient 89852283191814498730863481640 = 35940913275904283402290297152 := by
  rw [← show ((([(2, 3), (5, 1), (43749531307, 1), (51344711878912163, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481640 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_2, prime_seventySixBV_5, prime_seventySixBV_43749531307, prime_seventySixBV_51344711878912163]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481641 : Nat.totient 89852283191814498730863481641 = 56923620851041924532185036800 := by
  rw [← show ((([(3, 1), (23, 1), (167, 1), (2161, 1), (14107, 1), (255784440221916521, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481641 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_3, prime_seventySixBV_23, prime_seventySixBV_167, prime_seventySixBV_2161, prime_seventySixBV_14107, prime_seventySixBV_255784440221916521]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481642 : Nat.totient 89852283191814498730863481642 = 40801697619544517402966768640 := by
  rw [← show ((([(2, 1), (11, 1), (1063, 1), (37253, 1), (55697, 1), (1851740460540517, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481642 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_2, prime_seventySixBV_11, prime_seventySixBV_1063, prime_seventySixBV_37253, prime_seventySixBV_55697, prime_seventySixBV_1851740460540517]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481643 : Nat.totient 89852283191814498730863481643 = 82938421029454549950857036544 := by
  rw [← show ((([(13, 1), (43753, 1), (328579, 1), (480770846798109653, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481643 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_13, prime_seventySixBV_43753, prime_seventySixBV_328579, prime_seventySixBV_480770846798109653]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481644 : Nat.totient 89852283191814498730863481644 = 25671806844769217256290150400 := by
  rw [← show ((([(2, 2), (3, 2), (7, 1), (94057, 1), (22810441, 1), (166189573085381, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481644 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_2, prime_seventySixBV_3, prime_seventySixBV_7, prime_seventySixBV_94057, prime_seventySixBV_22810441, prime_seventySixBV_166189573085381]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481645 : Nat.totient 89852283191814498730863481645 = 71876492364932635144931150400 := by
  rw [← show ((([(5, 1), (14431, 1), (203549, 1), (6117777995774625091, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481645 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_5, prime_seventySixBV_14431, prime_seventySixBV_203549, prime_seventySixBV_6117777995774625091]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481646 : Nat.totient 89852283191814498730863481646 = 40055088008640537883699783680 := by
  rw [← show ((([(2, 1), (17, 1), (29, 1), (53, 1), (25860525331, 1), (66487344834077, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481646 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_2, prime_seventySixBV_17, prime_seventySixBV_29, prime_seventySixBV_53, prime_seventySixBV_25860525331, prime_seventySixBV_66487344834077]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481647 : Nat.totient 89852283191814498730863481647 = 59875163435907656103965967360 := by
  rw [← show ((([(3, 1), (2381, 1), (50773, 1), (2816269, 1), (87971400763817, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481647 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_3, prime_seventySixBV_2381, prime_seventySixBV_50773, prime_seventySixBV_2816269, prime_seventySixBV_87971400763817]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481648 : Nat.totient 89852283191814498730863481648 = 43872276368093182355363069952 := by
  rw [← show ((([(2, 4), (59, 1), (257, 1), (389, 1), (5927, 1), (699649, 1), (229593322723, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481648 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_2, prime_seventySixBV_59, prime_seventySixBV_257, prime_seventySixBV_389, prime_seventySixBV_5927, prime_seventySixBV_699649, prime_seventySixBV_229593322723]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481649 : Nat.totient 89852283191814498730863481649 = 87875997522525755699710334976 := by
  rw [← show ((([(47, 1), (1847, 1), (8803, 1), (23993, 1), (26833, 1), (182633262523, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481649 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_47, prime_seventySixBV_1847, prime_seventySixBV_8803, prime_seventySixBV_23993, prime_seventySixBV_26833, prime_seventySixBV_182633262523]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481650 : Nat.totient 89852283191814498730863481650 = 23878827437448112156109856000 := by
  rw [← show ((([(2, 1), (3, 1), (5, 2), (293, 1), (5200451, 1), (393123702240337477, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481650 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_2, prime_seventySixBV_3, prime_seventySixBV_5, prime_seventySixBV_293, prime_seventySixBV_5200451, prime_seventySixBV_393123702240337477]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481651 : Nat.totient 89852283191814498730863481651 = 77016242735840998912168684152 := by
  rw [← show ((([(7, 5), (5346122638889420999039893, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481651 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_7, prime_seventySixBV_5346122638889420999039893]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481652 : Nat.totient 89852283191814498730863481652 = 43686573864694561911596774400 := by
  rw [← show ((([(2, 2), (71, 1), (73, 1), (1026947, 1), (10877693, 1), (387974416741, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481652 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_2, prime_seventySixBV_71, prime_seventySixBV_73, prime_seventySixBV_1026947, prime_seventySixBV_10877693, prime_seventySixBV_387974416741]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481653 : Nat.totient 89852283191814498730863481653 = 54307547895002023236743200800 := by
  rw [← show ((([(3, 4), (11, 1), (367, 1), (1613207191, 1), (170331589700039, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481653 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_3, prime_seventySixBV_11, prime_seventySixBV_367, prime_seventySixBV_1613207191, prime_seventySixBV_170331589700039]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481654 : Nat.totient 89852283191814498730863481654 = 42539589404892650769163369632 := by
  rw [← show ((([(2, 1), (19, 1), (1933, 1), (23762806367, 1), (51477321037603, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481654 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_2, prime_seventySixBV_19, prime_seventySixBV_1933, prime_seventySixBV_23762806367, prime_seventySixBV_51477321037603]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481655 : Nat.totient 89852283191814498730863481655 = 69563045370961884965311200000 := by
  rw [← show ((([(5, 1), (31, 1), (5527901, 1), (104866593961181589401, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481655 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_5, prime_seventySixBV_31, prime_seventySixBV_5527901, prime_seventySixBV_104866593961181589401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481656 : Nat.totient 89852283191814498730863481656 = 27646856298023843407702468608 := by
  rw [← show ((([(2, 3), (3, 1), (13, 1), (402497257, 1), (715503229263626009, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481656 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_2, prime_seventySixBV_3, prime_seventySixBV_13, prime_seventySixBV_402497257, prime_seventySixBV_715503229263626009]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481657 : Nat.totient 89852283191814498730863481657 = 87622534362540853325024787840 := by
  rw [← show ((([(41, 1), (2293, 1), (955743175856684700316589, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481657 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_41, prime_seventySixBV_2293, prime_seventySixBV_955743175856684700316589]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481658 : Nat.totient 89852283191814498730863481658 = 38262846709506308657752857600 := by
  rw [← show ((([(2, 1), (7, 1), (157, 1), (2152231064311, 1), (18993829431361, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481658 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_2, prime_seventySixBV_7, prime_seventySixBV_157, prime_seventySixBV_2152231064311, prime_seventySixBV_18993829431361]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481659 : Nat.totient 89852283191814498730863481659 = 59901520147101458898036139656 := by
  rw [← show ((([(3, 1), (30241459, 1), (990387436794572849267, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481659 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_3, prime_seventySixBV_30241459, prime_seventySixBV_990387436794572849267]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481660 : Nat.totient 89852283191814498730863481660 = 35863948684500533325254507840 := by
  rw [← show ((([(2, 2), (5, 1), (467, 1), (10796459, 1), (891047592546791411, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481660 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_2, prime_seventySixBV_5, prime_seventySixBV_467, prime_seventySixBV_10796459, prime_seventySixBV_891047592546791411]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481661 : Nat.totient 89852283191814498730863481661 = 89851452694978423507427682300 := by
  rw [← show ((([(108191, 1), (830496836075223435691171, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481661 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_108191, prime_seventySixBV_830496836075223435691171]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481662 : Nat.totient 89852283191814498730863481662 = 29580362767411513961975672832 := by
  rw [← show ((([(2, 1), (3, 2), (113, 1), (479, 1), (683, 1), (9763916497, 1), (13829226667, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481662 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_2, prime_seventySixBV_3, prime_seventySixBV_113, prime_seventySixBV_479, prime_seventySixBV_683, prime_seventySixBV_9763916497, prime_seventySixBV_13829226667]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481663 : Nat.totient 89852283191814498730863481663 = 84566710525806149935095393280 := by
  rw [← show ((([(17, 1), (592157, 1), (59079017, 1), (151081075485731, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481663 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_17, prime_seventySixBV_592157, prime_seventySixBV_59079017, prime_seventySixBV_151081075485731]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481664 : Nat.totient 89852283191814498730863481664 = 39066210083344706893225943040 := by
  rw [← show ((([(2, 6), (11, 1), (23, 1), (830194792153, 1), (6684187399289, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481664 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_2, prime_seventySixBV_11, prime_seventySixBV_23, prime_seventySixBV_830194792153, prime_seventySixBV_6684187399289]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481665 : Nat.totient 89852283191814498730863481665 = 41075329459115199419823305856 := by
  rw [← show ((([(3, 1), (5, 1), (7, 1), (855736030398233321246318873, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481665 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_3, prime_seventySixBV_5, prime_seventySixBV_7, prime_seventySixBV_855736030398233321246318873]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481666 : Nat.totient 89852283191814498730863481666 = 44370689416751541032479465344 := by
  rw [← show ((([(2, 1), (103, 1), (373, 1), (133888841123, 1), (8733909400009, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481666 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_2, prime_seventySixBV_103, prime_seventySixBV_373, prime_seventySixBV_133888841123, prime_seventySixBV_8733909400009]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481667 : Nat.totient 89852283191814498730863481667 = 89852283191814498730863481666 := by
  rw [← show ((([(89852283191814498730863481667, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481667 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_89852283191814498730863481667]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481668 : Nat.totient 89852283191814498730863481668 = 29455941477993170031183075840 := by
  rw [← show ((([(2, 2), (3, 1), (61, 1), (15443, 1), (15739, 1), (666269, 1), (757983273923, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481668 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_2, prime_seventySixBV_3, prime_seventySixBV_61, prime_seventySixBV_15443, prime_seventySixBV_15739, prime_seventySixBV_666269, prime_seventySixBV_757983273923]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481669 : Nat.totient 89852283191814498730863481669 = 82914873421009151799112089600 := by
  rw [← show ((([(13, 1), (4861, 1), (9929, 1), (318743, 1), (4003361, 1), (112224899, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481669 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_13, prime_seventySixBV_4861, prime_seventySixBV_9929, prime_seventySixBV_318743, prime_seventySixBV_4003361, prime_seventySixBV_112224899]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481670 : Nat.totient 89852283191814498730863481670 = 35940913267143791286522084864 := by
  rw [← show ((([(2, 1), (5, 1), (3750874823, 1), (2395502047704952129, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481670 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_2, prime_seventySixBV_5, prime_seventySixBV_3750874823, prime_seventySixBV_2395502047704952129]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481671 : Nat.totient 89852283191814498730863481671 = 59886577781557869771238179456 := by
  rw [← show ((([(3, 2), (4153, 1), (115019, 1), (20900423646780275317, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481671 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_3, prime_seventySixBV_4153, prime_seventySixBV_115019, prime_seventySixBV_20900423646780275317]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481672 : Nat.totient 89852283191814498730863481672 = 37606646266349966553885032448 := by
  rw [← show ((([(2, 3), (7, 1), (43, 1), (7937, 1), (31379, 1), (149822539859765183, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481672 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_2, prime_seventySixBV_7, prime_seventySixBV_43, prime_seventySixBV_7937, prime_seventySixBV_31379, prime_seventySixBV_149822539859765183]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481673 : Nat.totient 89852283191814498730863481673 = 85120737112266515240911200000 := by
  rw [← show ((([(19, 1), (34501, 1), (11918981, 1), (21414277, 1), (537033391, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481673 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_19, prime_seventySixBV_34501, prime_seventySixBV_11918981, prime_seventySixBV_21414277, prime_seventySixBV_537033391]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481674 : Nat.totient 89852283191814498730863481674 = 29826483583050539654148480000 := by
  rw [← show ((([(2, 1), (3, 1), (241, 1), (114553301, 1), (152757959, 1), (3550989341, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481674 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_2, prime_seventySixBV_3, prime_seventySixBV_241, prime_seventySixBV_114553301, prime_seventySixBV_152757959, prime_seventySixBV_3550989341]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481675 : Nat.totient 89852283191814498730863481675 = 61381267633685777331688243200 := by
  rw [← show ((([(5, 2), (11, 1), (29, 1), (37, 1), (16823, 1), (17047, 1), (5394097, 1), (196845977, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481675 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_5, prime_seventySixBV_11, prime_seventySixBV_29, prime_seventySixBV_37, prime_seventySixBV_16823, prime_seventySixBV_17047, prime_seventySixBV_5394097, prime_seventySixBV_196845977]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481676 : Nat.totient 89852283191814498730863481676 = 44926114425482204599899353600 := by
  rw [← show ((([(2, 2), (1653599, 1), (27562133741, 1), (492862855841, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481676 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_2, prime_seventySixBV_1653599, prime_seventySixBV_27562133741, prime_seventySixBV_492862855841]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481677 : Nat.totient 89852283191814498730863481677 = 59790798426950546073057146880 := by
  rw [← show ((([(3, 1), (541, 1), (444848755067, 1), (124450950496897, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481677 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_3, prime_seventySixBV_541, prime_seventySixBV_444848755067, prime_seventySixBV_124450950496897]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481678 : Nat.totient 89852283191814498730863481678 = 44926104794639207858054999856 := by
  rw [← show ((([(2, 1), (1220777, 1), (36801268041507375520207, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481678 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_2, prime_seventySixBV_1220777, prime_seventySixBV_36801268041507375520207]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481679 : Nat.totient 89852283191814498730863481679 = 76296464766347157800840018520 := by
  rw [← show ((([(7, 1), (107, 1), (119962994915640185221446571, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481679 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_7, prime_seventySixBV_107, prime_seventySixBV_119962994915640185221446571]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481680 : Nat.totient 89852283191814498730863481680 = 22551161271633637676901089280 := by
  rw [← show ((([(2, 4), (3, 3), (5, 1), (17, 1), (735104895611, 1), (3328718959529, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481680 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_2, prime_seventySixBV_3, prime_seventySixBV_5, prime_seventySixBV_17, prime_seventySixBV_735104895611, prime_seventySixBV_3328718959529]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481681 : Nat.totient 89852283191814498730863481681 = 89850686403814295410804910400 := by
  rw [← show ((([(84551, 1), (168277, 1), (687640277, 1), (9183839839, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481681 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_84551, prime_seventySixBV_168277, prime_seventySixBV_687640277, prime_seventySixBV_9183839839]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481682 : Nat.totient 89852283191814498730863481682 = 41459549280367293631529064000 := by
  rw [← show ((([(2, 1), (13, 3), (3863, 1), (2573783231, 1), (2056706826301, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481682 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_2, prime_seventySixBV_13, prime_seventySixBV_3863, prime_seventySixBV_2573783231, prime_seventySixBV_2056706826301]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481683 : Nat.totient 89852283191814498730863481683 = 59901522127805378232001601000 := by
  rw [← show ((([(3, 1), (844247430011, 1), (35476283372930051, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481683 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_3, prime_seventySixBV_844247430011, prime_seventySixBV_35476283372930051]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481684 : Nat.totient 89852283191814498730863481684 = 44923267058726629540147594688 := by
  rw [← show ((([(2, 2), (15629, 1), (1437268590309912642057449, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481684 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_2, prime_seventySixBV_15629, prime_seventySixBV_1437268590309912642057449]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481685 : Nat.totient 89852283191814498730863481685 = 71880213515133858895401629904 := by
  rw [← show ((([(5, 1), (44563, 1), (403259579435022322244299, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481685 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_5, prime_seventySixBV_44563, prime_seventySixBV_403259579435022322244299]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481686 : Nat.totient 89852283191814498730863481686 = 22580732119614213130099920000 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (11, 1), (31, 1), (4831, 1), (18704263, 1), (69430103056571, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481686 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_2, prime_seventySixBV_3, prime_seventySixBV_7, prime_seventySixBV_11, prime_seventySixBV_31, prime_seventySixBV_4831, prime_seventySixBV_18704263, prime_seventySixBV_69430103056571]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481687 : Nat.totient 89852283191814498730863481687 = 84299240233731758754340800000 := by
  rw [← show ((([(23, 1), (101, 1), (109, 1), (5701, 1), (62244698619035204941, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481687 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_23, prime_seventySixBV_101, prime_seventySixBV_109, prime_seventySixBV_5701, prime_seventySixBV_62244698619035204941]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481688 : Nat.totient 89852283191814498730863481688 = 44926141595907249365431740840 := by
  rw [← show ((([(2, 3), (11231535398976812341357935211, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481688 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_2, prime_seventySixBV_11231535398976812341357935211]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481689 : Nat.totient 89852283191814498730863481689 = 59757939515758587244971540480 := by
  rw [← show ((([(3, 2), (641, 1), (1193, 1), (13055338435874271891817, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481689 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_3, prime_seventySixBV_641, prime_seventySixBV_1193, prime_seventySixBV_13055338435874271891817]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481690 : Nat.totient 89852283191814498730863481690 = 35940897949710260576857624704 := by
  rw [← show ((([(2, 1), (5, 1), (2696779, 1), (17973443, 1), (185375562083177, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481690 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_2, prime_seventySixBV_5, prime_seventySixBV_2696779, prime_seventySixBV_17973443, prime_seventySixBV_185375562083177]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481691 : Nat.totient 89852283191814498730863481691 = 89852283060954928565380167384 := by
  rw [← show ((([(686631349, 1), (130859570164796682959, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481691 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_686631349, prime_seventySixBV_130859570164796682959]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481692 : Nat.totient 89852283191814498730863481692 = 28183972951340868501928224000 := by
  rw [← show ((([(2, 2), (3, 1), (19, 1), (149, 1), (1625516111, 1), (1627109285643901, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481692 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_2, prime_seventySixBV_3, prime_seventySixBV_19, prime_seventySixBV_149, prime_seventySixBV_1625516111, prime_seventySixBV_1627109285643901]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481693 : Nat.totient 89852283191814498730863481693 = 77016236134780453523728129920 := by
  rw [← show ((([(7, 1), (11686303, 1), (7526405981, 1), (145937295593, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481693 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_7, prime_seventySixBV_11686303, prime_seventySixBV_7526405981, prime_seventySixBV_145937295593]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481694 : Nat.totient 89852283191814498730863481694 = 44224501956756140248628510232 := by
  rw [← show ((([(2, 1), (67, 1), (1423, 1), (471215338583686445133067, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481694 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_2, prime_seventySixBV_67, prime_seventySixBV_1423, prime_seventySixBV_471215338583686445133067]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481695 : Nat.totient 89852283191814498730863481695 = 44219041134921310936647195648 := by
  rw [← show ((([(3, 1), (5, 1), (13, 1), (2777, 1), (18331485479, 1), (9051508570747, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481695 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_3, prime_seventySixBV_5, prime_seventySixBV_13, prime_seventySixBV_2777, prime_seventySixBV_18331485479, prime_seventySixBV_9051508570747]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481696 : Nat.totient 89852283191814498730863481696 = 43964572372647293986966803456 := by
  rw [← show ((([(2, 5), (47, 1), (7723, 1), (97206377, 1), (79579368663719, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481696 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_2, prime_seventySixBV_47, prime_seventySixBV_7723, prime_seventySixBV_97206377, prime_seventySixBV_79579368663719]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481697 : Nat.totient 89852283191814498730863481697 = 76878939621509546643966654720 := by
  rw [← show ((([(11, 1), (17, 1), (3991807, 1), (120369920941657652333, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481697 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_11, prime_seventySixBV_17, prime_seventySixBV_3991807, prime_seventySixBV_120369920941657652333]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481698 : Nat.totient 89852283191814498730863481698 = 29115531338836781051419115520 := by
  rw [← show ((([(2, 1), (3, 2), (41, 1), (359, 1), (1249, 1), (211351817, 1), (1284724134143, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481698 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_2, prime_seventySixBV_3, prime_seventySixBV_41, prime_seventySixBV_359, prime_seventySixBV_1249, prime_seventySixBV_211351817, prime_seventySixBV_1284724134143]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481699 : Nat.totient 89852283191814498730863481699 = 88104394785745828782302456160 := by
  rw [← show ((([(53, 1), (2011, 1), (10099, 1), (83476225741034673047, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481699 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_53, prime_seventySixBV_2011, prime_seventySixBV_10099, prime_seventySixBV_83476225741034673047]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481700 : Nat.totient 89852283191814498730863481700 = 30806497094294287050414085440 := by
  rw [← show ((([(2, 2), (5, 2), (7, 2), (754221535219, 1), (24312751353707, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481700 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_2, prime_seventySixBV_5, prime_seventySixBV_7, prime_seventySixBV_754221535219, prime_seventySixBV_24312751353707]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySixBV_89852283191814498730863481701 : Nat.totient 89852283191814498730863481701 = 59864290791721750928303424000 := by
  rw [← show ((([(3, 1), (1789, 1), (15973, 1), (3887874511, 1), (269586904201, 1)] : List FactorBlock).map factorBlockValue).prod) = 89852283191814498730863481701 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySixBV_3, prime_seventySixBV_1789, prime_seventySixBV_15973, prime_seventySixBV_3887874511, prime_seventySixBV_269586904201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64SeventySixBV : certifiedKill 1 89852283191814498730863481599 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_seventySixBV_89852283191814498730863481600, phi_seventySixBV_89852283191814498730863481601, phi_seventySixBV_89852283191814498730863481602,
    phi_seventySixBV_89852283191814498730863481603, phi_seventySixBV_89852283191814498730863481604, phi_seventySixBV_89852283191814498730863481605,
    phi_seventySixBV_89852283191814498730863481606, phi_seventySixBV_89852283191814498730863481607, phi_seventySixBV_89852283191814498730863481608,
    phi_seventySixBV_89852283191814498730863481609, phi_seventySixBV_89852283191814498730863481610, phi_seventySixBV_89852283191814498730863481611,
    phi_seventySixBV_89852283191814498730863481612, phi_seventySixBV_89852283191814498730863481613, phi_seventySixBV_89852283191814498730863481614,
    phi_seventySixBV_89852283191814498730863481615, phi_seventySixBV_89852283191814498730863481616, phi_seventySixBV_89852283191814498730863481617,
    phi_seventySixBV_89852283191814498730863481618, phi_seventySixBV_89852283191814498730863481619, phi_seventySixBV_89852283191814498730863481620,
    phi_seventySixBV_89852283191814498730863481621, phi_seventySixBV_89852283191814498730863481622, phi_seventySixBV_89852283191814498730863481623,
    phi_seventySixBV_89852283191814498730863481624, phi_seventySixBV_89852283191814498730863481625, phi_seventySixBV_89852283191814498730863481626,
    phi_seventySixBV_89852283191814498730863481627, phi_seventySixBV_89852283191814498730863481628, phi_seventySixBV_89852283191814498730863481629,
    phi_seventySixBV_89852283191814498730863481630, phi_seventySixBV_89852283191814498730863481631, phi_seventySixBV_89852283191814498730863481632,
    phi_seventySixBV_89852283191814498730863481633, phi_seventySixBV_89852283191814498730863481634, phi_seventySixBV_89852283191814498730863481635,
    phi_seventySixBV_89852283191814498730863481636, phi_seventySixBV_89852283191814498730863481637, phi_seventySixBV_89852283191814498730863481638,
    phi_seventySixBV_89852283191814498730863481639, phi_seventySixBV_89852283191814498730863481640, phi_seventySixBV_89852283191814498730863481641,
    phi_seventySixBV_89852283191814498730863481642, phi_seventySixBV_89852283191814498730863481643, phi_seventySixBV_89852283191814498730863481644,
    phi_seventySixBV_89852283191814498730863481645, phi_seventySixBV_89852283191814498730863481646, phi_seventySixBV_89852283191814498730863481647,
    phi_seventySixBV_89852283191814498730863481648, phi_seventySixBV_89852283191814498730863481649, phi_seventySixBV_89852283191814498730863481650,
    phi_seventySixBV_89852283191814498730863481651, phi_seventySixBV_89852283191814498730863481652, phi_seventySixBV_89852283191814498730863481653,
    phi_seventySixBV_89852283191814498730863481654, phi_seventySixBV_89852283191814498730863481655, phi_seventySixBV_89852283191814498730863481656,
    phi_seventySixBV_89852283191814498730863481657, phi_seventySixBV_89852283191814498730863481658, phi_seventySixBV_89852283191814498730863481659,
    phi_seventySixBV_89852283191814498730863481660, phi_seventySixBV_89852283191814498730863481661, phi_seventySixBV_89852283191814498730863481662,
    phi_seventySixBV_89852283191814498730863481663, phi_seventySixBV_89852283191814498730863481664, phi_seventySixBV_89852283191814498730863481665,
    phi_seventySixBV_89852283191814498730863481666, phi_seventySixBV_89852283191814498730863481667, phi_seventySixBV_89852283191814498730863481668,
    phi_seventySixBV_89852283191814498730863481669, phi_seventySixBV_89852283191814498730863481670, phi_seventySixBV_89852283191814498730863481671,
    phi_seventySixBV_89852283191814498730863481672, phi_seventySixBV_89852283191814498730863481673, phi_seventySixBV_89852283191814498730863481674,
    phi_seventySixBV_89852283191814498730863481675, phi_seventySixBV_89852283191814498730863481676, phi_seventySixBV_89852283191814498730863481677,
    phi_seventySixBV_89852283191814498730863481678, phi_seventySixBV_89852283191814498730863481679, phi_seventySixBV_89852283191814498730863481680,
    phi_seventySixBV_89852283191814498730863481681, phi_seventySixBV_89852283191814498730863481682, phi_seventySixBV_89852283191814498730863481683,
    phi_seventySixBV_89852283191814498730863481684, phi_seventySixBV_89852283191814498730863481685, phi_seventySixBV_89852283191814498730863481686,
    phi_seventySixBV_89852283191814498730863481687, phi_seventySixBV_89852283191814498730863481688, phi_seventySixBV_89852283191814498730863481689,
    phi_seventySixBV_89852283191814498730863481690, phi_seventySixBV_89852283191814498730863481691, phi_seventySixBV_89852283191814498730863481692,
    phi_seventySixBV_89852283191814498730863481693, phi_seventySixBV_89852283191814498730863481694, phi_seventySixBV_89852283191814498730863481695,
    phi_seventySixBV_89852283191814498730863481696, phi_seventySixBV_89852283191814498730863481697, phi_seventySixBV_89852283191814498730863481698,
    phi_seventySixBV_89852283191814498730863481699, phi_seventySixBV_89852283191814498730863481700, phi_seventySixBV_89852283191814498730863481701]

end TotientTailPeriodKiller
end Erdos249257
