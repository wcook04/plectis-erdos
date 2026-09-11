import Erdos249257.DiagonalPincerCertificatesT64

-- Explicit full-window certificate for the earliest successful 56P sweep coordinate.
namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def fiftySixBBFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem fiftySixBBFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) :
    fiftySixBBFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [fiftySixBBFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [fiftySixBBFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then fiftySixBBFastPow a n * fiftySixBBFastPow a n * a
        else fiftySixBBFastPow a n * fiftySixBBFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_fiftySixBB_2 : Nat.Prime 2 := by norm_num
private theorem prime_fiftySixBB_3 : Nat.Prime 3 := by norm_num
private theorem prime_fiftySixBB_5 : Nat.Prime 5 := by norm_num
private theorem prime_fiftySixBB_7 : Nat.Prime 7 := by norm_num
private theorem prime_fiftySixBB_11 : Nat.Prime 11 := by norm_num
private theorem prime_fiftySixBB_13 : Nat.Prime 13 := by norm_num
private theorem prime_fiftySixBB_17 : Nat.Prime 17 := by norm_num
private theorem prime_fiftySixBB_19 : Nat.Prime 19 := by norm_num
private theorem prime_fiftySixBB_23 : Nat.Prime 23 := by norm_num
private theorem prime_fiftySixBB_29 : Nat.Prime 29 := by norm_num
private theorem prime_fiftySixBB_31 : Nat.Prime 31 := by norm_num
private theorem prime_fiftySixBB_37 : Nat.Prime 37 := by norm_num
private theorem prime_fiftySixBB_41 : Nat.Prime 41 := by norm_num
private theorem prime_fiftySixBB_43 : Nat.Prime 43 := by norm_num
private theorem prime_fiftySixBB_47 : Nat.Prime 47 := by norm_num
private theorem prime_fiftySixBB_53 : Nat.Prime 53 := by norm_num
private theorem prime_fiftySixBB_59 : Nat.Prime 59 := by norm_num
private theorem prime_fiftySixBB_61 : Nat.Prime 61 := by norm_num
private theorem prime_fiftySixBB_67 : Nat.Prime 67 := by norm_num
private theorem prime_fiftySixBB_71 : Nat.Prime 71 := by norm_num
private theorem prime_fiftySixBB_73 : Nat.Prime 73 := by norm_num
private theorem prime_fiftySixBB_79 : Nat.Prime 79 := by norm_num
private theorem prime_fiftySixBB_83 : Nat.Prime 83 := by norm_num
private theorem prime_fiftySixBB_89 : Nat.Prime 89 := by norm_num
private theorem prime_fiftySixBB_97 : Nat.Prime 97 := by norm_num
private theorem prime_fiftySixBB_101 : Nat.Prime 101 := by norm_num
private theorem prime_fiftySixBB_103 : Nat.Prime 103 := by norm_num
private theorem prime_fiftySixBB_107 : Nat.Prime 107 := by norm_num
private theorem prime_fiftySixBB_109 : Nat.Prime 109 := by norm_num
private theorem prime_fiftySixBB_113 : Nat.Prime 113 := by norm_num
private theorem prime_fiftySixBB_127 : Nat.Prime 127 := by norm_num
private theorem prime_fiftySixBB_131 : Nat.Prime 131 := by norm_num
private theorem prime_fiftySixBB_137 : Nat.Prime 137 := by norm_num
private theorem prime_fiftySixBB_139 : Nat.Prime 139 := by norm_num
private theorem prime_fiftySixBB_149 : Nat.Prime 149 := by norm_num
private theorem prime_fiftySixBB_151 : Nat.Prime 151 := by norm_num
private theorem prime_fiftySixBB_157 : Nat.Prime 157 := by norm_num
private theorem prime_fiftySixBB_163 : Nat.Prime 163 := by norm_num
private theorem prime_fiftySixBB_167 : Nat.Prime 167 := by norm_num
private theorem prime_fiftySixBB_173 : Nat.Prime 173 := by norm_num
private theorem prime_fiftySixBB_179 : Nat.Prime 179 := by norm_num
private theorem prime_fiftySixBB_181 : Nat.Prime 181 := by norm_num
private theorem prime_fiftySixBB_191 : Nat.Prime 191 := by norm_num
private theorem prime_fiftySixBB_193 : Nat.Prime 193 := by norm_num
private theorem prime_fiftySixBB_197 : Nat.Prime 197 := by norm_num
private theorem prime_fiftySixBB_211 : Nat.Prime 211 := by norm_num
private theorem prime_fiftySixBB_223 : Nat.Prime 223 := by norm_num
private theorem prime_fiftySixBB_229 : Nat.Prime 229 := by norm_num
private theorem prime_fiftySixBB_233 : Nat.Prime 233 := by norm_num
private theorem prime_fiftySixBB_239 : Nat.Prime 239 := by norm_num
private theorem prime_fiftySixBB_241 : Nat.Prime 241 := by norm_num
private theorem prime_fiftySixBB_251 : Nat.Prime 251 := by norm_num
private theorem prime_fiftySixBB_269 : Nat.Prime 269 := by norm_num
private theorem prime_fiftySixBB_271 : Nat.Prime 271 := by norm_num
private theorem prime_fiftySixBB_277 : Nat.Prime 277 := by norm_num
private theorem prime_fiftySixBB_281 : Nat.Prime 281 := by norm_num
private theorem prime_fiftySixBB_283 : Nat.Prime 283 := by norm_num
private theorem prime_fiftySixBB_293 : Nat.Prime 293 := by norm_num
private theorem prime_fiftySixBB_307 : Nat.Prime 307 := by norm_num
private theorem prime_fiftySixBB_311 : Nat.Prime 311 := by norm_num
private theorem prime_fiftySixBB_317 : Nat.Prime 317 := by norm_num
private theorem prime_fiftySixBB_331 : Nat.Prime 331 := by norm_num
private theorem prime_fiftySixBB_337 : Nat.Prime 337 := by norm_num
private theorem prime_fiftySixBB_347 : Nat.Prime 347 := by norm_num
private theorem prime_fiftySixBB_353 : Nat.Prime 353 := by norm_num
private theorem prime_fiftySixBB_373 : Nat.Prime 373 := by norm_num
private theorem prime_fiftySixBB_379 : Nat.Prime 379 := by norm_num
private theorem prime_fiftySixBB_389 : Nat.Prime 389 := by norm_num
private theorem prime_fiftySixBB_397 : Nat.Prime 397 := by norm_num
private theorem prime_fiftySixBB_419 : Nat.Prime 419 := by norm_num
private theorem prime_fiftySixBB_421 : Nat.Prime 421 := by norm_num
private theorem prime_fiftySixBB_433 : Nat.Prime 433 := by norm_num
private theorem prime_fiftySixBB_449 : Nat.Prime 449 := by norm_num
private theorem prime_fiftySixBB_457 : Nat.Prime 457 := by norm_num
private theorem prime_fiftySixBB_461 : Nat.Prime 461 := by norm_num
private theorem prime_fiftySixBB_463 : Nat.Prime 463 := by norm_num
private theorem prime_fiftySixBB_467 : Nat.Prime 467 := by norm_num
private theorem prime_fiftySixBB_487 : Nat.Prime 487 := by norm_num
private theorem prime_fiftySixBB_499 : Nat.Prime 499 := by norm_num
private theorem prime_fiftySixBB_503 : Nat.Prime 503 := by norm_num
private theorem prime_fiftySixBB_509 : Nat.Prime 509 := by norm_num
private theorem prime_fiftySixBB_521 : Nat.Prime 521 := by norm_num
private theorem prime_fiftySixBB_541 : Nat.Prime 541 := by norm_num
private theorem prime_fiftySixBB_587 : Nat.Prime 587 := by norm_num
private theorem prime_fiftySixBB_593 : Nat.Prime 593 := by norm_num
private theorem prime_fiftySixBB_599 : Nat.Prime 599 := by norm_num
private theorem prime_fiftySixBB_601 : Nat.Prime 601 := by norm_num
private theorem prime_fiftySixBB_613 : Nat.Prime 613 := by norm_num
private theorem prime_fiftySixBB_617 : Nat.Prime 617 := by norm_num
private theorem prime_fiftySixBB_619 : Nat.Prime 619 := by norm_num
private theorem prime_fiftySixBB_631 : Nat.Prime 631 := by norm_num
private theorem prime_fiftySixBB_661 : Nat.Prime 661 := by norm_num
private theorem prime_fiftySixBB_677 : Nat.Prime 677 := by norm_num
private theorem prime_fiftySixBB_727 : Nat.Prime 727 := by norm_num
private theorem prime_fiftySixBB_761 : Nat.Prime 761 := by norm_num
private theorem prime_fiftySixBB_769 : Nat.Prime 769 := by norm_num
private theorem prime_fiftySixBB_797 : Nat.Prime 797 := by norm_num
private theorem prime_fiftySixBB_827 : Nat.Prime 827 := by norm_num
private theorem prime_fiftySixBB_839 : Nat.Prime 839 := by norm_num
private theorem prime_fiftySixBB_853 : Nat.Prime 853 := by norm_num
private theorem prime_fiftySixBB_859 : Nat.Prime 859 := by norm_num
private theorem prime_fiftySixBB_863 : Nat.Prime 863 := by norm_num
private theorem prime_fiftySixBB_911 : Nat.Prime 911 := by norm_num
private theorem prime_fiftySixBB_937 : Nat.Prime 937 := by norm_num
private theorem prime_fiftySixBB_953 : Nat.Prime 953 := by norm_num
private theorem prime_fiftySixBB_967 : Nat.Prime 967 := by norm_num
private theorem prime_fiftySixBB_977 : Nat.Prime 977 := by norm_num
private theorem prime_fiftySixBB_983 : Nat.Prime 983 := by norm_num
private theorem prime_fiftySixBB_1087 : Nat.Prime 1087 := by norm_num
private theorem prime_fiftySixBB_1091 : Nat.Prime 1091 := by norm_num
private theorem prime_fiftySixBB_1123 : Nat.Prime 1123 := by norm_num
private theorem prime_fiftySixBB_1193 : Nat.Prime 1193 := by norm_num
private theorem prime_fiftySixBB_1201 : Nat.Prime 1201 := by norm_num
private theorem prime_fiftySixBB_1223 : Nat.Prime 1223 := by norm_num
private theorem prime_fiftySixBB_1237 : Nat.Prime 1237 := by norm_num
private theorem prime_fiftySixBB_1259 : Nat.Prime 1259 := by norm_num
private theorem prime_fiftySixBB_1279 : Nat.Prime 1279 := by norm_num
private theorem prime_fiftySixBB_1373 : Nat.Prime 1373 := by norm_num
private theorem prime_fiftySixBB_1399 : Nat.Prime 1399 := by norm_num
private theorem prime_fiftySixBB_1429 : Nat.Prime 1429 := by norm_num
private theorem prime_fiftySixBB_1453 : Nat.Prime 1453 := by norm_num
private theorem prime_fiftySixBB_1459 : Nat.Prime 1459 := by norm_num
private theorem prime_fiftySixBB_1483 : Nat.Prime 1483 := by norm_num
private theorem prime_fiftySixBB_1493 : Nat.Prime 1493 := by norm_num
private theorem prime_fiftySixBB_1499 : Nat.Prime 1499 := by norm_num
private theorem prime_fiftySixBB_1619 : Nat.Prime 1619 := by norm_num
private theorem prime_fiftySixBB_1669 : Nat.Prime 1669 := by norm_num
private theorem prime_fiftySixBB_1733 : Nat.Prime 1733 := by norm_num
private theorem prime_fiftySixBB_1753 : Nat.Prime 1753 := by norm_num
private theorem prime_fiftySixBB_1789 : Nat.Prime 1789 := by norm_num
private theorem prime_fiftySixBB_1861 : Nat.Prime 1861 := by norm_num
private theorem prime_fiftySixBB_1879 : Nat.Prime 1879 := by norm_num
private theorem prime_fiftySixBB_1949 : Nat.Prime 1949 := by norm_num
private theorem prime_fiftySixBB_1951 : Nat.Prime 1951 := by norm_num
private theorem prime_fiftySixBB_1979 : Nat.Prime 1979 := by norm_num
private theorem prime_fiftySixBB_2017 : Nat.Prime 2017 := by norm_num
private theorem prime_fiftySixBB_2029 : Nat.Prime 2029 := by norm_num
private theorem prime_fiftySixBB_2081 : Nat.Prime 2081 := by norm_num
private theorem prime_fiftySixBB_2141 : Nat.Prime 2141 := by norm_num
private theorem prime_fiftySixBB_2143 : Nat.Prime 2143 := by norm_num
private theorem prime_fiftySixBB_2269 : Nat.Prime 2269 := by norm_num
private theorem prime_fiftySixBB_2341 : Nat.Prime 2341 := by norm_num
private theorem prime_fiftySixBB_2381 : Nat.Prime 2381 := by norm_num
private theorem prime_fiftySixBB_2447 : Nat.Prime 2447 := by norm_num
private theorem prime_fiftySixBB_2593 : Nat.Prime 2593 := by norm_num
private theorem prime_fiftySixBB_2659 : Nat.Prime 2659 := by norm_num
private theorem prime_fiftySixBB_2677 : Nat.Prime 2677 := by norm_num
private theorem prime_fiftySixBB_2731 : Nat.Prime 2731 := by norm_num
private theorem prime_fiftySixBB_2753 : Nat.Prime 2753 := by norm_num
private theorem prime_fiftySixBB_2803 : Nat.Prime 2803 := by norm_num
private theorem prime_fiftySixBB_2819 : Nat.Prime 2819 := by norm_num
private theorem prime_fiftySixBB_2843 : Nat.Prime 2843 := by norm_num
private theorem prime_fiftySixBB_2879 : Nat.Prime 2879 := by norm_num
private theorem prime_fiftySixBB_2917 : Nat.Prime 2917 := by norm_num
private theorem prime_fiftySixBB_2927 : Nat.Prime 2927 := by norm_num
private theorem prime_fiftySixBB_2957 : Nat.Prime 2957 := by norm_num
private theorem prime_fiftySixBB_2969 : Nat.Prime 2969 := by norm_num
private theorem prime_fiftySixBB_3023 : Nat.Prime 3023 := by norm_num
private theorem prime_fiftySixBB_3137 : Nat.Prime 3137 := by norm_num
private theorem prime_fiftySixBB_3347 : Nat.Prime 3347 := by norm_num
private theorem prime_fiftySixBB_3463 : Nat.Prime 3463 := by norm_num
private theorem prime_fiftySixBB_3527 : Nat.Prime 3527 := by norm_num
private theorem prime_fiftySixBB_3533 : Nat.Prime 3533 := by norm_num
private theorem prime_fiftySixBB_3541 : Nat.Prime 3541 := by norm_num
private theorem prime_fiftySixBB_3733 : Nat.Prime 3733 := by norm_num
private theorem prime_fiftySixBB_3847 : Nat.Prime 3847 := by norm_num
private theorem prime_fiftySixBB_3853 : Nat.Prime 3853 := by norm_num
private theorem prime_fiftySixBB_4127 : Nat.Prime 4127 := by norm_num
private theorem prime_fiftySixBB_4133 : Nat.Prime 4133 := by norm_num
private theorem prime_fiftySixBB_4153 : Nat.Prime 4153 := by norm_num
private theorem prime_fiftySixBB_4229 : Nat.Prime 4229 := by norm_num
private theorem prime_fiftySixBB_4259 : Nat.Prime 4259 := by norm_num
private theorem prime_fiftySixBB_4327 : Nat.Prime 4327 := by norm_num
private theorem prime_fiftySixBB_4457 : Nat.Prime 4457 := by norm_num
private theorem prime_fiftySixBB_4597 : Nat.Prime 4597 := by norm_num
private theorem prime_fiftySixBB_4603 : Nat.Prime 4603 := by norm_num
private theorem prime_fiftySixBB_4637 : Nat.Prime 4637 := by norm_num
private theorem prime_fiftySixBB_4889 : Nat.Prime 4889 := by norm_num
private theorem prime_fiftySixBB_4993 : Nat.Prime 4993 := by norm_num
private theorem prime_fiftySixBB_5009 : Nat.Prime 5009 := by norm_num
private theorem prime_fiftySixBB_5021 : Nat.Prime 5021 := by norm_num
private theorem prime_fiftySixBB_5051 : Nat.Prime 5051 := by norm_num
private theorem prime_fiftySixBB_5077 : Nat.Prime 5077 := by norm_num
private theorem prime_fiftySixBB_5347 : Nat.Prime 5347 := by norm_num
private theorem prime_fiftySixBB_5479 : Nat.Prime 5479 := by norm_num
private theorem prime_fiftySixBB_5503 : Nat.Prime 5503 := by norm_num
private theorem prime_fiftySixBB_5563 : Nat.Prime 5563 := by norm_num
private theorem prime_fiftySixBB_5693 : Nat.Prime 5693 := by norm_num
private theorem prime_fiftySixBB_5779 : Nat.Prime 5779 := by norm_num
private theorem prime_fiftySixBB_5849 : Nat.Prime 5849 := by norm_num
private theorem prime_fiftySixBB_6151 : Nat.Prime 6151 := by norm_num
private theorem prime_fiftySixBB_6361 : Nat.Prime 6361 := by norm_num
private theorem prime_fiftySixBB_6367 : Nat.Prime 6367 := by norm_num
private theorem prime_fiftySixBB_6673 : Nat.Prime 6673 := by norm_num
private theorem prime_fiftySixBB_6991 : Nat.Prime 6991 := by norm_num
private theorem prime_fiftySixBB_7121 : Nat.Prime 7121 := by norm_num
private theorem prime_fiftySixBB_7603 : Nat.Prime 7603 := by norm_num
private theorem prime_fiftySixBB_7949 : Nat.Prime 7949 := by norm_num
private theorem prime_fiftySixBB_7951 : Nat.Prime 7951 := by norm_num
private theorem prime_fiftySixBB_8179 : Nat.Prime 8179 := by norm_num
private theorem prime_fiftySixBB_8543 : Nat.Prime 8543 := by norm_num
private theorem prime_fiftySixBB_8629 : Nat.Prime 8629 := by norm_num
private theorem prime_fiftySixBB_8741 : Nat.Prime 8741 := by norm_num
private theorem prime_fiftySixBB_9059 : Nat.Prime 9059 := by norm_num
private theorem prime_fiftySixBB_9133 : Nat.Prime 9133 := by norm_num
private theorem prime_fiftySixBB_9151 : Nat.Prime 9151 := by norm_num
private theorem prime_fiftySixBB_9349 : Nat.Prime 9349 := by norm_num
private theorem prime_fiftySixBB_9413 : Nat.Prime 9413 := by norm_num
private theorem prime_fiftySixBB_9859 : Nat.Prime 9859 := by norm_num
private theorem prime_fiftySixBB_10289 : Nat.Prime 10289 := by norm_num
private theorem prime_fiftySixBB_10331 : Nat.Prime 10331 := by norm_num
private theorem prime_fiftySixBB_10487 : Nat.Prime 10487 := by norm_num
private theorem prime_fiftySixBB_10789 : Nat.Prime 10789 := by norm_num
private theorem prime_fiftySixBB_11243 : Nat.Prime 11243 := by norm_num
private theorem prime_fiftySixBB_12583 : Nat.Prime 12583 := by norm_num
private theorem prime_fiftySixBB_13103 : Nat.Prime 13103 := by norm_num
private theorem prime_fiftySixBB_13163 : Nat.Prime 13163 := by norm_num
private theorem prime_fiftySixBB_13463 : Nat.Prime 13463 := by norm_num
private theorem prime_fiftySixBB_13711 : Nat.Prime 13711 := by norm_num
private theorem prime_fiftySixBB_13901 : Nat.Prime 13901 := by norm_num
private theorem prime_fiftySixBB_14033 : Nat.Prime 14033 := by norm_num
private theorem prime_fiftySixBB_14401 : Nat.Prime 14401 := by norm_num
private theorem prime_fiftySixBB_14449 : Nat.Prime 14449 := by norm_num
private theorem prime_fiftySixBB_14827 : Nat.Prime 14827 := by norm_num
private theorem prime_fiftySixBB_14887 : Nat.Prime 14887 := by norm_num
private theorem prime_fiftySixBB_15031 : Nat.Prime 15031 := by norm_num
private theorem prime_fiftySixBB_15299 : Nat.Prime 15299 := by norm_num
private theorem prime_fiftySixBB_15661 : Nat.Prime 15661 := by norm_num
private theorem prime_fiftySixBB_15797 : Nat.Prime 15797 := by norm_num
private theorem prime_fiftySixBB_16421 : Nat.Prime 16421 := by norm_num
private theorem prime_fiftySixBB_16811 : Nat.Prime 16811 := by norm_num
private theorem prime_fiftySixBB_18199 : Nat.Prime 18199 := by norm_num
private theorem prime_fiftySixBB_18307 : Nat.Prime 18307 := by norm_num
private theorem prime_fiftySixBB_18313 : Nat.Prime 18313 := by norm_num
private theorem prime_fiftySixBB_18661 : Nat.Prime 18661 := by norm_num
private theorem prime_fiftySixBB_19087 : Nat.Prime 19087 := by norm_num
private theorem prime_fiftySixBB_19387 : Nat.Prime 19387 := by norm_num
private theorem prime_fiftySixBB_20521 : Nat.Prime 20521 := by norm_num
private theorem prime_fiftySixBB_21061 : Nat.Prime 21061 := by norm_num
private theorem prime_fiftySixBB_21589 : Nat.Prime 21589 := by norm_num
private theorem prime_fiftySixBB_22973 : Nat.Prime 22973 := by norm_num
private theorem prime_fiftySixBB_23027 : Nat.Prime 23027 := by norm_num
private theorem prime_fiftySixBB_23743 : Nat.Prime 23743 := by norm_num
private theorem prime_fiftySixBB_23789 : Nat.Prime 23789 := by norm_num
private theorem prime_fiftySixBB_24799 : Nat.Prime 24799 := by norm_num
private theorem prime_fiftySixBB_25037 : Nat.Prime 25037 := by norm_num
private theorem prime_fiftySixBB_25589 : Nat.Prime 25589 := by norm_num
private theorem prime_fiftySixBB_26189 : Nat.Prime 26189 := by norm_num
private theorem prime_fiftySixBB_26357 : Nat.Prime 26357 := by norm_num
private theorem prime_fiftySixBB_26947 : Nat.Prime 26947 := by norm_num
private theorem prime_fiftySixBB_27457 : Nat.Prime 27457 := by norm_num
private theorem prime_fiftySixBB_27763 : Nat.Prime 27763 := by norm_num
private theorem prime_fiftySixBB_28403 : Nat.Prime 28403 := by norm_num
private theorem prime_fiftySixBB_28591 : Nat.Prime 28591 := by norm_num
private theorem prime_fiftySixBB_29363 : Nat.Prime 29363 := by norm_num
private theorem prime_fiftySixBB_30881 : Nat.Prime 30881 := by norm_num
private theorem prime_fiftySixBB_31657 : Nat.Prime 31657 := by norm_num
private theorem prime_fiftySixBB_33113 : Nat.Prime 33113 := by norm_num
private theorem prime_fiftySixBB_33679 : Nat.Prime 33679 := by norm_num
private theorem prime_fiftySixBB_37409 : Nat.Prime 37409 := by norm_num
private theorem prime_fiftySixBB_38167 : Nat.Prime 38167 := by norm_num
private theorem prime_fiftySixBB_38707 : Nat.Prime 38707 := by norm_num
private theorem prime_fiftySixBB_38903 : Nat.Prime 38903 := by norm_num
private theorem prime_fiftySixBB_39367 : Nat.Prime 39367 := by norm_num
private theorem prime_fiftySixBB_41957 : Nat.Prime 41957 := by norm_num
private theorem prime_fiftySixBB_43399 : Nat.Prime 43399 := by norm_num
private theorem prime_fiftySixBB_46817 : Nat.Prime 46817 := by norm_num
private theorem prime_fiftySixBB_46933 : Nat.Prime 46933 := by norm_num
private theorem prime_fiftySixBB_49339 : Nat.Prime 49339 := by norm_num
private theorem prime_fiftySixBB_49877 : Nat.Prime 49877 := by norm_num
private theorem prime_fiftySixBB_50177 : Nat.Prime 50177 := by norm_num
private theorem prime_fiftySixBB_51203 : Nat.Prime 51203 := by norm_num
private theorem prime_fiftySixBB_56101 : Nat.Prime 56101 := by norm_num
private theorem prime_fiftySixBB_57077 : Nat.Prime 57077 := by norm_num
private theorem prime_fiftySixBB_58543 : Nat.Prime 58543 := by norm_num
private theorem prime_fiftySixBB_61027 : Nat.Prime 61027 := by norm_num
private theorem prime_fiftySixBB_61057 : Nat.Prime 61057 := by norm_num
private theorem prime_fiftySixBB_63599 : Nat.Prime 63599 := by norm_num
private theorem prime_fiftySixBB_64081 : Nat.Prime 64081 := by norm_num
private theorem prime_fiftySixBB_65543 : Nat.Prime 65543 := by norm_num
private theorem prime_fiftySixBB_65713 : Nat.Prime 65713 := by norm_num
private theorem prime_fiftySixBB_70529 : Nat.Prime 70529 := by norm_num
private theorem prime_fiftySixBB_71023 : Nat.Prime 71023 := by norm_num
private theorem prime_fiftySixBB_71089 : Nat.Prime 71089 := by norm_num
private theorem prime_fiftySixBB_71789 : Nat.Prime 71789 := by norm_num
private theorem prime_fiftySixBB_72421 : Nat.Prime 72421 := by norm_num
private theorem prime_fiftySixBB_72997 : Nat.Prime 72997 := by norm_num
private theorem prime_fiftySixBB_75781 : Nat.Prime 75781 := by norm_num
private theorem prime_fiftySixBB_76919 : Nat.Prime 76919 := by norm_num
private theorem prime_fiftySixBB_78277 : Nat.Prime 78277 := by norm_num
private theorem prime_fiftySixBB_80471 : Nat.Prime 80471 := by norm_num
private theorem prime_fiftySixBB_82499 : Nat.Prime 82499 := by norm_num
private theorem prime_fiftySixBB_86257 : Nat.Prime 86257 := by norm_num
private theorem prime_fiftySixBB_86599 : Nat.Prime 86599 := by norm_num
private theorem prime_fiftySixBB_89329 : Nat.Prime 89329 := by norm_num
private theorem prime_fiftySixBB_89491 : Nat.Prime 89491 := by norm_num
private theorem prime_fiftySixBB_108041 : Nat.Prime 108041 := by norm_num
private theorem prime_fiftySixBB_116107 : Nat.Prime 116107 := by norm_num
private theorem prime_fiftySixBB_120077 : Nat.Prime 120077 := by norm_num
private theorem prime_fiftySixBB_125399 : Nat.Prime 125399 := by norm_num
private theorem prime_fiftySixBB_126517 : Nat.Prime 126517 := by norm_num
private theorem prime_fiftySixBB_127843 : Nat.Prime 127843 := by norm_num
private theorem prime_fiftySixBB_128873 : Nat.Prime 128873 := by norm_num
private theorem prime_fiftySixBB_129127 : Nat.Prime 129127 := by norm_num
private theorem prime_fiftySixBB_130657 : Nat.Prime 130657 := by norm_num
private theorem prime_fiftySixBB_145679 : Nat.Prime 145679 := by norm_num
private theorem prime_fiftySixBB_146521 : Nat.Prime 146521 := by norm_num
private theorem prime_fiftySixBB_148403 : Nat.Prime 148403 := by norm_num
private theorem prime_fiftySixBB_152239 : Nat.Prime 152239 := by norm_num
private theorem prime_fiftySixBB_174673 : Nat.Prime 174673 := by norm_num
private theorem prime_fiftySixBB_176611 : Nat.Prime 176611 := by norm_num
private theorem prime_fiftySixBB_188351 : Nat.Prime 188351 := by norm_num
private theorem prime_fiftySixBB_194827 : Nat.Prime 194827 := by norm_num
private theorem prime_fiftySixBB_202823 : Nat.Prime 202823 := by norm_num
private theorem prime_fiftySixBB_209449 : Nat.Prime 209449 := by norm_num
private theorem prime_fiftySixBB_210247 : Nat.Prime 210247 := by norm_num
private theorem prime_fiftySixBB_214147 : Nat.Prime 214147 := by norm_num
private theorem prime_fiftySixBB_216071 : Nat.Prime 216071 := by norm_num
private theorem prime_fiftySixBB_221567 : Nat.Prime 221567 := by norm_num
private theorem prime_fiftySixBB_228479 : Nat.Prime 228479 := by norm_num
private theorem prime_fiftySixBB_232363 : Nat.Prime 232363 := by norm_num
private theorem prime_fiftySixBB_250963 : Nat.Prime 250963 := by norm_num
private theorem prime_fiftySixBB_252727 : Nat.Prime 252727 := by norm_num
private theorem prime_fiftySixBB_259379 : Nat.Prime 259379 := by norm_num
private theorem prime_fiftySixBB_259451 : Nat.Prime 259451 := by norm_num
private theorem prime_fiftySixBB_260329 : Nat.Prime 260329 := by norm_num
private theorem prime_fiftySixBB_260453 : Nat.Prime 260453 := by norm_num
private theorem prime_fiftySixBB_261281 : Nat.Prime 261281 := by norm_num
private theorem prime_fiftySixBB_265459 : Nat.Prime 265459 := by norm_num
private theorem prime_fiftySixBB_283463 : Nat.Prime 283463 := by norm_num
private theorem prime_fiftySixBB_284747 : Nat.Prime 284747 := by norm_num
private theorem prime_fiftySixBB_304439 : Nat.Prime 304439 := by norm_num
private theorem prime_fiftySixBB_315521 : Nat.Prime 315521 := by norm_num
private theorem prime_fiftySixBB_317987 : Nat.Prime 317987 := by norm_num
private theorem prime_fiftySixBB_327337 : Nat.Prime 327337 := by norm_num
private theorem prime_fiftySixBB_330679 : Nat.Prime 330679 := by norm_num
private theorem prime_fiftySixBB_340129 : Nat.Prime 340129 := by norm_num
private theorem prime_fiftySixBB_357661 : Nat.Prime 357661 := by norm_num
private theorem prime_fiftySixBB_359389 : Nat.Prime 359389 := by norm_num
private theorem prime_fiftySixBB_362429 : Nat.Prime 362429 := by norm_num
private theorem prime_fiftySixBB_363947 : Nat.Prime 363947 := by norm_num
private theorem prime_fiftySixBB_365983 : Nat.Prime 365983 := by norm_num
private theorem prime_fiftySixBB_367781 : Nat.Prime 367781 := by norm_num
private theorem prime_fiftySixBB_417581 : Nat.Prime 417581 := by norm_num
private theorem prime_fiftySixBB_420757 : Nat.Prime 420757 := by norm_num
private theorem prime_fiftySixBB_421469 : Nat.Prime 421469 := by norm_num
private theorem prime_fiftySixBB_448321 : Nat.Prime 448321 := by norm_num
private theorem prime_fiftySixBB_454507 : Nat.Prime 454507 := by norm_num
private theorem prime_fiftySixBB_455381 : Nat.Prime 455381 := by norm_num
private theorem prime_fiftySixBB_467417 : Nat.Prime 467417 := by norm_num
private theorem prime_fiftySixBB_478243 : Nat.Prime 478243 := by norm_num
private theorem prime_fiftySixBB_525869 : Nat.Prime 525869 := by norm_num
private theorem prime_fiftySixBB_542923 : Nat.Prime 542923 := by norm_num
private theorem prime_fiftySixBB_571657 : Nat.Prime 571657 := by norm_num
private theorem prime_fiftySixBB_581687 : Nat.Prime 581687 := by norm_num
private theorem prime_fiftySixBB_585251 : Nat.Prime 585251 := by norm_num
private theorem prime_fiftySixBB_641239 : Nat.Prime 641239 := by norm_num
private theorem prime_fiftySixBB_672521 : Nat.Prime 672521 := by norm_num
private theorem prime_fiftySixBB_699817 : Nat.Prime 699817 := by norm_num
private theorem prime_fiftySixBB_708109 : Nat.Prime 708109 := by norm_num
private theorem prime_fiftySixBB_787217 : Nat.Prime 787217 := by norm_num
private theorem prime_fiftySixBB_858457 : Nat.Prime 858457 := by norm_num
private theorem prime_fiftySixBB_869689 : Nat.Prime 869689 := by norm_num
private theorem prime_fiftySixBB_877397 : Nat.Prime 877397 := by norm_num
private theorem prime_fiftySixBB_880199 : Nat.Prime 880199 := by norm_num
private theorem prime_fiftySixBB_884029 : Nat.Prime 884029 := by norm_num
private theorem prime_fiftySixBB_920279 : Nat.Prime 920279 := by norm_num
private theorem prime_fiftySixBB_930301 : Nat.Prime 930301 := by norm_num
private theorem prime_fiftySixBB_972029 : Nat.Prime 972029 := by norm_num
private theorem prime_fiftySixBB_1048447 : Nat.Prime 1048447 := by norm_num
private theorem prime_fiftySixBB_1096061 : Nat.Prime 1096061 := by norm_num
private theorem prime_fiftySixBB_1155703 : Nat.Prime 1155703 := by norm_num
private theorem prime_fiftySixBB_1186657 : Nat.Prime 1186657 := by norm_num
private theorem prime_fiftySixBB_1193161 : Nat.Prime 1193161 := by norm_num
private theorem prime_fiftySixBB_1228099 : Nat.Prime 1228099 := by norm_num
private theorem prime_fiftySixBB_1231481 : Nat.Prime 1231481 := by norm_num
private theorem prime_fiftySixBB_1319167 : Nat.Prime 1319167 := by norm_num
private theorem prime_fiftySixBB_1326889 : Nat.Prime 1326889 := by norm_num
private theorem prime_fiftySixBB_1384601 : Nat.Prime 1384601 := by norm_num
private theorem prime_fiftySixBB_1445929 : Nat.Prime 1445929 := by norm_num
private theorem prime_fiftySixBB_1448411 : Nat.Prime 1448411 := by norm_num
private theorem prime_fiftySixBB_1715849 : Nat.Prime 1715849 := by norm_num
private theorem prime_fiftySixBB_2074421 : Nat.Prime 2074421 := by norm_num
private theorem prime_fiftySixBB_2110133 : Nat.Prime 2110133 := by norm_num
private theorem prime_fiftySixBB_2156087 : Nat.Prime 2156087 := by norm_num
private theorem prime_fiftySixBB_2170603 : Nat.Prime 2170603 := by norm_num
private theorem prime_fiftySixBB_2400031 : Nat.Prime 2400031 := by norm_num
private theorem prime_fiftySixBB_2546671 : Nat.Prime 2546671 := by norm_num
private theorem prime_fiftySixBB_2570849 : Nat.Prime 2570849 := by norm_num
private theorem prime_fiftySixBB_2713457 : Nat.Prime 2713457 := by norm_num
private theorem prime_fiftySixBB_2766677 : Nat.Prime 2766677 := by norm_num
private theorem prime_fiftySixBB_2866901 : Nat.Prime 2866901 := by norm_num
private theorem prime_fiftySixBB_3470713 : Nat.Prime 3470713 := by norm_num
private theorem prime_fiftySixBB_3621353 : Nat.Prime 3621353 := by norm_num
private theorem prime_fiftySixBB_3705193 : Nat.Prime 3705193 := by norm_num
private theorem prime_fiftySixBB_3888851 : Nat.Prime 3888851 := by norm_num
private theorem prime_fiftySixBB_4404193 : Nat.Prime 4404193 := by norm_num
private theorem prime_fiftySixBB_4644971 : Nat.Prime 4644971 := by norm_num
private theorem prime_fiftySixBB_4938707 : Nat.Prime 4938707 := by norm_num
private theorem prime_fiftySixBB_4967827 : Nat.Prime 4967827 := by norm_num
private theorem prime_fiftySixBB_4988713 : Nat.Prime 4988713 := by norm_num
private theorem prime_fiftySixBB_5050261 : Nat.Prime 5050261 := by norm_num
private theorem prime_fiftySixBB_5138383 : Nat.Prime 5138383 := by norm_num
private theorem prime_fiftySixBB_6007609 : Nat.Prime 6007609 := by norm_num
private theorem prime_fiftySixBB_6290761 : Nat.Prime 6290761 := by norm_num
private theorem prime_fiftySixBB_6593009 : Nat.Prime 6593009 := by norm_num
private theorem prime_fiftySixBB_6627001 : Nat.Prime 6627001 := by norm_num
private theorem prime_fiftySixBB_6837773 : Nat.Prime 6837773 := by norm_num
private theorem prime_fiftySixBB_6963611 : Nat.Prime 6963611 := by norm_num
private theorem prime_fiftySixBB_6989579 : Nat.Prime 6989579 := by norm_num
private theorem prime_fiftySixBB_7298069 : Nat.Prime 7298069 := by norm_num
private theorem prime_fiftySixBB_7426669 : Nat.Prime 7426669 := by norm_num
private theorem prime_fiftySixBB_7905089 : Nat.Prime 7905089 := by norm_num
private theorem prime_fiftySixBB_8106871 : Nat.Prime 8106871 := by norm_num
private theorem prime_fiftySixBB_8264713 : Nat.Prime 8264713 := by norm_num
private theorem prime_fiftySixBB_8987357 : Nat.Prime 8987357 := by norm_num
private theorem prime_fiftySixBB_10496503 : Nat.Prime 10496503 := by norm_num
private theorem prime_fiftySixBB_11037937 : Nat.Prime 11037937 := by norm_num
private theorem prime_fiftySixBB_11166629 : Nat.Prime 11166629 := by norm_num
private theorem prime_fiftySixBB_11572507 : Nat.Prime 11572507 := by norm_num
private theorem prime_fiftySixBB_11861749 : Nat.Prime 11861749 := by norm_num
private theorem prime_fiftySixBB_12027451 : Nat.Prime 12027451 := by norm_num
private theorem prime_fiftySixBB_12301369 : Nat.Prime 12301369 := by norm_num
private theorem prime_fiftySixBB_12918757 : Nat.Prime 12918757 := by norm_num
private theorem prime_fiftySixBB_13256371 : Nat.Prime 13256371 := by norm_num
private theorem prime_fiftySixBB_13989383 : Nat.Prime 13989383 := by norm_num
private theorem prime_fiftySixBB_15973147 : Nat.Prime 15973147 := by norm_num
private theorem prime_fiftySixBB_20852509 : Nat.Prime 20852509 := by norm_num
private theorem prime_fiftySixBB_21287767 : Nat.Prime 21287767 := by norm_num
private theorem prime_fiftySixBB_22042687 : Nat.Prime 22042687 := by norm_num
private theorem prime_fiftySixBB_22138973 : Nat.Prime 22138973 := by norm_num
private theorem prime_fiftySixBB_23474863 : Nat.Prime 23474863 := by norm_num
private theorem prime_fiftySixBB_24218543 : Nat.Prime 24218543 := by norm_num
private theorem prime_fiftySixBB_24606013 : Nat.Prime 24606013 := by norm_num
private theorem prime_fiftySixBB_24934747 : Nat.Prime 24934747 := by norm_num
private theorem prime_fiftySixBB_25157753 : Nat.Prime 25157753 := by norm_num
private theorem prime_fiftySixBB_27031369 : Nat.Prime 27031369 := by norm_num
private theorem prime_fiftySixBB_27036833 : Nat.Prime 27036833 := by norm_num
private theorem prime_fiftySixBB_28180973 : Nat.Prime 28180973 := by norm_num
private theorem prime_fiftySixBB_28213219 : Nat.Prime 28213219 := by norm_num
private theorem prime_fiftySixBB_28358779 : Nat.Prime 28358779 := by norm_num
private theorem prime_fiftySixBB_28709383 : Nat.Prime 28709383 := by norm_num
private theorem prime_fiftySixBB_28835819 : Nat.Prime 28835819 := by norm_num
private theorem prime_fiftySixBB_32646343 : Nat.Prime 32646343 := by
  apply lucas_primality 32646343 (3 : ZMod 32646343)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (107, 1), (211, 1), (241, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (107, 1), (211, 1), (241, 1)] : List FactorBlock).map factorBlockValue).prod) = 32646343 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_107
      · exact prime_fiftySixBB_211
      · exact prime_fiftySixBB_241
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 32646343) ^ 16323171 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 32646343) ^ 10882114 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 32646343) ^ 305106 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 32646343) ^ 154722 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 32646343) ^ 135462 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_38114539 : Nat.Prime 38114539 := by
  apply lucas_primality 38114539 (3 : ZMod 38114539)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (11, 1), (82499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (11, 1), (82499, 1)] : List FactorBlock).map factorBlockValue).prod) = 38114539 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_7
      · exact prime_fiftySixBB_11
      · exact prime_fiftySixBB_82499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 38114539) ^ 19057269 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 38114539) ^ 12704846 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 38114539) ^ 5444934 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 38114539) ^ 3464958 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 38114539) ^ 462 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_40746703 : Nat.Prime 40746703 := by
  apply lucas_primality 40746703 (6 : ZMod 40746703)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (41, 1), (73, 1), (2269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (41, 1), (73, 1), (2269, 1)] : List FactorBlock).map factorBlockValue).prod) = 40746703 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_41
      · exact prime_fiftySixBB_73
      · exact prime_fiftySixBB_2269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 40746703) ^ 20373351 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (6 : ZMod 40746703) ^ 13582234 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (6 : ZMod 40746703) ^ 993822 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (6 : ZMod 40746703) ^ 558174 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (6 : ZMod 40746703) ^ 17958 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_41781667 : Nat.Prime 41781667 := by
  apply lucas_primality 41781667 (7 : ZMod 41781667)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (6963611, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (6963611, 1)] : List FactorBlock).map factorBlockValue).prod) = 41781667 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_6963611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 41781667) ^ 20890833 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 41781667) ^ 13927222 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 41781667) ^ 6 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_43940531 : Nat.Prime 43940531 := by
  apply lucas_primality 43940531 (2 : ZMod 43940531)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (419, 1), (10487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (419, 1), (10487, 1)] : List FactorBlock).map factorBlockValue).prod) = 43940531 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_5
      · exact prime_fiftySixBB_419
      · exact prime_fiftySixBB_10487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 43940531) ^ 21970265 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 43940531) ^ 8788106 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 43940531) ^ 104870 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 43940531) ^ 4190 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_45551269 : Nat.Prime 45551269 := by
  apply lucas_primality 45551269 (2 : ZMod 45551269)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (7, 1), (89, 1), (677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (7, 1), (89, 1), (677, 1)] : List FactorBlock).map factorBlockValue).prod) = 45551269 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_7
      · exact prime_fiftySixBB_89
      · exact prime_fiftySixBB_677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 45551269) ^ 22775634 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 45551269) ^ 15183756 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 45551269) ^ 6507324 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 45551269) ^ 511812 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 45551269) ^ 67284 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_52181341 : Nat.Prime 52181341 := by
  apply lucas_primality 52181341 (6 : ZMod 52181341)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (869689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (869689, 1)] : List FactorBlock).map factorBlockValue).prod) = 52181341 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_5
      · exact prime_fiftySixBB_869689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 52181341) ^ 26090670 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (6 : ZMod 52181341) ^ 17393780 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (6 : ZMod 52181341) ^ 10436268 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (6 : ZMod 52181341) ^ 60 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_52659163 : Nat.Prime 52659163 := by
  apply lucas_primality 52659163 (2 : ZMod 52659163)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (103, 1), (28403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (103, 1), (28403, 1)] : List FactorBlock).map factorBlockValue).prod) = 52659163 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_103
      · exact prime_fiftySixBB_28403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 52659163) ^ 26329581 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 52659163) ^ 17553054 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 52659163) ^ 511254 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 52659163) ^ 1854 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_52744073 : Nat.Prime 52744073 := by
  apply lucas_primality 52744073 (3 : ZMod 52744073)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (6593009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (6593009, 1)] : List FactorBlock).map factorBlockValue).prod) = 52744073 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_6593009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 52744073) ^ 26372036 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 52744073) ^ 8 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_53744533 : Nat.Prime 53744533 := by
  apply lucas_primality 53744533 (5 : ZMod 53744533)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (311, 1), (14401, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (311, 1), (14401, 1)] : List FactorBlock).map factorBlockValue).prod) = 53744533 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_311
      · exact prime_fiftySixBB_14401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 53744533) ^ 26872266 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 53744533) ^ 17914844 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 53744533) ^ 172812 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 53744533) ^ 3732 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_62432077 : Nat.Prime 62432077 := by
  apply lucas_primality 62432077 (22 : ZMod 62432077)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 2), (89, 1), (1193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 2), (89, 1), (1193, 1)] : List FactorBlock).map factorBlockValue).prod) = 62432077 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_7
      · exact prime_fiftySixBB_89
      · exact prime_fiftySixBB_1193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (22 : ZMod 62432077) ^ 31216038 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (22 : ZMod 62432077) ^ 20810692 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (22 : ZMod 62432077) ^ 8918868 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (22 : ZMod 62432077) ^ 701484 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (22 : ZMod 62432077) ^ 52332 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_65702803 : Nat.Prime 65702803 := by
  apply lucas_primality 65702803 (2 : ZMod 65702803)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (109, 1), (9133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (109, 1), (9133, 1)] : List FactorBlock).map factorBlockValue).prod) = 65702803 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_11
      · exact prime_fiftySixBB_109
      · exact prime_fiftySixBB_9133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 65702803) ^ 32851401 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 65702803) ^ 21900934 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 65702803) ^ 5972982 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 65702803) ^ 602778 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 65702803) ^ 7194 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_66253633 : Nat.Prime 66253633 := by
  apply lucas_primality 66253633 (7 : ZMod 66253633)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (29, 1), (73, 1), (163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (29, 1), (73, 1), (163, 1)] : List FactorBlock).map factorBlockValue).prod) = 66253633 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_29
      · exact prime_fiftySixBB_73
      · exact prime_fiftySixBB_163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 66253633) ^ 33126816 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 66253633) ^ 22084544 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 66253633) ^ 2284608 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 66253633) ^ 907584 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 66253633) ^ 406464 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_66838843 : Nat.Prime 66838843 := by
  apply lucas_primality 66838843 (2 : ZMod 66838843)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 2), (75781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 2), (75781, 1)] : List FactorBlock).map factorBlockValue).prod) = 66838843 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_7
      · exact prime_fiftySixBB_75781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 66838843) ^ 33419421 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 66838843) ^ 22279614 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 66838843) ^ 9548406 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 66838843) ^ 882 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_67235899 : Nat.Prime 67235899 := by
  apply lucas_primality 67235899 (2 : ZMod 67235899)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1237, 1), (9059, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1237, 1), (9059, 1)] : List FactorBlock).map factorBlockValue).prod) = 67235899 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_1237
      · exact prime_fiftySixBB_9059
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 67235899) ^ 33617949 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 67235899) ^ 22411966 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 67235899) ^ 54354 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 67235899) ^ 7422 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_73424423 : Nat.Prime 73424423 := by
  apply lucas_primality 73424423 (5 : ZMod 73424423)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (73, 1), (631, 1), (797, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (73, 1), (631, 1), (797, 1)] : List FactorBlock).map factorBlockValue).prod) = 73424423 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_73
      · exact prime_fiftySixBB_631
      · exact prime_fiftySixBB_797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 73424423) ^ 36712211 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 73424423) ^ 1005814 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 73424423) ^ 116362 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 73424423) ^ 92126 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_78023597 : Nat.Prime 78023597 := by
  apply lucas_primality 78023597 (2 : ZMod 78023597)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (1483, 1), (1879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (1483, 1), (1879, 1)] : List FactorBlock).map factorBlockValue).prod) = 78023597 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_7
      · exact prime_fiftySixBB_1483
      · exact prime_fiftySixBB_1879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 78023597) ^ 39011798 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 78023597) ^ 11146228 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 78023597) ^ 52612 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 78023597) ^ 41524 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_79515047 : Nat.Prime 79515047 := by
  apply lucas_primality 79515047 (5 : ZMod 79515047)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (167, 1), (18313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (167, 1), (18313, 1)] : List FactorBlock).map factorBlockValue).prod) = 79515047 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_13
      · exact prime_fiftySixBB_167
      · exact prime_fiftySixBB_18313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 79515047) ^ 39757523 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 79515047) ^ 6116542 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 79515047) ^ 476138 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 79515047) ^ 4342 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_92899421 : Nat.Prime 92899421 := by
  apply lucas_primality 92899421 (2 : ZMod 92899421)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (4644971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (4644971, 1)] : List FactorBlock).map factorBlockValue).prod) = 92899421 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_5
      · exact prime_fiftySixBB_4644971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 92899421) ^ 46449710 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 92899421) ^ 18579884 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 92899421) ^ 20 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_93899453 : Nat.Prime 93899453 := by
  apply lucas_primality 93899453 (2 : ZMod 93899453)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23474863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23474863, 1)] : List FactorBlock).map factorBlockValue).prod) = 93899453 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_23474863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 93899453) ^ 46949726 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 93899453) ^ 4 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_96200113 : Nat.Prime 96200113 := by
  apply lucas_primality 96200113 (5 : ZMod 96200113)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (131, 1), (15299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (131, 1), (15299, 1)] : List FactorBlock).map factorBlockValue).prod) = 96200113 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_131
      · exact prime_fiftySixBB_15299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 96200113) ^ 48100056 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 96200113) ^ 32066704 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 96200113) ^ 734352 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 96200113) ^ 6288 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_97264499 : Nat.Prime 97264499 := by
  apply lucas_primality 97264499 (2 : ZMod 97264499)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (107, 1), (454507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (107, 1), (454507, 1)] : List FactorBlock).map factorBlockValue).prod) = 97264499 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_107
      · exact prime_fiftySixBB_454507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 97264499) ^ 48632249 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 97264499) ^ 909014 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 97264499) ^ 214 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_106379677 : Nat.Prime 106379677 := by
  apply lucas_primality 106379677 (2 : ZMod 106379677)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (13, 1), (17, 1), (4457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (13, 1), (17, 1), (4457, 1)] : List FactorBlock).map factorBlockValue).prod) = 106379677 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_13
      · exact prime_fiftySixBB_17
      · exact prime_fiftySixBB_4457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 106379677) ^ 53189838 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 106379677) ^ 35459892 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 106379677) ^ 8183052 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 106379677) ^ 6257628 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 106379677) ^ 23868 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_118781783 : Nat.Prime 118781783 := by
  apply lucas_primality 118781783 (5 : ZMod 118781783)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (421, 1), (2879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (421, 1), (2879, 1)] : List FactorBlock).map factorBlockValue).prod) = 118781783 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_7
      · exact prime_fiftySixBB_421
      · exact prime_fiftySixBB_2879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 118781783) ^ 59390891 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 118781783) ^ 16968826 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 118781783) ^ 282142 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 118781783) ^ 41258 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_120528907 : Nat.Prime 120528907 := by
  apply lucas_primality 120528907 (2 : ZMod 120528907)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (37, 1), (542923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (37, 1), (542923, 1)] : List FactorBlock).map factorBlockValue).prod) = 120528907 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_37
      · exact prime_fiftySixBB_542923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 120528907) ^ 60264453 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 120528907) ^ 40176302 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 120528907) ^ 3257538 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 120528907) ^ 222 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_127656761 : Nat.Prime 127656761 := by
  apply lucas_primality 127656761 (6 : ZMod 127656761)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (7, 2), (11, 1), (31, 1), (191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (7, 2), (11, 1), (31, 1), (191, 1)] : List FactorBlock).map factorBlockValue).prod) = 127656761 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_5
      · exact prime_fiftySixBB_7
      · exact prime_fiftySixBB_11
      · exact prime_fiftySixBB_31
      · exact prime_fiftySixBB_191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 127656761) ^ 63828380 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (6 : ZMod 127656761) ^ 25531352 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (6 : ZMod 127656761) ^ 18236680 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (6 : ZMod 127656761) ^ 11605160 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (6 : ZMod 127656761) ^ 4117960 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (6 : ZMod 127656761) ^ 668360 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_130167463 : Nat.Prime 130167463 := by
  apply lucas_primality 130167463 (6 : ZMod 130167463)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (3527, 1), (6151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (3527, 1), (6151, 1)] : List FactorBlock).map factorBlockValue).prod) = 130167463 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_3527
      · exact prime_fiftySixBB_6151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 130167463) ^ 65083731 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (6 : ZMod 130167463) ^ 43389154 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (6 : ZMod 130167463) ^ 36906 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (6 : ZMod 130167463) ^ 21162 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_146848847 : Nat.Prime 146848847 := by
  apply lucas_primality 146848847 (5 : ZMod 146848847)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (73424423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (73424423, 1)] : List FactorBlock).map factorBlockValue).prod) = 146848847 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_73424423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 146848847) ^ 73424423 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 146848847) ^ 2 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_147636079 : Nat.Prime 147636079 := by
  apply lucas_primality 147636079 (6 : ZMod 147636079)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (24606013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (24606013, 1)] : List FactorBlock).map factorBlockValue).prod) = 147636079 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_24606013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 147636079) ^ 73818039 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (6 : ZMod 147636079) ^ 49212026 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (6 : ZMod 147636079) ^ 6 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_178266971 : Nat.Prime 178266971 := by
  apply lucas_primality 178266971 (2 : ZMod 178266971)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (2546671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (2546671, 1)] : List FactorBlock).map factorBlockValue).prod) = 178266971 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_5
      · exact prime_fiftySixBB_7
      · exact prime_fiftySixBB_2546671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 178266971) ^ 89133485 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 178266971) ^ 35653394 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 178266971) ^ 25466710 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 178266971) ^ 70 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_188801807 : Nat.Prime 188801807 := by
  apply lucas_primality 188801807 (5 : ZMod 188801807)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (449, 1), (210247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (449, 1), (210247, 1)] : List FactorBlock).map factorBlockValue).prod) = 188801807 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_449
      · exact prime_fiftySixBB_210247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 188801807) ^ 94400903 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 188801807) ^ 420494 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 188801807) ^ 898 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_205508873 : Nat.Prime 205508873 := by
  apply lucas_primality 205508873 (3 : ZMod 205508873)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (2381, 1), (10789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (2381, 1), (10789, 1)] : List FactorBlock).map factorBlockValue).prod) = 205508873 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_2381
      · exact prime_fiftySixBB_10789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 205508873) ^ 102754436 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 205508873) ^ 86312 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 205508873) ^ 19048 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_215803673 : Nat.Prime 215803673 := by
  apply lucas_primality 215803673 (3 : ZMod 215803673)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (19, 1), (202823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (19, 1), (202823, 1)] : List FactorBlock).map factorBlockValue).prod) = 215803673 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_7
      · exact prime_fiftySixBB_19
      · exact prime_fiftySixBB_202823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 215803673) ^ 107901836 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 215803673) ^ 30829096 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 215803673) ^ 11358088 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 215803673) ^ 1064 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_219634633 : Nat.Prime 219634633 := by
  apply lucas_primality 219634633 (10 : ZMod 219634633)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (7, 1), (29, 1), (5009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (7, 1), (29, 1), (5009, 1)] : List FactorBlock).map factorBlockValue).prod) = 219634633 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_7
      · exact prime_fiftySixBB_29
      · exact prime_fiftySixBB_5009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 219634633) ^ 109817316 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (10 : ZMod 219634633) ^ 73211544 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (10 : ZMod 219634633) ^ 31376376 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (10 : ZMod 219634633) ^ 7573608 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (10 : ZMod 219634633) ^ 43848 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_228285181 : Nat.Prime 228285181 := by
  apply lucas_primality 228285181 (2 : ZMod 228285181)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (17, 1), (61, 1), (1223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (17, 1), (61, 1), (1223, 1)] : List FactorBlock).map factorBlockValue).prod) = 228285181 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_5
      · exact prime_fiftySixBB_17
      · exact prime_fiftySixBB_61
      · exact prime_fiftySixBB_1223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 228285181) ^ 114142590 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 228285181) ^ 76095060 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 228285181) ^ 45657036 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 228285181) ^ 13428540 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 228285181) ^ 3742380 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 228285181) ^ 186660 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_238382671 : Nat.Prime 238382671 := by
  apply lucas_primality 238382671 (3 : ZMod 238382671)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (17, 1), (467417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (17, 1), (467417, 1)] : List FactorBlock).map factorBlockValue).prod) = 238382671 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_5
      · exact prime_fiftySixBB_17
      · exact prime_fiftySixBB_467417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 238382671) ^ 119191335 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 238382671) ^ 79460890 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 238382671) ^ 47676534 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 238382671) ^ 14022510 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 238382671) ^ 510 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_261073973 : Nat.Prime 261073973 := by
  apply lucas_primality 261073973 (2 : ZMod 261073973)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (53, 1), (1231481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (53, 1), (1231481, 1)] : List FactorBlock).map factorBlockValue).prod) = 261073973 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_53
      · exact prime_fiftySixBB_1231481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 261073973) ^ 130536986 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 261073973) ^ 4925924 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 261073973) ^ 212 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_283205861 : Nat.Prime 283205861 := by
  apply lucas_primality 283205861 (2 : ZMod 283205861)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (41, 1), (49339, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (41, 1), (49339, 1)] : List FactorBlock).map factorBlockValue).prod) = 283205861 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_5
      · exact prime_fiftySixBB_7
      · exact prime_fiftySixBB_41
      · exact prime_fiftySixBB_49339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 283205861) ^ 141602930 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 283205861) ^ 56641172 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 283205861) ^ 40457980 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 283205861) ^ 6907460 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 283205861) ^ 5740 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_330837593 : Nat.Prime 330837593 := by
  apply lucas_primality 330837593 (3 : ZMod 330837593)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (181, 1), (228479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (181, 1), (228479, 1)] : List FactorBlock).map factorBlockValue).prod) = 330837593 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_181
      · exact prime_fiftySixBB_228479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 330837593) ^ 165418796 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 330837593) ^ 1827832 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 330837593) ^ 1448 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_355606253 : Nat.Prime 355606253 := by
  apply lucas_primality 355606253 (2 : ZMod 355606253)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (67, 1), (1326889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (67, 1), (1326889, 1)] : List FactorBlock).map factorBlockValue).prod) = 355606253 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_67
      · exact prime_fiftySixBB_1326889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 355606253) ^ 177803126 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 355606253) ^ 5307556 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 355606253) ^ 268 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_361725197 : Nat.Prime 361725197 := by
  apply lucas_primality 361725197 (3 : ZMod 361725197)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (12918757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (12918757, 1)] : List FactorBlock).map factorBlockValue).prod) = 361725197 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_7
      · exact prime_fiftySixBB_12918757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 361725197) ^ 180862598 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 361725197) ^ 51675028 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 361725197) ^ 28 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_371178389 : Nat.Prime 371178389 := by
  apply lucas_primality 371178389 (2 : ZMod 371178389)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (13256371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (13256371, 1)] : List FactorBlock).map factorBlockValue).prod) = 371178389 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_7
      · exact prime_fiftySixBB_13256371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 371178389) ^ 185589194 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 371178389) ^ 53025484 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 371178389) ^ 28 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_372916067 : Nat.Prime 372916067 := by
  apply lucas_primality 372916067 (2 : ZMod 372916067)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (8106871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (8106871, 1)] : List FactorBlock).map factorBlockValue).prod) = 372916067 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_23
      · exact prime_fiftySixBB_8106871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 372916067) ^ 186458033 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 372916067) ^ 16213742 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 372916067) ^ 46 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_407861903 : Nat.Prime 407861903 := by
  apply lucas_primality 407861903 (5 : ZMod 407861903)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (89, 1), (327337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (89, 1), (327337, 1)] : List FactorBlock).map factorBlockValue).prod) = 407861903 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_7
      · exact prime_fiftySixBB_89
      · exact prime_fiftySixBB_327337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 407861903) ^ 203930951 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 407861903) ^ 58265986 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 407861903) ^ 4582718 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 407861903) ^ 1246 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_412729991 : Nat.Prime 412729991 := by
  apply lucas_primality 412729991 (7 : ZMod 412729991)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (191, 1), (281, 1), (769, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (191, 1), (281, 1), (769, 1)] : List FactorBlock).map factorBlockValue).prod) = 412729991 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_5
      · exact prime_fiftySixBB_191
      · exact prime_fiftySixBB_281
      · exact prime_fiftySixBB_769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 412729991) ^ 206364995 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 412729991) ^ 82545998 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 412729991) ^ 2160890 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 412729991) ^ 1468790 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 412729991) ^ 536710 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_433518637 : Nat.Prime 433518637 := by
  apply lucas_primality 433518637 (5 : ZMod 433518637)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (4133, 1), (8741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (4133, 1), (8741, 1)] : List FactorBlock).map factorBlockValue).prod) = 433518637 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_4133
      · exact prime_fiftySixBB_8741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 433518637) ^ 216759318 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 433518637) ^ 144506212 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 433518637) ^ 104892 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 433518637) ^ 49596 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_459581659 : Nat.Prime 459581659 := by
  apply lucas_primality 459581659 (2 : ZMod 459581659)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (269, 1), (284747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (269, 1), (284747, 1)] : List FactorBlock).map factorBlockValue).prod) = 459581659 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_269
      · exact prime_fiftySixBB_284747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 459581659) ^ 229790829 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 459581659) ^ 153193886 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 459581659) ^ 1708482 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 459581659) ^ 1614 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_548124341 : Nat.Prime 548124341 := by
  apply lucas_primality 548124341 (2 : ZMod 548124341)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (47, 1), (389, 1), (1499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (47, 1), (389, 1), (1499, 1)] : List FactorBlock).map factorBlockValue).prod) = 548124341 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_5
      · exact prime_fiftySixBB_47
      · exact prime_fiftySixBB_389
      · exact prime_fiftySixBB_1499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 548124341) ^ 274062170 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 548124341) ^ 109624868 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 548124341) ^ 11662220 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 548124341) ^ 1409060 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 548124341) ^ 365660 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_602086141 : Nat.Prime 602086141 := by
  apply lucas_primality 602086141 (7 : ZMod 602086141)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (163, 1), (20521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (163, 1), (20521, 1)] : List FactorBlock).map factorBlockValue).prod) = 602086141 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_5
      · exact prime_fiftySixBB_163
      · exact prime_fiftySixBB_20521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 602086141) ^ 301043070 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 602086141) ^ 200695380 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 602086141) ^ 120417228 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 602086141) ^ 3693780 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 602086141) ^ 29340 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_627380101 : Nat.Prime 627380101 := by
  apply lucas_primality 627380101 (6 : ZMod 627380101)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 2), (232363, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 2), (232363, 1)] : List FactorBlock).map factorBlockValue).prod) = 627380101 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_5
      · exact prime_fiftySixBB_232363
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 627380101) ^ 313690050 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (6 : ZMod 627380101) ^ 209126700 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (6 : ZMod 627380101) ^ 125476020 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (6 : ZMod 627380101) ^ 2700 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_651269809 : Nat.Prime 651269809 := by
  apply lucas_primality 651269809 (13 : ZMod 651269809)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 4), (7, 1), (71789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 4), (7, 1), (71789, 1)] : List FactorBlock).map factorBlockValue).prod) = 651269809 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_7
      · exact prime_fiftySixBB_71789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 651269809) ^ 325634904 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (13 : ZMod 651269809) ^ 217089936 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (13 : ZMod 651269809) ^ 93038544 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (13 : ZMod 651269809) ^ 9072 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_661675187 : Nat.Prime 661675187 := by
  apply lucas_primality 661675187 (2 : ZMod 661675187)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (330837593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (330837593, 1)] : List FactorBlock).map factorBlockValue).prod) = 661675187 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_330837593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 661675187) ^ 330837593 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 661675187) ^ 2 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_667748359 : Nat.Prime 667748359 := by
  apply lucas_primality 667748359 (3 : ZMod 667748359)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (461, 1), (80471, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (461, 1), (80471, 1)] : List FactorBlock).map factorBlockValue).prod) = 667748359 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_461
      · exact prime_fiftySixBB_80471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 667748359) ^ 333874179 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 667748359) ^ 222582786 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 667748359) ^ 1448478 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 667748359) ^ 8298 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_692769199 : Nat.Prime 692769199 := by
  apply lucas_primality 692769199 (11 : ZMod 692769199)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (10496503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (10496503, 1)] : List FactorBlock).map factorBlockValue).prod) = 692769199 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_11
      · exact prime_fiftySixBB_10496503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 692769199) ^ 346384599 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (11 : ZMod 692769199) ^ 230923066 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (11 : ZMod 692769199) ^ 62979018 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (11 : ZMod 692769199) ^ 66 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_753319507 : Nat.Prime 753319507 := by
  apply lucas_primality 753319507 (3 : ZMod 753319507)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (389, 1), (14033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (389, 1), (14033, 1)] : List FactorBlock).map factorBlockValue).prod) = 753319507 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_23
      · exact prime_fiftySixBB_389
      · exact prime_fiftySixBB_14033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 753319507) ^ 376659753 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 753319507) ^ 251106502 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 753319507) ^ 32753022 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 753319507) ^ 1936554 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 753319507) ^ 53682 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_922196281 : Nat.Prime 922196281 := by
  apply lucas_primality 922196281 (11 : ZMod 922196281)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (17, 1), (71, 1), (6367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (17, 1), (71, 1), (6367, 1)] : List FactorBlock).map factorBlockValue).prod) = 922196281 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_5
      · exact prime_fiftySixBB_17
      · exact prime_fiftySixBB_71
      · exact prime_fiftySixBB_6367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 922196281) ^ 461098140 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (11 : ZMod 922196281) ^ 307398760 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (11 : ZMod 922196281) ^ 184439256 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (11 : ZMod 922196281) ^ 54246840 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (11 : ZMod 922196281) ^ 12988680 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (11 : ZMod 922196281) ^ 144840 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_1008658451 : Nat.Prime 1008658451 := by
  apply lucas_primality 1008658451 (2 : ZMod 1008658451)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (17, 1), (1186657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (17, 1), (1186657, 1)] : List FactorBlock).map factorBlockValue).prod) = 1008658451 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_5
      · exact prime_fiftySixBB_17
      · exact prime_fiftySixBB_1186657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1008658451) ^ 504329225 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1008658451) ^ 201731690 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1008658451) ^ 59332850 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1008658451) ^ 850 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_1021254089 : Nat.Prime 1021254089 := by
  apply lucas_primality 1021254089 (3 : ZMod 1021254089)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (127656761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (127656761, 1)] : List FactorBlock).map factorBlockValue).prod) = 1021254089 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_127656761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 1021254089) ^ 510627044 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1021254089) ^ 8 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_1103043239 : Nat.Prime 1103043239 := by
  apply lucas_primality 1103043239 (7 : ZMod 1103043239)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (5479, 1), (9151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (5479, 1), (9151, 1)] : List FactorBlock).map factorBlockValue).prod) = 1103043239 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_11
      · exact prime_fiftySixBB_5479
      · exact prime_fiftySixBB_9151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 1103043239) ^ 551521619 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 1103043239) ^ 100276658 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 1103043239) ^ 201322 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 1103043239) ^ 120538 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_1174790777 : Nat.Prime 1174790777 := by
  apply lucas_primality 1174790777 (3 : ZMod 1174790777)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (146848847, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (146848847, 1)] : List FactorBlock).map factorBlockValue).prod) = 1174790777 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_146848847
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 1174790777) ^ 587395388 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1174790777) ^ 8 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_1218582427 : Nat.Prime 1218582427 := by
  apply lucas_primality 1218582427 (2 : ZMod 1218582427)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (79, 1), (2570849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (79, 1), (2570849, 1)] : List FactorBlock).map factorBlockValue).prod) = 1218582427 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_79
      · exact prime_fiftySixBB_2570849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1218582427) ^ 609291213 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1218582427) ^ 406194142 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1218582427) ^ 15425094 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1218582427) ^ 474 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_1514891051 : Nat.Prime 1514891051 := by
  apply lucas_primality 1514891051 (2 : ZMod 1514891051)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (53, 1), (571657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (53, 1), (571657, 1)] : List FactorBlock).map factorBlockValue).prod) = 1514891051 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_5
      · exact prime_fiftySixBB_53
      · exact prime_fiftySixBB_571657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1514891051) ^ 757445525 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1514891051) ^ 302978210 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1514891051) ^ 28582850 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1514891051) ^ 2650 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_1595739571 : Nat.Prime 1595739571 := by
  apply lucas_primality 1595739571 (10 : ZMod 1595739571)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (31, 1), (1715849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (31, 1), (1715849, 1)] : List FactorBlock).map factorBlockValue).prod) = 1595739571 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_5
      · exact prime_fiftySixBB_31
      · exact prime_fiftySixBB_1715849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 1595739571) ^ 797869785 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (10 : ZMod 1595739571) ^ 531913190 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (10 : ZMod 1595739571) ^ 319147914 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (10 : ZMod 1595739571) ^ 51475470 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (10 : ZMod 1595739571) ^ 930 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_1664791591 : Nat.Prime 1664791591 := by
  apply lucas_primality 1664791591 (7 : ZMod 1664791591)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (11, 1), (19, 1), (83, 1), (457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (11, 1), (19, 1), (83, 1), (457, 1)] : List FactorBlock).map factorBlockValue).prod) = 1664791591 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_5
      · exact prime_fiftySixBB_7
      · exact prime_fiftySixBB_11
      · exact prime_fiftySixBB_19
      · exact prime_fiftySixBB_83
      · exact prime_fiftySixBB_457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1664791591) ^ 832395795 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 1664791591) ^ 554930530 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 1664791591) ^ 332958318 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 1664791591) ^ 237827370 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 1664791591) ^ 151344690 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 1664791591) ^ 87620610 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 1664791591) ^ 20057730 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 1664791591) ^ 3642870 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_1717378147 : Nat.Prime 1717378147 := by
  apply lucas_primality 1717378147 (7 : ZMod 1717378147)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (11, 1), (281, 1), (10289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (11, 1), (281, 1), (10289, 1)] : List FactorBlock).map factorBlockValue).prod) = 1717378147 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_11
      · exact prime_fiftySixBB_281
      · exact prime_fiftySixBB_10289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1717378147) ^ 858689073 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 1717378147) ^ 572459382 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 1717378147) ^ 156125286 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 1717378147) ^ 6111666 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 1717378147) ^ 166914 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_1727404801 : Nat.Prime 1727404801 := by
  apply lucas_primality 1727404801 (7 : ZMod 1727404801)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 1), (5, 2), (11, 1), (8179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 1), (5, 2), (11, 1), (8179, 1)] : List FactorBlock).map factorBlockValue).prod) = 1727404801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_5
      · exact prime_fiftySixBB_11
      · exact prime_fiftySixBB_8179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1727404801) ^ 863702400 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 1727404801) ^ 575801600 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 1727404801) ^ 345480960 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 1727404801) ^ 157036800 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 1727404801) ^ 211200 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_1734074549 : Nat.Prime 1734074549 := by
  apply lucas_primality 1734074549 (2 : ZMod 1734074549)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (433518637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (433518637, 1)] : List FactorBlock).map factorBlockValue).prod) = 1734074549 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_433518637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 1734074549) ^ 867037274 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1734074549) ^ 4 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_1875953119 : Nat.Prime 1875953119 := by
  apply lucas_primality 1875953119 (3 : ZMod 1875953119)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (79, 1), (304439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (79, 1), (304439, 1)] : List FactorBlock).map factorBlockValue).prod) = 1875953119 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_13
      · exact prime_fiftySixBB_79
      · exact prime_fiftySixBB_304439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1875953119) ^ 937976559 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1875953119) ^ 625317706 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1875953119) ^ 144304086 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1875953119) ^ 23746242 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1875953119) ^ 6162 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_2042508179 : Nat.Prime 2042508179 := by
  apply lucas_primality 2042508179 (2 : ZMod 2042508179)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1021254089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1021254089, 1)] : List FactorBlock).map factorBlockValue).prod) = 2042508179 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_1021254089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 2042508179) ^ 1021254089 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 2042508179) ^ 2 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_2143992769 : Nat.Prime 2143992769 := by
  apply lucas_primality 2143992769 (11 : ZMod 2143992769)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (11166629, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (11166629, 1)] : List FactorBlock).map factorBlockValue).prod) = 2143992769 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_11166629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 2143992769) ^ 1071996384 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (11 : ZMod 2143992769) ^ 714664256 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (11 : ZMod 2143992769) ^ 192 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_2247554773 : Nat.Prime 2247554773 := by
  apply lucas_primality 2247554773 (5 : ZMod 2247554773)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (62432077, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (62432077, 1)] : List FactorBlock).map factorBlockValue).prod) = 2247554773 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_62432077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 2247554773) ^ 1123777386 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 2247554773) ^ 749184924 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 2247554773) ^ 36 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_2349505663 : Nat.Prime 2349505663 := by
  apply lucas_primality 2349505663 (3 : ZMod 2349505663)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (79, 1), (708109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (79, 1), (708109, 1)] : List FactorBlock).map factorBlockValue).prod) = 2349505663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_7
      · exact prime_fiftySixBB_79
      · exact prime_fiftySixBB_708109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2349505663) ^ 1174752831 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 2349505663) ^ 783168554 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 2349505663) ^ 335643666 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 2349505663) ^ 29740578 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 2349505663) ^ 3318 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_2423336687 : Nat.Prime 2423336687 := by
  apply lucas_primality 2423336687 (5 : ZMod 2423336687)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (41781667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (41781667, 1)] : List FactorBlock).map factorBlockValue).prod) = 2423336687 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_29
      · exact prime_fiftySixBB_41781667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 2423336687) ^ 1211668343 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 2423336687) ^ 83563334 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 2423336687) ^ 58 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_2571178417 : Nat.Prime 2571178417 := by
  apply lucas_primality 2571178417 (7 : ZMod 2571178417)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (419, 1), (127843, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (419, 1), (127843, 1)] : List FactorBlock).map factorBlockValue).prod) = 2571178417 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_419
      · exact prime_fiftySixBB_127843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 2571178417) ^ 1285589208 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 2571178417) ^ 857059472 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 2571178417) ^ 6136464 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 2571178417) ^ 20112 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_2802116873 : Nat.Prime 2802116873 := by
  apply lucas_primality 2802116873 (3 : ZMod 2802116873)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (2917, 1), (120077, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (2917, 1), (120077, 1)] : List FactorBlock).map factorBlockValue).prod) = 2802116873 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_2917
      · exact prime_fiftySixBB_120077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2802116873) ^ 1401058436 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 2802116873) ^ 960616 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 2802116873) ^ 23336 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_2972781473 : Nat.Prime 2972781473 := by
  apply lucas_primality 2972781473 (3 : ZMod 2972781473)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (92899421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (92899421, 1)] : List FactorBlock).map factorBlockValue).prod) = 2972781473 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_92899421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 2972781473) ^ 1486390736 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 2972781473) ^ 32 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_3270803843 : Nat.Prime 3270803843 := by
  apply lucas_primality 3270803843 (2 : ZMod 3270803843)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (96200113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (96200113, 1)] : List FactorBlock).map factorBlockValue).prod) = 3270803843 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_17
      · exact prime_fiftySixBB_96200113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3270803843) ^ 1635401921 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 3270803843) ^ 192400226 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 3270803843) ^ 34 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_3846448201 : Nat.Prime 3846448201 := by
  apply lucas_primality 3846448201 (23 : ZMod 3846448201)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 2), (7, 1), (131, 1), (6991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 2), (7, 1), (131, 1), (6991, 1)] : List FactorBlock).map factorBlockValue).prod) = 3846448201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_5
      · exact prime_fiftySixBB_7
      · exact prime_fiftySixBB_131
      · exact prime_fiftySixBB_6991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 3846448201) ^ 1923224100 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (23 : ZMod 3846448201) ^ 1282149400 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (23 : ZMod 3846448201) ^ 769289640 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (23 : ZMod 3846448201) ^ 549492600 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (23 : ZMod 3846448201) ^ 29362200 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (23 : ZMod 3846448201) ^ 550200 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_3954647791 : Nat.Prime 3954647791 := by
  apply lucas_primality 3954647791 (3 : ZMod 3954647791)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (43940531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (43940531, 1)] : List FactorBlock).map factorBlockValue).prod) = 3954647791 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_5
      · exact prime_fiftySixBB_43940531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3954647791) ^ 1977323895 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 3954647791) ^ 1318215930 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 3954647791) ^ 790929558 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 3954647791) ^ 90 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_4027570517 : Nat.Prime 4027570517 := by
  apply lucas_primality 4027570517 (2 : ZMod 4027570517)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (467, 1), (2156087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (467, 1), (2156087, 1)] : List FactorBlock).map factorBlockValue).prod) = 4027570517 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_467
      · exact prime_fiftySixBB_2156087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4027570517) ^ 2013785258 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 4027570517) ^ 8624348 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 4027570517) ^ 1868 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_4293812539 : Nat.Prime 4293812539 := by
  apply lucas_primality 4293812539 (7 : ZMod 4293812539)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (79515047, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (79515047, 1)] : List FactorBlock).map factorBlockValue).prod) = 4293812539 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_79515047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 4293812539) ^ 2146906269 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 4293812539) ^ 1431270846 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 4293812539) ^ 54 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_4560605677 : Nat.Prime 4560605677 := by
  apply lucas_primality 4560605677 (5 : ZMod 4560605677)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (11, 2), (179, 1), (5849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (11, 2), (179, 1), (5849, 1)] : List FactorBlock).map factorBlockValue).prod) = 4560605677 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_11
      · exact prime_fiftySixBB_179
      · exact prime_fiftySixBB_5849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 4560605677) ^ 2280302838 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 4560605677) ^ 1520201892 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 4560605677) ^ 414600516 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 4560605677) ^ 25478244 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 4560605677) ^ 779724 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_4650856811 : Nat.Prime 4650856811 := by
  apply lucas_primality 4650856811 (2 : ZMod 4650856811)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (251, 1), (379, 1), (4889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (251, 1), (379, 1), (4889, 1)] : List FactorBlock).map factorBlockValue).prod) = 4650856811 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_5
      · exact prime_fiftySixBB_251
      · exact prime_fiftySixBB_379
      · exact prime_fiftySixBB_4889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4650856811) ^ 2325428405 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 4650856811) ^ 930171362 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 4650856811) ^ 18529310 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 4650856811) ^ 12271390 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 4650856811) ^ 951290 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_6681211003 : Nat.Prime 6681211003 := by
  apply lucas_primality 6681211003 (2 : ZMod 6681211003)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (371178389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (371178389, 1)] : List FactorBlock).map factorBlockValue).prod) = 6681211003 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_371178389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 6681211003) ^ 3340605501 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 6681211003) ^ 2227070334 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 6681211003) ^ 18 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_6887453099 : Nat.Prime 6887453099 := by
  apply lucas_primality 6887453099 (2 : ZMod 6887453099)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (26357, 1), (130657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (26357, 1), (130657, 1)] : List FactorBlock).map factorBlockValue).prod) = 6887453099 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_26357
      · exact prime_fiftySixBB_130657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 6887453099) ^ 3443726549 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 6887453099) ^ 261314 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 6887453099) ^ 52714 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_7113705553 : Nat.Prime 7113705553 := by
  apply lucas_primality 7113705553 (7 : ZMod 7113705553)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (1201, 1), (13711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (1201, 1), (13711, 1)] : List FactorBlock).map factorBlockValue).prod) = 7113705553 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_1201
      · exact prime_fiftySixBB_13711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 7113705553) ^ 3556852776 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 7113705553) ^ 2371235184 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 7113705553) ^ 5923152 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 7113705553) ^ 518832 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_7255842257 : Nat.Prime 7255842257 := by
  apply lucas_primality 7255842257 (3 : ZMod 7255842257)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (13, 1), (139, 1), (250963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (13, 1), (139, 1), (250963, 1)] : List FactorBlock).map factorBlockValue).prod) = 7255842257 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_13
      · exact prime_fiftySixBB_139
      · exact prime_fiftySixBB_250963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 7255842257) ^ 3627921128 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 7255842257) ^ 558141712 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 7255842257) ^ 52200304 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 7255842257) ^ 28912 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_7533195071 : Nat.Prime 7533195071 := by
  apply lucas_primality 7533195071 (17 : ZMod 7533195071)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (753319507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (753319507, 1)] : List FactorBlock).map factorBlockValue).prod) = 7533195071 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_5
      · exact prime_fiftySixBB_753319507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (17 : ZMod 7533195071) ^ 3766597535 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (17 : ZMod 7533195071) ^ 1506639014 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (17 : ZMod 7533195071) ^ 10 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_8768397551 : Nat.Prime 8768397551 := by
  apply lucas_primality 8768397551 (7 : ZMod 8768397551)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (11, 1), (47, 1), (163, 1), (2081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (11, 1), (47, 1), (163, 1), (2081, 1)] : List FactorBlock).map factorBlockValue).prod) = 8768397551 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_5
      · exact prime_fiftySixBB_11
      · exact prime_fiftySixBB_47
      · exact prime_fiftySixBB_163
      · exact prime_fiftySixBB_2081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 8768397551) ^ 4384198775 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 8768397551) ^ 1753679510 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 8768397551) ^ 797127050 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 8768397551) ^ 186561650 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 8768397551) ^ 53793850 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 8768397551) ^ 4213550 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_9278554063 : Nat.Prime 9278554063 := by
  apply lucas_primality 9278554063 (5 : ZMod 9278554063)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (67235899, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (67235899, 1)] : List FactorBlock).map factorBlockValue).prod) = 9278554063 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_23
      · exact prime_fiftySixBB_67235899
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 9278554063) ^ 4639277031 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 9278554063) ^ 3092851354 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 9278554063) ^ 403415394 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 9278554063) ^ 138 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_9495361613 : Nat.Prime 9495361613 := by
  apply lucas_primality 9495361613 (2 : ZMod 9495361613)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (215803673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (215803673, 1)] : List FactorBlock).map factorBlockValue).prod) = 9495361613 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_11
      · exact prime_fiftySixBB_215803673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 9495361613) ^ 4747680806 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 9495361613) ^ 863214692 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 9495361613) ^ 44 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_9972323201 : Nat.Prime 9972323201 := by
  apply lucas_primality 9972323201 (3 : ZMod 9972323201)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (5, 2), (7, 2), (63599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (5, 2), (7, 2), (63599, 1)] : List FactorBlock).map factorBlockValue).prod) = 9972323201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_5
      · exact prime_fiftySixBB_7
      · exact prime_fiftySixBB_63599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 9972323201) ^ 4986161600 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 9972323201) ^ 1994464640 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 9972323201) ^ 1424617600 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 9972323201) ^ 156800 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_14732232239 : Nat.Prime 14732232239 := by
  apply lucas_primality 14732232239 (7 : ZMod 14732232239)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (53, 1), (1201, 1), (3733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (53, 1), (1201, 1), (3733, 1)] : List FactorBlock).map factorBlockValue).prod) = 14732232239 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_31
      · exact prime_fiftySixBB_53
      · exact prime_fiftySixBB_1201
      · exact prime_fiftySixBB_3733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 14732232239) ^ 7366116119 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 14732232239) ^ 475233298 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 14732232239) ^ 277966646 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 14732232239) ^ 12266638 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 14732232239) ^ 3946486 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_15764043973 : Nat.Prime 15764043973 := by
  apply lucas_primality 15764043973 (2 : ZMod 15764043973)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (8629, 1), (152239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (8629, 1), (152239, 1)] : List FactorBlock).map factorBlockValue).prod) = 15764043973 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_8629
      · exact prime_fiftySixBB_152239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 15764043973) ^ 7882021986 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 15764043973) ^ 5254681324 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 15764043973) ^ 1826868 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 15764043973) ^ 103548 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_18159997147 : Nat.Prime 18159997147 := by
  apply lucas_primality 18159997147 (2 : ZMod 18159997147)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (47, 1), (509, 1), (126517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (47, 1), (509, 1), (126517, 1)] : List FactorBlock).map factorBlockValue).prod) = 18159997147 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_47
      · exact prime_fiftySixBB_509
      · exact prime_fiftySixBB_126517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 18159997147) ^ 9079998573 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 18159997147) ^ 6053332382 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 18159997147) ^ 386382918 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 18159997147) ^ 35677794 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 18159997147) ^ 143538 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_19190512697 : Nat.Prime 19190512697 := by
  apply lucas_primality 19190512697 (3 : ZMod 19190512697)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17, 1), (19, 1), (7426669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17, 1), (19, 1), (7426669, 1)] : List FactorBlock).map factorBlockValue).prod) = 19190512697 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_17
      · exact prime_fiftySixBB_19
      · exact prime_fiftySixBB_7426669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 19190512697) ^ 9595256348 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 19190512697) ^ 1128853688 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 19190512697) ^ 1010026984 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 19190512697) ^ 2584 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_20001778001 : Nat.Prime 20001778001 := by
  apply lucas_primality 20001778001 (3 : ZMod 20001778001)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 3), (61, 1), (67, 1), (2447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 3), (61, 1), (67, 1), (2447, 1)] : List FactorBlock).map factorBlockValue).prod) = 20001778001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_5
      · exact prime_fiftySixBB_61
      · exact prime_fiftySixBB_67
      · exact prime_fiftySixBB_2447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 20001778001) ^ 10000889000 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 20001778001) ^ 4000355600 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 20001778001) ^ 327898000 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 20001778001) ^ 298534000 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 20001778001) ^ 8174000 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_20265076277 : Nat.Prime 20265076277 := by
  apply lucas_primality 20265076277 (2 : ZMod 20265076277)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (613, 1), (8264713, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (613, 1), (8264713, 1)] : List FactorBlock).map factorBlockValue).prod) = 20265076277 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_613
      · exact prime_fiftySixBB_8264713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 20265076277) ^ 10132538138 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 20265076277) ^ 33058852 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 20265076277) ^ 2452 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_23308375481 : Nat.Prime 23308375481 := by
  apply lucas_primality 23308375481 (3 : ZMod 23308375481)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (13, 1), (31, 1), (1445929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (13, 1), (31, 1), (1445929, 1)] : List FactorBlock).map factorBlockValue).prod) = 23308375481 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_5
      · exact prime_fiftySixBB_13
      · exact prime_fiftySixBB_31
      · exact prime_fiftySixBB_1445929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 23308375481) ^ 11654187740 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 23308375481) ^ 4661675096 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 23308375481) ^ 1792951960 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 23308375481) ^ 751883080 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 23308375481) ^ 16120 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_25733689453 : Nat.Prime 25733689453 := by
  apply lucas_primality 25733689453 (5 : ZMod 25733689453)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (19, 1), (59, 1), (127, 1), (5021, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (19, 1), (59, 1), (127, 1), (5021, 1)] : List FactorBlock).map factorBlockValue).prod) = 25733689453 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_19
      · exact prime_fiftySixBB_59
      · exact prime_fiftySixBB_127
      · exact prime_fiftySixBB_5021
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 25733689453) ^ 12866844726 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 25733689453) ^ 8577896484 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 25733689453) ^ 1354404708 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 25733689453) ^ 436164228 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 25733689453) ^ 202627476 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 25733689453) ^ 5125212 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_29794745927 : Nat.Prime 29794745927 := by
  apply lucas_primality 29794745927 (5 : ZMod 29794745927)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (4259, 1), (317987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (4259, 1), (317987, 1)] : List FactorBlock).map factorBlockValue).prod) = 29794745927 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_11
      · exact prime_fiftySixBB_4259
      · exact prime_fiftySixBB_317987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 29794745927) ^ 14897372963 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 29794745927) ^ 2708613266 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 29794745927) ^ 6995714 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 29794745927) ^ 93698 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_30738281129 : Nat.Prime 30738281129 := by
  apply lucas_primality 30738281129 (6 : ZMod 30738281129)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17, 1), (61, 1), (3705193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17, 1), (61, 1), (3705193, 1)] : List FactorBlock).map factorBlockValue).prod) = 30738281129 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_17
      · exact prime_fiftySixBB_61
      · exact prime_fiftySixBB_3705193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 30738281129) ^ 15369140564 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (6 : ZMod 30738281129) ^ 1808134184 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (6 : ZMod 30738281129) ^ 503906248 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (6 : ZMod 30738281129) ^ 8296 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_32563365641 : Nat.Prime 32563365641 := by
  apply lucas_primality 32563365641 (3 : ZMod 32563365641)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (13, 1), (107, 1), (585251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (13, 1), (107, 1), (585251, 1)] : List FactorBlock).map factorBlockValue).prod) = 32563365641 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_5
      · exact prime_fiftySixBB_13
      · exact prime_fiftySixBB_107
      · exact prime_fiftySixBB_585251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 32563365641) ^ 16281682820 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 32563365641) ^ 6512673128 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 32563365641) ^ 2504874280 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 32563365641) ^ 304330520 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 32563365641) ^ 55640 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_35272115069 : Nat.Prime 35272115069 := by
  apply lucas_primality 35272115069 (2 : ZMod 35272115069)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (46817, 1), (188351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (46817, 1), (188351, 1)] : List FactorBlock).map factorBlockValue).prod) = 35272115069 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_46817
      · exact prime_fiftySixBB_188351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 35272115069) ^ 17636057534 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 35272115069) ^ 753404 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 35272115069) ^ 187268 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_38016983041 : Nat.Prime 38016983041 := by
  apply lucas_primality 38016983041 (26 : ZMod 38016983041)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 13), (3, 1), (5, 1), (17, 1), (18199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 13), (3, 1), (5, 1), (17, 1), (18199, 1)] : List FactorBlock).map factorBlockValue).prod) = 38016983041 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_5
      · exact prime_fiftySixBB_17
      · exact prime_fiftySixBB_18199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (26 : ZMod 38016983041) ^ 19008491520 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (26 : ZMod 38016983041) ^ 12672327680 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (26 : ZMod 38016983041) ^ 7603396608 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (26 : ZMod 38016983041) ^ 2236293120 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (26 : ZMod 38016983041) ^ 2088960 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_40087266019 : Nat.Prime 40087266019 := by
  apply lucas_primality 40087266019 (2 : ZMod 40087266019)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (6681211003, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (6681211003, 1)] : List FactorBlock).map factorBlockValue).prod) = 40087266019 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_6681211003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 40087266019) ^ 20043633009 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 40087266019) ^ 13362422006 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 40087266019) ^ 6 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_44346407471 : Nat.Prime 44346407471 := by
  apply lucas_primality 44346407471 (7 : ZMod 44346407471)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (79, 1), (769, 1), (72997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (79, 1), (769, 1), (72997, 1)] : List FactorBlock).map factorBlockValue).prod) = 44346407471 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_5
      · exact prime_fiftySixBB_79
      · exact prime_fiftySixBB_769
      · exact prime_fiftySixBB_72997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 44346407471) ^ 22173203735 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 44346407471) ^ 8869281494 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 44346407471) ^ 561346930 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 44346407471) ^ 57667630 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 44346407471) ^ 607510 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_46157378413 : Nat.Prime 46157378413 := by
  apply lucas_primality 46157378413 (2 : ZMod 46157378413)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (3846448201, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (3846448201, 1)] : List FactorBlock).map factorBlockValue).prod) = 46157378413 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_3846448201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 46157378413) ^ 23078689206 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 46157378413) ^ 15385792804 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 46157378413) ^ 12 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_46616750963 : Nat.Prime 46616750963 := by
  apply lucas_primality 46616750963 (2 : ZMod 46616750963)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23308375481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23308375481, 1)] : List FactorBlock).map factorBlockValue).prod) = 46616750963 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_23308375481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 46616750963) ^ 23308375481 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 46616750963) ^ 2 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_49352735143 : Nat.Prime 49352735143 := by
  apply lucas_primality 49352735143 (10 : ZMod 49352735143)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (101, 1), (5077, 1), (5347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (101, 1), (5077, 1), (5347, 1)] : List FactorBlock).map factorBlockValue).prod) = 49352735143 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_101
      · exact prime_fiftySixBB_5077
      · exact prime_fiftySixBB_5347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 49352735143) ^ 24676367571 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (10 : ZMod 49352735143) ^ 16450911714 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (10 : ZMod 49352735143) ^ 488640942 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (10 : ZMod 49352735143) ^ 9720846 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (10 : ZMod 49352735143) ^ 9229986 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_58431885367 : Nat.Prime 58431885367 := by
  apply lucas_primality 58431885367 (6 : ZMod 58431885367)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (37409, 1), (260329, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (37409, 1), (260329, 1)] : List FactorBlock).map factorBlockValue).prod) = 58431885367 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_37409
      · exact prime_fiftySixBB_260329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 58431885367) ^ 29215942683 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (6 : ZMod 58431885367) ^ 19477295122 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (6 : ZMod 58431885367) ^ 1561974 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (6 : ZMod 58431885367) ^ 224454 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_66571457767 : Nat.Prime 66571457767 := by
  apply lucas_primality 66571457767 (5 : ZMod 66571457767)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (1008658451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (1008658451, 1)] : List FactorBlock).map factorBlockValue).prod) = 66571457767 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_11
      · exact prime_fiftySixBB_1008658451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 66571457767) ^ 33285728883 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 66571457767) ^ 22190485922 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 66571457767) ^ 6051950706 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 66571457767) ^ 66 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_66776672329 : Nat.Prime 66776672329 := by
  apply lucas_primality 66776672329 (7 : ZMod 66776672329)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (73, 1), (38114539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (73, 1), (38114539, 1)] : List FactorBlock).map factorBlockValue).prod) = 66776672329 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_73
      · exact prime_fiftySixBB_38114539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 66776672329) ^ 33388336164 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 66776672329) ^ 22258890776 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 66776672329) ^ 914748936 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 66776672329) ^ 1752 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_76671741329 : Nat.Prime 76671741329 := by
  apply lucas_primality 76671741329 (3 : ZMod 76671741329)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (13, 1), (52659163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (13, 1), (52659163, 1)] : List FactorBlock).map factorBlockValue).prod) = 76671741329 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_7
      · exact prime_fiftySixBB_13
      · exact prime_fiftySixBB_52659163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 76671741329) ^ 38335870664 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 76671741329) ^ 10953105904 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 76671741329) ^ 5897826256 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 76671741329) ^ 1456 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_77922343351 : Nat.Prime 77922343351 := by
  apply lucas_primality 77922343351 (6 : ZMod 77922343351)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (67, 1), (101, 1), (25589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (67, 1), (101, 1), (25589, 1)] : List FactorBlock).map factorBlockValue).prod) = 77922343351 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_5
      · exact prime_fiftySixBB_67
      · exact prime_fiftySixBB_101
      · exact prime_fiftySixBB_25589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 77922343351) ^ 38961171675 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (6 : ZMod 77922343351) ^ 25974114450 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (6 : ZMod 77922343351) ^ 15584468670 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (6 : ZMod 77922343351) ^ 1163020050 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (6 : ZMod 77922343351) ^ 771508350 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (6 : ZMod 77922343351) ^ 3045150 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_84001067177 : Nat.Prime 84001067177 := by
  apply lucas_primality 84001067177 (3 : ZMod 84001067177)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (23, 1), (1279, 1), (27457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (23, 1), (1279, 1), (27457, 1)] : List FactorBlock).map factorBlockValue).prod) = 84001067177 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_13
      · exact prime_fiftySixBB_23
      · exact prime_fiftySixBB_1279
      · exact prime_fiftySixBB_27457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 84001067177) ^ 42000533588 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 84001067177) ^ 6461620552 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 84001067177) ^ 3652220312 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 84001067177) ^ 65677144 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 84001067177) ^ 3059368 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_93233501927 : Nat.Prime 93233501927 := by
  apply lucas_primality 93233501927 (5 : ZMod 93233501927)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (46616750963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (46616750963, 1)] : List FactorBlock).map factorBlockValue).prod) = 93233501927 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_46616750963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 93233501927) ^ 46616750963 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 93233501927) ^ 2 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_114682684871 : Nat.Prime 114682684871 := by
  apply lucas_primality 114682684871 (23 : ZMod 114682684871)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (23, 1), (769, 1), (49877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (23, 1), (769, 1), (49877, 1)] : List FactorBlock).map factorBlockValue).prod) = 114682684871 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_5
      · exact prime_fiftySixBB_13
      · exact prime_fiftySixBB_23
      · exact prime_fiftySixBB_769
      · exact prime_fiftySixBB_49877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 114682684871) ^ 57341342435 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (23 : ZMod 114682684871) ^ 22936536974 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (23 : ZMod 114682684871) ^ 8821744990 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (23 : ZMod 114682684871) ^ 4986203690 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (23 : ZMod 114682684871) ^ 149132230 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (23 : ZMod 114682684871) ^ 2299310 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_129471756923 : Nat.Prime 129471756923 := by
  apply lucas_primality 129471756923 (2 : ZMod 129471756923)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (59, 1), (4229, 1), (259451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (59, 1), (4229, 1), (259451, 1)] : List FactorBlock).map factorBlockValue).prod) = 129471756923 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_59
      · exact prime_fiftySixBB_4229
      · exact prime_fiftySixBB_259451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 129471756923) ^ 64735878461 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 129471756923) ^ 2194436558 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 129471756923) ^ 30615218 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 129471756923) ^ 499022 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_132325445243 : Nat.Prime 132325445243 := by
  apply lucas_primality 132325445243 (5 : ZMod 132325445243)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (53, 1), (65702803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (53, 1), (65702803, 1)] : List FactorBlock).map factorBlockValue).prod) = 132325445243 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_19
      · exact prime_fiftySixBB_53
      · exact prime_fiftySixBB_65702803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 132325445243) ^ 66162722621 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 132325445243) ^ 6964497118 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 132325445243) ^ 2496706514 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 132325445243) ^ 2014 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_138890556173 : Nat.Prime 138890556173 := by
  apply lucas_primality 138890556173 (2 : ZMod 138890556173)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (2042508179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (2042508179, 1)] : List FactorBlock).map factorBlockValue).prod) = 138890556173 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_17
      · exact prime_fiftySixBB_2042508179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 138890556173) ^ 69445278086 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 138890556173) ^ 8170032716 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 138890556173) ^ 68 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_153343482659 : Nat.Prime 153343482659 := by
  apply lucas_primality 153343482659 (2 : ZMod 153343482659)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (76671741329, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (76671741329, 1)] : List FactorBlock).map factorBlockValue).prod) = 153343482659 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_76671741329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 153343482659) ^ 76671741329 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 153343482659) ^ 2 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_160022813851 : Nat.Prime 160022813851 := by
  apply lucas_primality 160022813851 (2 : ZMod 160022813851)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (355606253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (355606253, 1)] : List FactorBlock).map factorBlockValue).prod) = 160022813851 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_5
      · exact prime_fiftySixBB_355606253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 160022813851) ^ 80011406925 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 160022813851) ^ 53340937950 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 160022813851) ^ 32004562770 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 160022813851) ^ 450 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_174067614401 : Nat.Prime 174067614401 := by
  apply lucas_primality 174067614401 (3 : ZMod 174067614401)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (5, 2), (937, 1), (116107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (5, 2), (937, 1), (116107, 1)] : List FactorBlock).map factorBlockValue).prod) = 174067614401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_5
      · exact prime_fiftySixBB_937
      · exact prime_fiftySixBB_116107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 174067614401) ^ 87033807200 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 174067614401) ^ 34813522880 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 174067614401) ^ 185771200 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 174067614401) ^ 1499200 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_218909072497 : Nat.Prime 218909072497 := by
  apply lucas_primality 218909072497 (5 : ZMod 218909072497)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (4560605677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (4560605677, 1)] : List FactorBlock).map factorBlockValue).prod) = 218909072497 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_4560605677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 218909072497) ^ 109454536248 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 218909072497) ^ 72969690832 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 218909072497) ^ 48 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_249193476541 : Nat.Prime 249193476541 := by
  apply lucas_primality 249193476541 (6 : ZMod 249193476541)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 1), (23, 1), (67, 1), (347, 1), (863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 1), (23, 1), (67, 1), (347, 1), (863, 1)] : List FactorBlock).map factorBlockValue).prod) = 249193476541 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_5
      · exact prime_fiftySixBB_23
      · exact prime_fiftySixBB_67
      · exact prime_fiftySixBB_347
      · exact prime_fiftySixBB_863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 249193476541) ^ 124596738270 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (6 : ZMod 249193476541) ^ 83064492180 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (6 : ZMod 249193476541) ^ 49838695308 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (6 : ZMod 249193476541) ^ 10834498980 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (6 : ZMod 249193476541) ^ 3719305620 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (6 : ZMod 249193476541) ^ 718136820 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (6 : ZMod 249193476541) ^ 288752580 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_251572542787 : Nat.Prime 251572542787 := by
  apply lucas_primality 251572542787 (2 : ZMod 251572542787)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (271, 1), (5693, 1), (9059, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (271, 1), (5693, 1), (9059, 1)] : List FactorBlock).map factorBlockValue).prod) = 251572542787 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_271
      · exact prime_fiftySixBB_5693
      · exact prime_fiftySixBB_9059
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 251572542787) ^ 125786271393 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 251572542787) ^ 83857514262 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 251572542787) ^ 928311966 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 251572542787) ^ 44189802 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 251572542787) ^ 27770454 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_274804002497 : Nat.Prime 274804002497 := by
  apply lucas_primality 274804002497 (3 : ZMod 274804002497)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (4293812539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (4293812539, 1)] : List FactorBlock).map factorBlockValue).prod) = 274804002497 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_4293812539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 274804002497) ^ 137402001248 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 274804002497) ^ 64 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_294644644781 : Nat.Prime 294644644781 := by
  apply lucas_primality 294644644781 (2 : ZMod 294644644781)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (14732232239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (14732232239, 1)] : List FactorBlock).map factorBlockValue).prod) = 294644644781 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_5
      · exact prime_fiftySixBB_14732232239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 294644644781) ^ 147322322390 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 294644644781) ^ 58928928956 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 294644644781) ^ 20 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_437540673079 : Nat.Prime 437540673079 := by
  apply lucas_primality 437540673079 (3 : ZMod 437540673079)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (131, 1), (233, 1), (265459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (131, 1), (233, 1), (265459, 1)] : List FactorBlock).map factorBlockValue).prod) = 437540673079 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_131
      · exact prime_fiftySixBB_233
      · exact prime_fiftySixBB_265459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 437540673079) ^ 218770336539 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 437540673079) ^ 145846891026 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 437540673079) ^ 3340005138 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 437540673079) ^ 1877856966 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 437540673079) ^ 1648242 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_483268841543 : Nat.Prime 483268841543 := by
  apply lucas_primality 483268841543 (5 : ZMod 483268841543)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (71, 1), (541, 1), (6290761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (71, 1), (541, 1), (6290761, 1)] : List FactorBlock).map factorBlockValue).prod) = 483268841543 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_71
      · exact prime_fiftySixBB_541
      · exact prime_fiftySixBB_6290761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 483268841543) ^ 241634420771 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 483268841543) ^ 6806603402 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 483268841543) ^ 893288062 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 483268841543) ^ 76822 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_524065109329 : Nat.Prime 524065109329 := by
  apply lucas_primality 524065109329 (7 : ZMod 524065109329)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (23, 1), (52744073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (23, 1), (52744073, 1)] : List FactorBlock).map factorBlockValue).prod) = 524065109329 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_23
      · exact prime_fiftySixBB_52744073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 524065109329) ^ 262032554664 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 524065109329) ^ 174688369776 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 524065109329) ^ 22785439536 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 524065109329) ^ 9936 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_583144971181 : Nat.Prime 583144971181 := by
  apply lucas_primality 583144971181 (2 : ZMod 583144971181)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (541, 1), (853, 1), (21061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (541, 1), (853, 1), (21061, 1)] : List FactorBlock).map factorBlockValue).prod) = 583144971181 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_5
      · exact prime_fiftySixBB_541
      · exact prime_fiftySixBB_853
      · exact prime_fiftySixBB_21061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 583144971181) ^ 291572485590 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 583144971181) ^ 194381657060 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 583144971181) ^ 116628994236 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 583144971181) ^ 1077901980 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 583144971181) ^ 683640060 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 583144971181) ^ 27688380 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_618659636789 : Nat.Prime 618659636789 := by
  apply lucas_primality 618659636789 (2 : ZMod 618659636789)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (37, 1), (7949, 1), (525869, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (37, 1), (7949, 1), (525869, 1)] : List FactorBlock).map factorBlockValue).prod) = 618659636789 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_37
      · exact prime_fiftySixBB_7949
      · exact prime_fiftySixBB_525869
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 618659636789) ^ 309329818394 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 618659636789) ^ 16720530724 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 618659636789) ^ 77828612 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 618659636789) ^ 1176452 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_667101754351 : Nat.Prime 667101754351 := by
  apply lucas_primality 667101754351 (13 : ZMod 667101754351)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (19, 1), (78023597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (19, 1), (78023597, 1)] : List FactorBlock).map factorBlockValue).prod) = 667101754351 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_5
      · exact prime_fiftySixBB_19
      · exact prime_fiftySixBB_78023597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 667101754351) ^ 333550877175 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (13 : ZMod 667101754351) ^ 222367251450 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (13 : ZMod 667101754351) ^ 133420350870 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (13 : ZMod 667101754351) ^ 35110618650 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (13 : ZMod 667101754351) ^ 8550 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_686631416353 : Nat.Prime 686631416353 := by
  apply lucas_primality 686631416353 (5 : ZMod 686631416353)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (7, 3), (20852509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (7, 3), (20852509, 1)] : List FactorBlock).map factorBlockValue).prod) = 686631416353 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_7
      · exact prime_fiftySixBB_20852509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 686631416353) ^ 343315708176 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 686631416353) ^ 228877138784 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 686631416353) ^ 98090202336 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 686631416353) ^ 32928 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_720365997697 : Nat.Prime 720365997697 := by
  apply lucas_primality 720365997697 (7 : ZMod 720365997697)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (1875953119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (1875953119, 1)] : List FactorBlock).map factorBlockValue).prod) = 720365997697 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_1875953119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 720365997697) ^ 360182998848 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 720365997697) ^ 240121999232 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 720365997697) ^ 384 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_752050583071 : Nat.Prime 752050583071 := by
  apply lucas_primality 752050583071 (6 : ZMod 752050583071)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (379, 1), (1733, 1), (38167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (379, 1), (1733, 1), (38167, 1)] : List FactorBlock).map factorBlockValue).prod) = 752050583071 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_5
      · exact prime_fiftySixBB_379
      · exact prime_fiftySixBB_1733
      · exact prime_fiftySixBB_38167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 752050583071) ^ 376025291535 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (6 : ZMod 752050583071) ^ 250683527690 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (6 : ZMod 752050583071) ^ 150410116614 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (6 : ZMod 752050583071) ^ 1984302330 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (6 : ZMod 752050583071) ^ 433958790 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (6 : ZMod 752050583071) ^ 19704210 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_841150196333 : Nat.Prime 841150196333 := by
  apply lucas_primality 841150196333 (2 : ZMod 841150196333)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (179, 1), (1174790777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (179, 1), (1174790777, 1)] : List FactorBlock).map factorBlockValue).prod) = 841150196333 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_179
      · exact prime_fiftySixBB_1174790777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 841150196333) ^ 420575098166 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 841150196333) ^ 4699163108 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 841150196333) ^ 716 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_1006290171149 : Nat.Prime 1006290171149 := by
  apply lucas_primality 1006290171149 (2 : ZMod 1006290171149)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (251572542787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (251572542787, 1)] : List FactorBlock).map factorBlockValue).prod) = 1006290171149 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_251572542787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 1006290171149) ^ 503145085574 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1006290171149) ^ 4 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_1146423076607 : Nat.Prime 1146423076607 := by
  apply lucas_primality 1146423076607 (5 : ZMod 1146423076607)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (79, 1), (7255842257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (79, 1), (7255842257, 1)] : List FactorBlock).map factorBlockValue).prod) = 1146423076607 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_79
      · exact prime_fiftySixBB_7255842257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1146423076607) ^ 573211538303 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 1146423076607) ^ 14511684514 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 1146423076607) ^ 158 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_1210609994311 : Nat.Prime 1210609994311 := by
  apply lucas_primality 1210609994311 (6 : ZMod 1210609994311)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (19, 1), (761, 1), (930301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (19, 1), (761, 1), (930301, 1)] : List FactorBlock).map factorBlockValue).prod) = 1210609994311 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_5
      · exact prime_fiftySixBB_19
      · exact prime_fiftySixBB_761
      · exact prime_fiftySixBB_930301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1210609994311) ^ 605304997155 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (6 : ZMod 1210609994311) ^ 403536664770 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (6 : ZMod 1210609994311) ^ 242121998862 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (6 : ZMod 1210609994311) ^ 63716315490 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (6 : ZMod 1210609994311) ^ 1590814710 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (6 : ZMod 1210609994311) ^ 1301310 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_1295964640559 : Nat.Prime 1295964640559 := by
  apply lucas_primality 1295964640559 (7 : ZMod 1295964640559)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (307, 1), (839, 1), (359389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (307, 1), (839, 1), (359389, 1)] : List FactorBlock).map factorBlockValue).prod) = 1295964640559 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_7
      · exact prime_fiftySixBB_307
      · exact prime_fiftySixBB_839
      · exact prime_fiftySixBB_359389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1295964640559) ^ 647982320279 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 1295964640559) ^ 185137805794 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 1295964640559) ^ 4221383194 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 1295964640559) ^ 1544653922 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 1295964640559) ^ 3606022 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_1332086172569 : Nat.Prime 1332086172569 := by
  apply lucas_primality 1332086172569 (3 : ZMod 1332086172569)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (41, 1), (197, 1), (239, 1), (86257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (41, 1), (197, 1), (239, 1), (86257, 1)] : List FactorBlock).map factorBlockValue).prod) = 1332086172569 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_41
      · exact prime_fiftySixBB_197
      · exact prime_fiftySixBB_239
      · exact prime_fiftySixBB_86257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1332086172569) ^ 666043086284 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1332086172569) ^ 32489906648 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1332086172569) ^ 6761858744 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1332086172569) ^ 5573582312 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1332086172569) ^ 15443224 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_2013036748361 : Nat.Prime 2013036748361 := by
  apply lucas_primality 2013036748361 (6 : ZMod 2013036748361)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (11, 1), (277, 1), (2969, 1), (5563, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (11, 1), (277, 1), (2969, 1), (5563, 1)] : List FactorBlock).map factorBlockValue).prod) = 2013036748361 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_5
      · exact prime_fiftySixBB_11
      · exact prime_fiftySixBB_277
      · exact prime_fiftySixBB_2969
      · exact prime_fiftySixBB_5563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 2013036748361) ^ 1006518374180 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (6 : ZMod 2013036748361) ^ 402607349672 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (6 : ZMod 2013036748361) ^ 183003340760 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (6 : ZMod 2013036748361) ^ 7267280680 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (6 : ZMod 2013036748361) ^ 678018440 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (6 : ZMod 2013036748361) ^ 361861720 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_2226099472853 : Nat.Prime 2226099472853 := by
  apply lucas_primality 2226099472853 (2 : ZMod 2226099472853)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 1), (19190512697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 1), (19190512697, 1)] : List FactorBlock).map factorBlockValue).prod) = 2226099472853 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_29
      · exact prime_fiftySixBB_19190512697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2226099472853) ^ 1113049736426 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 2226099472853) ^ 76762050788 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 2226099472853) ^ 116 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_2930503252087 : Nat.Prime 2930503252087 := by
  apply lucas_primality 2930503252087 (6 : ZMod 2930503252087)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (1493, 1), (5051, 1), (21589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (1493, 1), (5051, 1), (21589, 1)] : List FactorBlock).map factorBlockValue).prod) = 2930503252087 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_1493
      · exact prime_fiftySixBB_5051
      · exact prime_fiftySixBB_21589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 2930503252087) ^ 1465251626043 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (6 : ZMod 2930503252087) ^ 976834417362 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (6 : ZMod 2930503252087) ^ 1962828702 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (6 : ZMod 2930503252087) ^ 580182786 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (6 : ZMod 2930503252087) ^ 135740574 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_4160692695739 : Nat.Prime 4160692695739 := by
  apply lucas_primality 4160692695739 (2 : ZMod 4160692695739)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 1), (59, 1), (2731, 1), (148403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 1), (59, 1), (2731, 1), (148403, 1)] : List FactorBlock).map factorBlockValue).prod) = 4160692695739 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_29
      · exact prime_fiftySixBB_59
      · exact prime_fiftySixBB_2731
      · exact prime_fiftySixBB_148403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4160692695739) ^ 2080346347869 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 4160692695739) ^ 1386897565246 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 4160692695739) ^ 143472161922 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 4160692695739) ^ 70520215182 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 4160692695739) ^ 1523505198 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 4160692695739) ^ 28036446 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_5942163459247 : Nat.Prime 5942163459247 := by
  apply lucas_primality 5942163459247 (3 : ZMod 5942163459247)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (109, 1), (331, 1), (1399, 1), (2803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (109, 1), (331, 1), (1399, 1), (2803, 1)] : List FactorBlock).map factorBlockValue).prod) = 5942163459247 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_7
      · exact prime_fiftySixBB_109
      · exact prime_fiftySixBB_331
      · exact prime_fiftySixBB_1399
      · exact prime_fiftySixBB_2803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 5942163459247) ^ 2971081729623 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 5942163459247) ^ 1980721153082 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 5942163459247) ^ 848880494178 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 5942163459247) ^ 54515261094 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 5942163459247) ^ 17952155466 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 5942163459247) ^ 4247436354 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 5942163459247) ^ 2119929882 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_7596145097711 : Nat.Prime 7596145097711 := by
  apply lucas_primality 7596145097711 (19 : ZMod 7596145097711)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (58431885367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (58431885367, 1)] : List FactorBlock).map factorBlockValue).prod) = 7596145097711 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_5
      · exact prime_fiftySixBB_13
      · exact prime_fiftySixBB_58431885367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 7596145097711) ^ 3798072548855 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (19 : ZMod 7596145097711) ^ 1519229019542 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (19 : ZMod 7596145097711) ^ 584318853670 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (19 : ZMod 7596145097711) ^ 130 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_7665119763551 : Nat.Prime 7665119763551 := by
  apply lucas_primality 7665119763551 (19 : ZMod 7665119763551)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (79, 1), (499, 1), (3888851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (79, 1), (499, 1), (3888851, 1)] : List FactorBlock).map factorBlockValue).prod) = 7665119763551 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_5
      · exact prime_fiftySixBB_79
      · exact prime_fiftySixBB_499
      · exact prime_fiftySixBB_3888851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 7665119763551) ^ 3832559881775 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (19 : ZMod 7665119763551) ^ 1533023952710 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (19 : ZMod 7665119763551) ^ 97026832450 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (19 : ZMod 7665119763551) ^ 15360961450 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (19 : ZMod 7665119763551) ^ 1971050 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_7797001747441 : Nat.Prime 7797001747441 := by
  apply lucas_primality 7797001747441 (17 : ZMod 7797001747441)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (15661, 1), (2074421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (15661, 1), (2074421, 1)] : List FactorBlock).map factorBlockValue).prod) = 7797001747441 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_5
      · exact prime_fiftySixBB_15661
      · exact prime_fiftySixBB_2074421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 7797001747441) ^ 3898500873720 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (17 : ZMod 7797001747441) ^ 2599000582480 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (17 : ZMod 7797001747441) ^ 1559400349488 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (17 : ZMod 7797001747441) ^ 497861040 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (17 : ZMod 7797001747441) ^ 3758640 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_8051124455639 : Nat.Prime 8051124455639 := by
  apply lucas_primality 8051124455639 (11 : ZMod 8051124455639)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (17, 1), (19, 1), (1619, 1), (699817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (17, 1), (19, 1), (1619, 1), (699817, 1)] : List FactorBlock).map factorBlockValue).prod) = 8051124455639 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_11
      · exact prime_fiftySixBB_17
      · exact prime_fiftySixBB_19
      · exact prime_fiftySixBB_1619
      · exact prime_fiftySixBB_699817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 8051124455639) ^ 4025562227819 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (11 : ZMod 8051124455639) ^ 731920405058 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (11 : ZMod 8051124455639) ^ 473595556214 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (11 : ZMod 8051124455639) ^ 423743392402 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (11 : ZMod 8051124455639) ^ 4972899602 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (11 : ZMod 8051124455639) ^ 11504614 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_8222354312929 : Nat.Prime 8222354312929 := by
  apply lucas_primality 8222354312929 (31 : ZMod 8222354312929)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (7, 1), (13901, 1), (880199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (7, 1), (13901, 1), (880199, 1)] : List FactorBlock).map factorBlockValue).prod) = 8222354312929 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_7
      · exact prime_fiftySixBB_13901
      · exact prime_fiftySixBB_880199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (31 : ZMod 8222354312929) ^ 4111177156464 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (31 : ZMod 8222354312929) ^ 2740784770976 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (31 : ZMod 8222354312929) ^ 1174622044704 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (31 : ZMod 8222354312929) ^ 591493728 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (31 : ZMod 8222354312929) ^ 9341472 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_12485088396817 : Nat.Prime 12485088396817 := by
  apply lucas_primality 12485088396817 (5 : ZMod 12485088396817)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (7, 2), (211, 1), (25157753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (7, 2), (211, 1), (25157753, 1)] : List FactorBlock).map factorBlockValue).prod) = 12485088396817 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_7
      · exact prime_fiftySixBB_211
      · exact prime_fiftySixBB_25157753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 12485088396817) ^ 6242544198408 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 12485088396817) ^ 4161696132272 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 12485088396817) ^ 1783584056688 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 12485088396817) ^ 59171035056 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 12485088396817) ^ 496272 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_14502975966929 : Nat.Prime 14502975966929 := by
  apply lucas_primality 14502975966929 (3 : ZMod 14502975966929)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (1669, 1), (2593, 1), (209449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (1669, 1), (2593, 1), (209449, 1)] : List FactorBlock).map factorBlockValue).prod) = 14502975966929 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_1669
      · exact prime_fiftySixBB_2593
      · exact prime_fiftySixBB_209449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 14502975966929) ^ 7251487983464 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 14502975966929) ^ 8689620112 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 14502975966929) ^ 5593126096 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 14502975966929) ^ 69243472 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_15529240709137 : Nat.Prime 15529240709137 := by
  apply lucas_primality 15529240709137 (5 : ZMod 15529240709137)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (7, 1), (11, 1), (353, 1), (499, 1), (7951, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (7, 1), (11, 1), (353, 1), (499, 1), (7951, 1)] : List FactorBlock).map factorBlockValue).prod) = 15529240709137 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_7
      · exact prime_fiftySixBB_11
      · exact prime_fiftySixBB_353
      · exact prime_fiftySixBB_499
      · exact prime_fiftySixBB_7951
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 15529240709137) ^ 7764620354568 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 15529240709137) ^ 5176413569712 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 15529240709137) ^ 2218462958448 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 15529240709137) ^ 1411749155376 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 15529240709137) ^ 43992183312 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 15529240709137) ^ 31120722864 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 15529240709137) ^ 1953117936 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_18673903145791 : Nat.Prime 18673903145791 := by
  apply lucas_primality 18673903145791 (3 : ZMod 18673903145791)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (9413, 1), (22042687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (9413, 1), (22042687, 1)] : List FactorBlock).map factorBlockValue).prod) = 18673903145791 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_5
      · exact prime_fiftySixBB_9413
      · exact prime_fiftySixBB_22042687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 18673903145791) ^ 9336951572895 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 18673903145791) ^ 6224634381930 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 18673903145791) ^ 3734780629158 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 18673903145791) ^ 1983841830 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 18673903145791) ^ 847170 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_19934982458257 : Nat.Prime 19934982458257 := by
  apply lucas_primality 19934982458257 (5 : ZMod 19934982458257)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (617, 1), (1979, 1), (340129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (617, 1), (1979, 1), (340129, 1)] : List FactorBlock).map factorBlockValue).prod) = 19934982458257 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_617
      · exact prime_fiftySixBB_1979
      · exact prime_fiftySixBB_340129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 19934982458257) ^ 9967491229128 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 19934982458257) ^ 6644994152752 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 19934982458257) ^ 32309533968 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 19934982458257) ^ 10073260464 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 19934982458257) ^ 58610064 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_25770973828681 : Nat.Prime 25770973828681 := by
  apply lucas_primality 25770973828681 (29 : ZMod 25770973828681)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (43, 1), (1664791591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (43, 1), (1664791591, 1)] : List FactorBlock).map factorBlockValue).prod) = 25770973828681 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_5
      · exact prime_fiftySixBB_43
      · exact prime_fiftySixBB_1664791591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (29 : ZMod 25770973828681) ^ 12885486914340 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (29 : ZMod 25770973828681) ^ 8590324609560 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (29 : ZMod 25770973828681) ^ 5154194765736 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (29 : ZMod 25770973828681) ^ 599324972760 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (29 : ZMod 25770973828681) ^ 15480 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_25941157117327 : Nat.Prime 25941157117327 := by
  apply lucas_primality 25941157117327 (5 : ZMod 25941157117327)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (11, 1), (12583, 1), (3470713, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (11, 1), (12583, 1), (3470713, 1)] : List FactorBlock).map factorBlockValue).prod) = 25941157117327 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_11
      · exact prime_fiftySixBB_12583
      · exact prime_fiftySixBB_3470713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 25941157117327) ^ 12970578558663 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 25941157117327) ^ 8647052372442 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 25941157117327) ^ 2358287010666 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 25941157117327) ^ 2061603522 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 25941157117327) ^ 7474302 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_27287293850357 : Nat.Prime 27287293850357 := by
  apply lucas_primality 27287293850357 (2 : ZMod 27287293850357)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (37, 1), (587, 1), (5503, 1), (57077, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (37, 1), (587, 1), (5503, 1), (57077, 1)] : List FactorBlock).map factorBlockValue).prod) = 27287293850357 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_37
      · exact prime_fiftySixBB_587
      · exact prime_fiftySixBB_5503
      · exact prime_fiftySixBB_57077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 27287293850357) ^ 13643646925178 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 27287293850357) ^ 737494428388 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 27287293850357) ^ 46486020188 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 27287293850357) ^ 4958621452 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 27287293850357) ^ 478078628 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_29985914084089 : Nat.Prime 29985914084089 := by
  apply lucas_primality 29985914084089 (7 : ZMod 29985914084089)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (17, 1), (174673, 1), (420757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (17, 1), (174673, 1), (420757, 1)] : List FactorBlock).map factorBlockValue).prod) = 29985914084089 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_17
      · exact prime_fiftySixBB_174673
      · exact prime_fiftySixBB_420757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 29985914084089) ^ 14992957042044 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 29985914084089) ^ 9995304694696 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 29985914084089) ^ 1763877299064 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 29985914084089) ^ 171668856 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 29985914084089) ^ 71266584 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_38446881338053 : Nat.Prime 38446881338053 := by
  apply lucas_primality 38446881338053 (2 : ZMod 38446881338053)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (11, 1), (599, 1), (5779, 1), (9349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (11, 1), (599, 1), (5779, 1), (9349, 1)] : List FactorBlock).map factorBlockValue).prod) = 38446881338053 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_11
      · exact prime_fiftySixBB_599
      · exact prime_fiftySixBB_5779
      · exact prime_fiftySixBB_9349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 38446881338053) ^ 19223440669026 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 38446881338053) ^ 12815627112684 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 38446881338053) ^ 3495171030732 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 38446881338053) ^ 64185110748 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 38446881338053) ^ 6652860588 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 38446881338053) ^ 4112405748 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_44101402262573 : Nat.Prime 44101402262573 := by
  apply lucas_primality 44101402262573 (2 : ZMod 44101402262573)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (67, 1), (283, 1), (4637, 1), (125399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (67, 1), (283, 1), (4637, 1), (125399, 1)] : List FactorBlock).map factorBlockValue).prod) = 44101402262573 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_67
      · exact prime_fiftySixBB_283
      · exact prime_fiftySixBB_4637
      · exact prime_fiftySixBB_125399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 44101402262573) ^ 22050701131286 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 44101402262573) ^ 658229884516 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 44101402262573) ^ 155835343684 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 44101402262573) ^ 9510761756 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 44101402262573) ^ 351688628 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_59468070831677 : Nat.Prime 59468070831677 := by
  apply lucas_primality 59468070831677 (2 : ZMod 59468070831677)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (17, 1), (419, 1), (4127, 1), (38903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (17, 1), (419, 1), (4127, 1), (38903, 1)] : List FactorBlock).map factorBlockValue).prod) = 59468070831677 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_13
      · exact prime_fiftySixBB_17
      · exact prime_fiftySixBB_419
      · exact prime_fiftySixBB_4127
      · exact prime_fiftySixBB_38903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 59468070831677) ^ 29734035415838 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 59468070831677) ^ 4574466987052 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 59468070831677) ^ 3498121813628 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 59468070831677) ^ 141928570004 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 59468070831677) ^ 14409515588 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 59468070831677) ^ 1528624292 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_88229095896547 : Nat.Prime 88229095896547 := by
  apply lucas_primality 88229095896547 (3 : ZMod 88229095896547)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (19, 1), (827, 1), (28358779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (19, 1), (827, 1), (28358779, 1)] : List FactorBlock).map factorBlockValue).prod) = 88229095896547 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_11
      · exact prime_fiftySixBB_19
      · exact prime_fiftySixBB_827
      · exact prime_fiftySixBB_28358779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 88229095896547) ^ 44114547948273 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 88229095896547) ^ 29409698632182 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 88229095896547) ^ 8020826899686 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 88229095896547) ^ 4643636626134 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 88229095896547) ^ 106685726598 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 88229095896547) ^ 3111174 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_88716320317727 : Nat.Prime 88716320317727 := by
  apply lucas_primality 88716320317727 (5 : ZMod 88716320317727)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (1123, 1), (1717378147, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (1123, 1), (1717378147, 1)] : List FactorBlock).map factorBlockValue).prod) = 88716320317727 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_23
      · exact prime_fiftySixBB_1123
      · exact prime_fiftySixBB_1717378147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 88716320317727) ^ 44358160158863 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 88716320317727) ^ 3857231318162 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 88716320317727) ^ 78999394762 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 88716320317727) ^ 51658 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_93519466652483 : Nat.Prime 93519466652483 := by
  apply lucas_primality 93519466652483 (2 : ZMod 93519466652483)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (911, 1), (26947, 1), (146521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (911, 1), (26947, 1), (146521, 1)] : List FactorBlock).map factorBlockValue).prod) = 93519466652483 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_13
      · exact prime_fiftySixBB_911
      · exact prime_fiftySixBB_26947
      · exact prime_fiftySixBB_146521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 93519466652483) ^ 46759733326241 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 93519466652483) ^ 7193805127114 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 93519466652483) ^ 102655836062 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 93519466652483) ^ 3470496406 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 93519466652483) ^ 638266642 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_104733100103693 : Nat.Prime 104733100103693 := by
  apply lucas_primality 104733100103693 (2 : ZMod 104733100103693)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (281, 1), (33679, 1), (2766677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (281, 1), (33679, 1), (2766677, 1)] : List FactorBlock).map factorBlockValue).prod) = 104733100103693 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_281
      · exact prime_fiftySixBB_33679
      · exact prime_fiftySixBB_2766677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 104733100103693) ^ 52366550051846 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 104733100103693) ^ 372715658732 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 104733100103693) ^ 3109744948 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 104733100103693) ^ 37855196 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_117750204835019 : Nat.Prime 117750204835019 := by
  apply lucas_primality 117750204835019 (2 : ZMod 117750204835019)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (17, 1), (37, 1), (1087, 1), (12301369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (17, 1), (37, 1), (1087, 1), (12301369, 1)] : List FactorBlock).map factorBlockValue).prod) = 117750204835019 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_7
      · exact prime_fiftySixBB_17
      · exact prime_fiftySixBB_37
      · exact prime_fiftySixBB_1087
      · exact prime_fiftySixBB_12301369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 117750204835019) ^ 58875102417509 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 117750204835019) ^ 16821457833574 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 117750204835019) ^ 6926482637354 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 117750204835019) ^ 3182437968514 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 117750204835019) ^ 108325855414 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 117750204835019) ^ 9572122 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_134657809527203 : Nat.Prime 134657809527203 := by
  apply lucas_primality 134657809527203 (2 : ZMod 134657809527203)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (421, 1), (43399, 1), (283463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (421, 1), (43399, 1), (283463, 1)] : List FactorBlock).map factorBlockValue).prod) = 134657809527203 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_13
      · exact prime_fiftySixBB_421
      · exact prime_fiftySixBB_43399
      · exact prime_fiftySixBB_283463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 134657809527203) ^ 67328904763601 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 134657809527203) ^ 10358293040554 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 134657809527203) ^ 319852279162 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 134657809527203) ^ 3102785998 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 134657809527203) ^ 475045454 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_141589066728049 : Nat.Prime 141589066728049 := by
  apply lucas_primality 141589066728049 (11 : ZMod 141589066728049)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (29, 1), (317, 1), (16811, 1), (19087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (29, 1), (317, 1), (16811, 1), (19087, 1)] : List FactorBlock).map factorBlockValue).prod) = 141589066728049 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_29
      · exact prime_fiftySixBB_317
      · exact prime_fiftySixBB_16811
      · exact prime_fiftySixBB_19087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 141589066728049) ^ 70794533364024 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (11 : ZMod 141589066728049) ^ 47196355576016 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (11 : ZMod 141589066728049) ^ 4882381611312 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (11 : ZMod 141589066728049) ^ 446653207344 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (11 : ZMod 141589066728049) ^ 8422405968 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (11 : ZMod 141589066728049) ^ 7418089104 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_148702234825633 : Nat.Prime 148702234825633 := by
  apply lucas_primality 148702234825633 (10 : ZMod 148702234825633)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (2341, 1), (661675187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (2341, 1), (661675187, 1)] : List FactorBlock).map factorBlockValue).prod) = 148702234825633 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_2341
      · exact prime_fiftySixBB_661675187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 148702234825633) ^ 74351117412816 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (10 : ZMod 148702234825633) ^ 49567411608544 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (10 : ZMod 148702234825633) ^ 63520817952 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (10 : ZMod 148702234825633) ^ 224736 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_169084920951997 : Nat.Prime 169084920951997 := by
  apply lucas_primality 169084920951997 (5 : ZMod 169084920951997)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (509, 1), (3954647791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (509, 1), (3954647791, 1)] : List FactorBlock).map factorBlockValue).prod) = 169084920951997 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_7
      · exact prime_fiftySixBB_509
      · exact prime_fiftySixBB_3954647791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 169084920951997) ^ 84542460475998 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 169084920951997) ^ 56361640317332 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 169084920951997) ^ 24154988707428 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 169084920951997) ^ 332190414444 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 169084920951997) ^ 42756 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_195787168385233 : Nat.Prime 195787168385233 := by
  apply lucas_primality 195787168385233 (7 : ZMod 195787168385233)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (661, 1), (18661, 1), (330679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (661, 1), (18661, 1), (330679, 1)] : List FactorBlock).map factorBlockValue).prod) = 195787168385233 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_661
      · exact prime_fiftySixBB_18661
      · exact prime_fiftySixBB_330679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 195787168385233) ^ 97893584192616 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 195787168385233) ^ 65262389461744 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 195787168385233) ^ 296198439312 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 195787168385233) ^ 10491783312 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 195787168385233) ^ 592076208 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_200224964144497 : Nat.Prime 200224964144497 := by
  apply lucas_primality 200224964144497 (5 : ZMod 200224964144497)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (197, 1), (251, 1), (433, 1), (194827, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (197, 1), (251, 1), (433, 1), (194827, 1)] : List FactorBlock).map factorBlockValue).prod) = 200224964144497 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_197
      · exact prime_fiftySixBB_251
      · exact prime_fiftySixBB_433
      · exact prime_fiftySixBB_194827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 200224964144497) ^ 100112482072248 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 200224964144497) ^ 66741654714832 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 200224964144497) ^ 1016370376368 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 200224964144497) ^ 797709020496 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 200224964144497) ^ 462413312112 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 200224964144497) ^ 1027706448 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_269030791811857 : Nat.Prime 269030791811857 := by
  apply lucas_primality 269030791811857 (5 : ZMod 269030791811857)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (97, 1), (4993, 1), (11572507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (97, 1), (4993, 1), (11572507, 1)] : List FactorBlock).map factorBlockValue).prod) = 269030791811857 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_97
      · exact prime_fiftySixBB_4993
      · exact prime_fiftySixBB_11572507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 269030791811857) ^ 134515395905928 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 269030791811857) ^ 89676930603952 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 269030791811857) ^ 2773513317648 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 269030791811857) ^ 53881592592 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 269030791811857) ^ 23247408 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_285168955958611 : Nat.Prime 285168955958611 := by
  apply lucas_primality 285168955958611 (2 : ZMod 285168955958611)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (23, 1), (31, 1), (953, 1), (13989383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (23, 1), (31, 1), (953, 1), (13989383, 1)] : List FactorBlock).map factorBlockValue).prod) = 285168955958611 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_5
      · exact prime_fiftySixBB_23
      · exact prime_fiftySixBB_31
      · exact prime_fiftySixBB_953
      · exact prime_fiftySixBB_13989383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 285168955958611) ^ 142584477979305 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 285168955958611) ^ 95056318652870 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 285168955958611) ^ 57033791191722 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 285168955958611) ^ 12398650259070 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 285168955958611) ^ 9198998579310 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 285168955958611) ^ 299232902370 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 285168955958611) ^ 20384670 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_501684070269761 : Nat.Prime 501684070269761 := by
  apply lucas_primality 501684070269761 (3 : ZMod 501684070269761)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (5, 1), (7, 1), (19, 1), (11243, 1), (1048447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (5, 1), (7, 1), (19, 1), (11243, 1), (1048447, 1)] : List FactorBlock).map factorBlockValue).prod) = 501684070269761 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_5
      · exact prime_fiftySixBB_7
      · exact prime_fiftySixBB_19
      · exact prime_fiftySixBB_11243
      · exact prime_fiftySixBB_1048447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 501684070269761) ^ 250842035134880 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 501684070269761) ^ 100336814053952 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 501684070269761) ^ 71669152895680 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 501684070269761) ^ 26404424751040 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 501684070269761) ^ 44621904320 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 501684070269761) ^ 478502080 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_566356266912197 : Nat.Prime 566356266912197 := by
  apply lucas_primality 566356266912197 (2 : ZMod 566356266912197)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (141589066728049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (141589066728049, 1)] : List FactorBlock).map factorBlockValue).prod) = 566356266912197 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_141589066728049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 566356266912197) ^ 283178133456098 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 566356266912197) ^ 4 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_741242125656041 : Nat.Prime 741242125656041 := by
  apply lucas_primality 741242125656041 (3 : ZMod 741242125656041)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (127, 1), (2029, 1), (3023, 1), (23789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (127, 1), (2029, 1), (3023, 1), (23789, 1)] : List FactorBlock).map factorBlockValue).prod) = 741242125656041 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_5
      · exact prime_fiftySixBB_127
      · exact prime_fiftySixBB_2029
      · exact prime_fiftySixBB_3023
      · exact prime_fiftySixBB_23789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 741242125656041) ^ 370621062828020 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 741242125656041) ^ 148248425131208 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 741242125656041) ^ 5836552170520 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 741242125656041) ^ 365323866760 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 741242125656041) ^ 245200835480 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 741242125656041) ^ 31159028360 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_940803220869947 : Nat.Prime 940803220869947 := by
  apply lucas_primality 940803220869947 (2 : ZMod 940803220869947)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (14449, 1), (4650856811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (14449, 1), (4650856811, 1)] : List FactorBlock).map factorBlockValue).prod) = 940803220869947 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_7
      · exact prime_fiftySixBB_14449
      · exact prime_fiftySixBB_4650856811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 940803220869947) ^ 470401610434973 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 940803220869947) ^ 134400460124278 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 940803220869947) ^ 65111995354 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 940803220869947) ^ 202286 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_1070066991781687 : Nat.Prime 1070066991781687 := by
  apply lucas_primality 1070066991781687 (3 : ZMod 1070066991781687)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (478243, 1), (372916067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (478243, 1), (372916067, 1)] : List FactorBlock).map factorBlockValue).prod) = 1070066991781687 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_478243
      · exact prime_fiftySixBB_372916067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1070066991781687) ^ 535033495890843 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1070066991781687) ^ 356688997260562 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1070066991781687) ^ 2237496402 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1070066991781687) ^ 2869458 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_1392736542082349 : Nat.Prime 1392736542082349 := by
  apply lucas_primality 1392736542082349 (2 : ZMod 1392736542082349)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (41, 1), (363947, 1), (1228099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (41, 1), (363947, 1), (1228099, 1)] : List FactorBlock).map factorBlockValue).prod) = 1392736542082349 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_19
      · exact prime_fiftySixBB_41
      · exact prime_fiftySixBB_363947
      · exact prime_fiftySixBB_1228099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1392736542082349) ^ 696368271041174 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1392736542082349) ^ 73301923267492 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1392736542082349) ^ 33969183953228 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1392736542082349) ^ 3826756484 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1392736542082349) ^ 1134058852 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_1407823793269601 : Nat.Prime 1407823793269601 := by
  apply lucas_primality 1407823793269601 (3 : ZMod 1407823793269601)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 2), (7, 1), (107, 1), (2349505663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 2), (7, 1), (107, 1), (2349505663, 1)] : List FactorBlock).map factorBlockValue).prod) = 1407823793269601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_5
      · exact prime_fiftySixBB_7
      · exact prime_fiftySixBB_107
      · exact prime_fiftySixBB_2349505663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1407823793269601) ^ 703911896634800 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1407823793269601) ^ 281564758653920 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1407823793269601) ^ 201117684752800 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1407823793269601) ^ 13157231712800 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1407823793269601) ^ 599200 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_1508995978447961 : Nat.Prime 1508995978447961 := by
  apply lucas_primality 1508995978447961 (3 : ZMod 1508995978447961)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (13463, 1), (2802116873, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (13463, 1), (2802116873, 1)] : List FactorBlock).map factorBlockValue).prod) = 1508995978447961 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_5
      · exact prime_fiftySixBB_13463
      · exact prime_fiftySixBB_2802116873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1508995978447961) ^ 754497989223980 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1508995978447961) ^ 301799195689592 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1508995978447961) ^ 112084674920 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1508995978447961) ^ 538520 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_1711013735751667 : Nat.Prime 1711013735751667 := by
  apply lucas_primality 1711013735751667 (2 : ZMod 1711013735751667)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (285168955958611, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (285168955958611, 1)] : List FactorBlock).map factorBlockValue).prod) = 1711013735751667 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_285168955958611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1711013735751667) ^ 855506867875833 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1711013735751667) ^ 570337911917222 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1711013735751667) ^ 6 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_2252483178934717 : Nat.Prime 2252483178934717 := by
  apply lucas_primality 2252483178934717 (14 : ZMod 2252483178934717)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 6), (7, 1), (13, 1), (127, 1), (66838843, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 6), (7, 1), (13, 1), (127, 1), (66838843, 1)] : List FactorBlock).map factorBlockValue).prod) = 2252483178934717 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_7
      · exact prime_fiftySixBB_13
      · exact prime_fiftySixBB_127
      · exact prime_fiftySixBB_66838843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 2252483178934717) ^ 1126241589467358 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (14 : ZMod 2252483178934717) ^ 750827726311572 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (14 : ZMod 2252483178934717) ^ 321783311276388 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (14 : ZMod 2252483178934717) ^ 173267936841132 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (14 : ZMod 2252483178934717) ^ 17736088023108 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (14 : ZMod 2252483178934717) ^ 33700212 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_3538626651473483 : Nat.Prime 3538626651473483 := by
  apply lucas_primality 3538626651473483 (2 : ZMod 3538626651473483)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (787217, 1), (2247554773, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (787217, 1), (2247554773, 1)] : List FactorBlock).map factorBlockValue).prod) = 3538626651473483 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_787217
      · exact prime_fiftySixBB_2247554773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3538626651473483) ^ 1769313325736741 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 3538626651473483) ^ 4495109546 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 3538626651473483) ^ 1574434 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_3947126526734887 : Nat.Prime 3947126526734887 := by
  apply lucas_primality 3947126526734887 (5 : ZMod 3947126526734887)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (19934982458257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (19934982458257, 1)] : List FactorBlock).map factorBlockValue).prod) = 3947126526734887 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_11
      · exact prime_fiftySixBB_19934982458257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 3947126526734887) ^ 1973563263367443 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 3947126526734887) ^ 1315708842244962 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 3947126526734887) ^ 358829684248626 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 3947126526734887) ^ 198 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_4304492668989713 : Nat.Prime 4304492668989713 := by
  apply lucas_primality 4304492668989713 (3 : ZMod 4304492668989713)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (269030791811857, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (269030791811857, 1)] : List FactorBlock).map factorBlockValue).prod) = 4304492668989713 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_269030791811857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 4304492668989713) ^ 2152246334494856 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 4304492668989713) ^ 16 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_6048341521768043 : Nat.Prime 6048341521768043 := by
  apply lucas_primality 6048341521768043 (2 : ZMod 6048341521768043)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (23, 1), (53, 1), (107, 1), (419, 1), (7905089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (23, 1), (53, 1), (107, 1), (419, 1), (7905089, 1)] : List FactorBlock).map factorBlockValue).prod) = 6048341521768043 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_7
      · exact prime_fiftySixBB_23
      · exact prime_fiftySixBB_53
      · exact prime_fiftySixBB_107
      · exact prime_fiftySixBB_419
      · exact prime_fiftySixBB_7905089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6048341521768043) ^ 3024170760884021 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 6048341521768043) ^ 864048788824006 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 6048341521768043) ^ 262971370511654 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 6048341521768043) ^ 114119651354114 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 6048341521768043) ^ 56526556278206 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 6048341521768043) ^ 14435182629518 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 6048341521768043) ^ 765119978 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_7173004378370641 : Nat.Prime 7173004378370641 := by
  apply lucas_primality 7173004378370641 (21 : ZMod 7173004378370641)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (2927, 1), (39367, 1), (259379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (2927, 1), (39367, 1), (259379, 1)] : List FactorBlock).map factorBlockValue).prod) = 7173004378370641 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_5
      · exact prime_fiftySixBB_2927
      · exact prime_fiftySixBB_39367
      · exact prime_fiftySixBB_259379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (21 : ZMod 7173004378370641) ^ 3586502189185320 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (21 : ZMod 7173004378370641) ^ 2391001459456880 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (21 : ZMod 7173004378370641) ^ 1434600875674128 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (21 : ZMod 7173004378370641) ^ 2450633542320 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (21 : ZMod 7173004378370641) ^ 182208559920 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (21 : ZMod 7173004378370641) ^ 27654530160 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_12071967827583689 : Nat.Prime 12071967827583689 := by
  apply lucas_primality 12071967827583689 (3 : ZMod 12071967827583689)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (1508995978447961, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (1508995978447961, 1)] : List FactorBlock).map factorBlockValue).prod) = 12071967827583689 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_1508995978447961
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 12071967827583689) ^ 6035983913791844 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 12071967827583689) ^ 8 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_20162692742566397 : Nat.Prime 20162692742566397 := by
  apply lucas_primality 20162692742566397 (2 : ZMod 20162692742566397)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (3463, 1), (132325445243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (3463, 1), (132325445243, 1)] : List FactorBlock).map factorBlockValue).prod) = 20162692742566397 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_11
      · exact prime_fiftySixBB_3463
      · exact prime_fiftySixBB_132325445243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 20162692742566397) ^ 10081346371283198 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 20162692742566397) ^ 1832972067506036 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 20162692742566397) ^ 5822319590692 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 20162692742566397) ^ 152372 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_22706856367353751 : Nat.Prime 22706856367353751 := by
  apply lucas_primality 22706856367353751 (3 : ZMod 22706856367353751)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 4), (17, 1), (863, 1), (412729991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 4), (17, 1), (863, 1), (412729991, 1)] : List FactorBlock).map factorBlockValue).prod) = 22706856367353751 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_5
      · exact prime_fiftySixBB_17
      · exact prime_fiftySixBB_863
      · exact prime_fiftySixBB_412729991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 22706856367353751) ^ 11353428183676875 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 22706856367353751) ^ 7568952122451250 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 22706856367353751) ^ 4541371273470750 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 22706856367353751) ^ 1335697433373750 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 22706856367353751) ^ 26311536926250 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 22706856367353751) ^ 55016250 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_23101139984032133 : Nat.Prime 23101139984032133 := by
  apply lucas_primality 23101139984032133 (2 : ZMod 23101139984032133)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (176611, 1), (2972781473, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (176611, 1), (2972781473, 1)] : List FactorBlock).map factorBlockValue).prod) = 23101139984032133 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_11
      · exact prime_fiftySixBB_176611
      · exact prime_fiftySixBB_2972781473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 23101139984032133) ^ 11550569992016066 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 23101139984032133) ^ 2100103634912012 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 23101139984032133) ^ 130802384812 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 23101139984032133) ^ 7770884 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_23396293639338811 : Nat.Prime 23396293639338811 := by
  apply lucas_primality 23396293639338811 (2 : ZMod 23396293639338811)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (17, 1), (61, 1), (752050583071, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (17, 1), (61, 1), (752050583071, 1)] : List FactorBlock).map factorBlockValue).prod) = 23396293639338811 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_5
      · exact prime_fiftySixBB_17
      · exact prime_fiftySixBB_61
      · exact prime_fiftySixBB_752050583071
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 23396293639338811) ^ 11698146819669405 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 23396293639338811) ^ 7798764546446270 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 23396293639338811) ^ 4679258727867762 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 23396293639338811) ^ 1376252567019930 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 23396293639338811) ^ 383545797366210 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 23396293639338811) ^ 31110 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_30861423995319391 : Nat.Prime 30861423995319391 := by
  apply lucas_primality 30861423995319391 (3 : ZMod 30861423995319391)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (93519466652483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (93519466652483, 1)] : List FactorBlock).map factorBlockValue).prod) = 30861423995319391 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_5
      · exact prime_fiftySixBB_11
      · exact prime_fiftySixBB_93519466652483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 30861423995319391) ^ 15430711997659695 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 30861423995319391) ^ 10287141331773130 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 30861423995319391) ^ 6172284799063878 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 30861423995319391) ^ 2805583999574490 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 30861423995319391) ^ 330 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_39076976989226203 : Nat.Prime 39076976989226203 := by
  apply lucas_primality 39076976989226203 (2 : ZMod 39076976989226203)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (19, 1), (23, 1), (1146423076607, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (19, 1), (23, 1), (1146423076607, 1)] : List FactorBlock).map factorBlockValue).prod) = 39076976989226203 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_13
      · exact prime_fiftySixBB_19
      · exact prime_fiftySixBB_23
      · exact prime_fiftySixBB_1146423076607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 39076976989226203) ^ 19538488494613101 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 39076976989226203) ^ 13025658996408734 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 39076976989226203) ^ 3005921306863554 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 39076976989226203) ^ 2056682999432958 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 39076976989226203) ^ 1698998999531574 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 39076976989226203) ^ 34086 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_42951372623209649 : Nat.Prime 42951372623209649 := by
  apply lucas_primality 42951372623209649 (3 : ZMod 42951372623209649)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (13, 1), (47, 1), (61, 1), (65713, 1), (1096061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (13, 1), (47, 1), (61, 1), (65713, 1), (1096061, 1)] : List FactorBlock).map factorBlockValue).prod) = 42951372623209649 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_13
      · exact prime_fiftySixBB_47
      · exact prime_fiftySixBB_61
      · exact prime_fiftySixBB_65713
      · exact prime_fiftySixBB_1096061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 42951372623209649) ^ 21475686311604824 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 42951372623209649) ^ 3303951740246896 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 42951372623209649) ^ 913858991983184 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 42951372623209649) ^ 704120862675568 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 42951372623209649) ^ 653620632496 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 42951372623209649) ^ 39187027568 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_46479945701182171 : Nat.Prime 46479945701182171 := by
  apply lucas_primality 46479945701182171 (3 : ZMod 46479945701182171)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (3541, 1), (437540673079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (3541, 1), (437540673079, 1)] : List FactorBlock).map factorBlockValue).prod) = 46479945701182171 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_5
      · exact prime_fiftySixBB_3541
      · exact prime_fiftySixBB_437540673079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 46479945701182171) ^ 23239972850591085 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 46479945701182171) ^ 15493315233727390 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 46479945701182171) ^ 9295989140236434 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 46479945701182171) ^ 13126220192370 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 46479945701182171) ^ 106230 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_48168371974273897 : Nat.Prime 48168371974273897 := by
  apply lucas_primality 48168371974273897 (5 : ZMod 48168371974273897)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (4153, 1), (483268841543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (4153, 1), (483268841543, 1)] : List FactorBlock).map factorBlockValue).prod) = 48168371974273897 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_4153
      · exact prime_fiftySixBB_483268841543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 48168371974273897) ^ 24084185987136948 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 48168371974273897) ^ 16056123991424632 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 48168371974273897) ^ 11598452197032 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 48168371974273897) ^ 99672 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_192673487897095589 : Nat.Prime 192673487897095589 := by
  apply lucas_primality 192673487897095589 (2 : ZMod 192673487897095589)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (48168371974273897, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (48168371974273897, 1)] : List FactorBlock).map factorBlockValue).prod) = 192673487897095589 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_48168371974273897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 192673487897095589) ^ 96336743948547794 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 192673487897095589) ^ 4 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_193349174014205873 : Nat.Prime 193349174014205873 := by
  apply lucas_primality 193349174014205873 (3 : ZMod 193349174014205873)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (13, 1), (31, 1), (29985914084089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (13, 1), (31, 1), (29985914084089, 1)] : List FactorBlock).map factorBlockValue).prod) = 193349174014205873 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_13
      · exact prime_fiftySixBB_31
      · exact prime_fiftySixBB_29985914084089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 193349174014205873) ^ 96674587007102936 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 193349174014205873) ^ 14873013385708144 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 193349174014205873) ^ 6237070129490512 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 193349174014205873) ^ 6448 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_506237852249668793 : Nat.Prime 506237852249668793 := by
  apply lucas_primality 506237852249668793 (5 : ZMod 506237852249668793)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (41, 1), (2843, 1), (49352735143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (41, 1), (2843, 1), (49352735143, 1)] : List FactorBlock).map factorBlockValue).prod) = 506237852249668793 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_11
      · exact prime_fiftySixBB_41
      · exact prime_fiftySixBB_2843
      · exact prime_fiftySixBB_49352735143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 506237852249668793) ^ 253118926124834396 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 506237852249668793) ^ 46021622931788072 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 506237852249668793) ^ 12347264689016312 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 506237852249668793) ^ 178064668395944 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 506237852249668793) ^ 10257544 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_976333550724236977 : Nat.Prime 976333550724236977 := by
  apply lucas_primality 976333550724236977 (5 : ZMod 976333550724236977)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5050261, 1), (4027570517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5050261, 1), (4027570517, 1)] : List FactorBlock).map factorBlockValue).prod) = 976333550724236977 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_5050261
      · exact prime_fiftySixBB_4027570517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 976333550724236977) ^ 488166775362118488 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 976333550724236977) ^ 325444516908078992 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 976333550724236977) ^ 193323384816 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 976333550724236977) ^ 242412528 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_1065630590924394647 : Nat.Prime 1065630590924394647 := by
  apply lucas_primality 1065630590924394647 (5 : ZMod 1065630590924394647)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (6837773, 1), (77922343351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (6837773, 1), (77922343351, 1)] : List FactorBlock).map factorBlockValue).prod) = 1065630590924394647 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_6837773
      · exact prime_fiftySixBB_77922343351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1065630590924394647) ^ 532815295462197323 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 1065630590924394647) ^ 155844686702 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 1065630590924394647) ^ 13675546 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_1434374043459781607 : Nat.Prime 1434374043459781607 := by
  apply lucas_primality 1434374043459781607 (5 : ZMod 1434374043459781607)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13, 1), (281, 1), (61027, 1), (459581659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13, 1), (281, 1), (61027, 1), (459581659, 1)] : List FactorBlock).map factorBlockValue).prod) = 1434374043459781607 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_7
      · exact prime_fiftySixBB_13
      · exact prime_fiftySixBB_281
      · exact prime_fiftySixBB_61027
      · exact prime_fiftySixBB_459581659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1434374043459781607) ^ 717187021729890803 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 1434374043459781607) ^ 204910577637111658 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 1434374043459781607) ^ 110336464881521662 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 1434374043459781607) ^ 5104533962490326 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 1434374043459781607) ^ 23503925204578 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 1434374043459781607) ^ 3121042834 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_2048219706030468941 : Nat.Prime 2048219706030468941 := by
  apply lucas_primality 2048219706030468941 (2 : ZMod 2048219706030468941)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (3347, 1), (108041, 1), (283205861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (3347, 1), (108041, 1), (283205861, 1)] : List FactorBlock).map factorBlockValue).prod) = 2048219706030468941 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_5
      · exact prime_fiftySixBB_3347
      · exact prime_fiftySixBB_108041
      · exact prime_fiftySixBB_283205861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2048219706030468941) ^ 1024109853015234470 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 2048219706030468941) ^ 409643941206093788 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 2048219706030468941) ^ 611956888566020 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 2048219706030468941) ^ 18957800335340 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 2048219706030468941) ^ 7232264540 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_3310053011609667619 : Nat.Prime 3310053011609667619 := by
  apply lucas_primality 3310053011609667619 (3 : ZMod 3310053011609667619)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (46933, 1), (618659636789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (46933, 1), (618659636789, 1)] : List FactorBlock).map factorBlockValue).prod) = 3310053011609667619 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_19
      · exact prime_fiftySixBB_46933
      · exact prime_fiftySixBB_618659636789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3310053011609667619) ^ 1655026505804833809 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 3310053011609667619) ^ 1103351003869889206 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 3310053011609667619) ^ 174213316400508822 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 3310053011609667619) ^ 70527198593946 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 3310053011609667619) ^ 5350362 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_3704551212047837153 : Nat.Prime 3704551212047837153 := by
  apply lucas_primality 3704551212047837153 (3 : ZMod 3704551212047837153)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (89329, 1), (1295964640559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (89329, 1), (1295964640559, 1)] : List FactorBlock).map factorBlockValue).prod) = 3704551212047837153 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_89329
      · exact prime_fiftySixBB_1295964640559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 3704551212047837153) ^ 1852275606023918576 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 3704551212047837153) ^ 41470868497888 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 3704551212047837153) ^ 2858528 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_4324582462598349901 : Nat.Prime 4324582462598349901 := by
  apply lucas_primality 4324582462598349901 (2 : ZMod 4324582462598349901)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (13, 1), (37, 1), (113, 1), (193, 1), (2143, 1), (641239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (13, 1), (37, 1), (113, 1), (193, 1), (2143, 1), (641239, 1)] : List FactorBlock).map factorBlockValue).prod) = 4324582462598349901 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_5
      · exact prime_fiftySixBB_13
      · exact prime_fiftySixBB_37
      · exact prime_fiftySixBB_113
      · exact prime_fiftySixBB_193
      · exact prime_fiftySixBB_2143
      · exact prime_fiftySixBB_641239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4324582462598349901) ^ 2162291231299174950 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 4324582462598349901) ^ 1441527487532783300 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 4324582462598349901) ^ 864916492519669980 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 4324582462598349901) ^ 332660189430642300 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 4324582462598349901) ^ 116880607097252700 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 4324582462598349901) ^ 38270641261932300 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 4324582462598349901) ^ 22407163018644300 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 4324582462598349901) ^ 2018003948949300 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 4324582462598349901) ^ 6744103934100 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_4417983747923694479 : Nat.Prime 4417983747923694479 := by
  apply lucas_primality 4417983747923694479 (11 : ZMod 4417983747923694479)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (25037, 1), (88229095896547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (25037, 1), (88229095896547, 1)] : List FactorBlock).map factorBlockValue).prod) = 4417983747923694479 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_25037
      · exact prime_fiftySixBB_88229095896547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 4417983747923694479) ^ 2208991873961847239 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (11 : ZMod 4417983747923694479) ^ 176458191793094 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (11 : ZMod 4417983747923694479) ^ 50074 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_6609969620782255129 : Nat.Prime 6609969620782255129 := by
  apply lucas_primality 6609969620782255129 (7 : ZMod 6609969620782255129)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (17, 1), (613, 1), (3621353, 1), (7298069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (17, 1), (613, 1), (3621353, 1), (7298069, 1)] : List FactorBlock).map factorBlockValue).prod) = 6609969620782255129 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_17
      · exact prime_fiftySixBB_613
      · exact prime_fiftySixBB_3621353
      · exact prime_fiftySixBB_7298069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 6609969620782255129) ^ 3304984810391127564 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 6609969620782255129) ^ 2203323206927418376 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 6609969620782255129) ^ 388821742398956184 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 6609969620782255129) ^ 10782984699481656 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 6609969620782255129) ^ 1825276249176 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 6609969620782255129) ^ 905714870712 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_9077868255217730393 : Nat.Prime 9077868255217730393 := by
  apply lucas_primality 9077868255217730393 (3 : ZMod 9077868255217730393)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (97, 1), (1453, 1), (8051124455639, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (97, 1), (1453, 1), (8051124455639, 1)] : List FactorBlock).map factorBlockValue).prod) = 9077868255217730393 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_97
      · exact prime_fiftySixBB_1453
      · exact prime_fiftySixBB_8051124455639
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 9077868255217730393) ^ 4538934127608865196 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 9077868255217730393) ^ 93586270672347736 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 9077868255217730393) ^ 6247672577575864 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 9077868255217730393) ^ 1127528 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_15731014760608141297 : Nat.Prime 15731014760608141297 := by
  apply lucas_primality 15731014760608141297 (5 : ZMod 15731014760608141297)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 5), (157, 1), (25770973828681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 5), (157, 1), (25770973828681, 1)] : List FactorBlock).map factorBlockValue).prod) = 15731014760608141297 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_157
      · exact prime_fiftySixBB_25770973828681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 15731014760608141297) ^ 7865507380304070648 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 15731014760608141297) ^ 5243671586869380432 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 15731014760608141297) ^ 100197546245911728 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 15731014760608141297) ^ 610416 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_30716061827277751681 : Nat.Prime 30716061827277751681 := by
  apply lucas_primality 30716061827277751681 (61 : ZMod 30716061827277751681)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (5, 1), (7, 1), (23, 1), (2659, 1), (89491, 1), (417581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (5, 1), (7, 1), (23, 1), (2659, 1), (89491, 1), (417581, 1)] : List FactorBlock).map factorBlockValue).prod) = 30716061827277751681 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_5
      · exact prime_fiftySixBB_7
      · exact prime_fiftySixBB_23
      · exact prime_fiftySixBB_2659
      · exact prime_fiftySixBB_89491
      · exact prime_fiftySixBB_417581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (61 : ZMod 30716061827277751681) ^ 15358030913638875840 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (61 : ZMod 30716061827277751681) ^ 10238687275759250560 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (61 : ZMod 30716061827277751681) ^ 6143212365455550336 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (61 : ZMod 30716061827277751681) ^ 4388008832468250240 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (61 : ZMod 30716061827277751681) ^ 1335480949012076160 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (61 : ZMod 30716061827277751681) ^ 11551734421691520 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (61 : ZMod 30716061827277751681) ^ 343230736356480 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (61 : ZMod 30716061827277751681) ^ 73557134609280 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_41248383127722139157 : Nat.Prime 41248383127722139157 := by
  apply lucas_primality 41248383127722139157 (2 : ZMod 41248383127722139157)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (448321, 1), (1210609994311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (448321, 1), (1210609994311, 1)] : List FactorBlock).map factorBlockValue).prod) = 41248383127722139157 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_19
      · exact prime_fiftySixBB_448321
      · exact prime_fiftySixBB_1210609994311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 41248383127722139157) ^ 20624191563861069578 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 41248383127722139157) ^ 2170967533038007324 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 41248383127722139157) ^ 92006359567636 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 41248383127722139157) ^ 34072396 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_62207821345309824479 : Nat.Prime 62207821345309824479 := by
  apply lucas_primality 62207821345309824479 (7 : ZMod 62207821345309824479)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (17, 1), (521, 1), (501684070269761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (17, 1), (521, 1), (501684070269761, 1)] : List FactorBlock).map factorBlockValue).prod) = 62207821345309824479 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_7
      · exact prime_fiftySixBB_17
      · exact prime_fiftySixBB_521
      · exact prime_fiftySixBB_501684070269761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 62207821345309824479) ^ 31103910672654912239 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 62207821345309824479) ^ 8886831620758546354 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 62207821345309824479) ^ 3659283608547636734 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 62207821345309824479) ^ 119400808724203118 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 62207821345309824479) ^ 123998 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_90822579144922755997 : Nat.Prime 90822579144922755997 := by
  apply lucas_primality 90822579144922755997 (2 : ZMod 90822579144922755997)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (188801807, 1), (40087266019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (188801807, 1), (40087266019, 1)] : List FactorBlock).map factorBlockValue).prod) = 90822579144922755997 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_188801807
      · exact prime_fiftySixBB_40087266019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 90822579144922755997) ^ 45411289572461377998 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 90822579144922755997) ^ 30274193048307585332 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 90822579144922755997) ^ 481047192228 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 90822579144922755997) ^ 2265621684 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_94386361719004958389 : Nat.Prime 94386361719004958389 := by
  apply lucas_primality 94386361719004958389 (2 : ZMod 94386361719004958389)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (4597, 1), (1711013735751667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (4597, 1), (1711013735751667, 1)] : List FactorBlock).map factorBlockValue).prod) = 94386361719004958389 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_4597
      · exact prime_fiftySixBB_1711013735751667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 94386361719004958389) ^ 47193180859502479194 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 94386361719004958389) ^ 31462120573001652796 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 94386361719004958389) ^ 20532164829020004 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 94386361719004958389) ^ 55164 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_105529240414588870393 : Nat.Prime 105529240414588870393 := by
  apply lucas_primality 105529240414588870393 (7 : ZMod 105529240414588870393)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (613, 1), (7173004378370641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (613, 1), (7173004378370641, 1)] : List FactorBlock).map factorBlockValue).prod) = 105529240414588870393 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_613
      · exact prime_fiftySixBB_7173004378370641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 105529240414588870393) ^ 52764620207294435196 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 105529240414588870393) ^ 35176413471529623464 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 105529240414588870393) ^ 172152105080895384 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 105529240414588870393) ^ 14712 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_149212657232306165857 : Nat.Prime 149212657232306165857 := by
  apply lucas_primality 149212657232306165857 (5 : ZMod 149212657232306165857)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (29, 1), (43, 1), (503, 1), (1429, 1), (1734074549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (29, 1), (43, 1), (503, 1), (1429, 1), (1734074549, 1)] : List FactorBlock).map factorBlockValue).prod) = 149212657232306165857 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_29
      · exact prime_fiftySixBB_43
      · exact prime_fiftySixBB_503
      · exact prime_fiftySixBB_1429
      · exact prime_fiftySixBB_1734074549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 149212657232306165857) ^ 74606328616153082928 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 149212657232306165857) ^ 49737552410768721952 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 149212657232306165857) ^ 5145264042493316064 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 149212657232306165857) ^ 3470061796100143392 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 149212657232306165857) ^ 296645441813729952 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 149212657232306165857) ^ 104417534802173664 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 149212657232306165857) ^ 86047429344 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_610072944166959921377 : Nat.Prime 610072944166959921377 := by
  apply lucas_primality 610072944166959921377 (3 : ZMod 610072944166959921377)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (53, 1), (61, 1), (672521, 1), (8768397551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (53, 1), (61, 1), (672521, 1), (8768397551, 1)] : List FactorBlock).map factorBlockValue).prod) = 610072944166959921377 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_53
      · exact prime_fiftySixBB_61
      · exact prime_fiftySixBB_672521
      · exact prime_fiftySixBB_8768397551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 610072944166959921377) ^ 305036472083479960688 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 610072944166959921377) ^ 11510810267301130592 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 610072944166959921377) ^ 10001195806015736416 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 610072944166959921377) ^ 907143337036256 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 610072944166959921377) ^ 69576332576 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_1030631217342895000603 : Nat.Prime 1030631217342895000603 := by
  apply lucas_primality 1030631217342895000603 (11 : ZMod 1030631217342895000603)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (11, 1), (884029, 1), (841150196333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (11, 1), (884029, 1), (841150196333, 1)] : List FactorBlock).map factorBlockValue).prod) = 1030631217342895000603 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_7
      · exact prime_fiftySixBB_11
      · exact prime_fiftySixBB_884029
      · exact prime_fiftySixBB_841150196333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 1030631217342895000603) ^ 515315608671447500301 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (11 : ZMod 1030631217342895000603) ^ 343543739114298333534 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (11 : ZMod 1030631217342895000603) ^ 147233031048985000086 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (11 : ZMod 1030631217342895000603) ^ 93693747031172272782 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (11 : ZMod 1030631217342895000603) ^ 1165834172117538 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (11 : ZMod 1030631217342895000603) ^ 1225264194 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_1174780344618098168767 : Nat.Prime 1174780344618098168767 := by
  apply lucas_primality 1174780344618098168767 (3 : ZMod 1174780344618098168767)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (15031, 1), (566356266912197, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (15031, 1), (566356266912197, 1)] : List FactorBlock).map factorBlockValue).prod) = 1174780344618098168767 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_23
      · exact prime_fiftySixBB_15031
      · exact prime_fiftySixBB_566356266912197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1174780344618098168767) ^ 587390172309049084383 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1174780344618098168767) ^ 391593448206032722922 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1174780344618098168767) ^ 51077406287743398642 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1174780344618098168767) ^ 78157164833883186 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1174780344618098168767) ^ 2074278 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_1387727643836568978667 : Nat.Prime 1387727643836568978667 := by
  apply lucas_primality 1387727643836568978667 (2 : ZMod 1387727643836568978667)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (147636079, 1), (174067614401, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (147636079, 1), (174067614401, 1)] : List FactorBlock).map factorBlockValue).prod) = 1387727643836568978667 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_147636079
      · exact prime_fiftySixBB_174067614401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1387727643836568978667) ^ 693863821918284489333 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1387727643836568978667) ^ 462575881278856326222 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1387727643836568978667) ^ 9399651177654 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1387727643836568978667) ^ 7972348266 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_1577070521261648103071 : Nat.Prime 1577070521261648103071 := by
  apply lucas_primality 1577070521261648103071 (23 : ZMod 1577070521261648103071)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (853, 1), (1373, 1), (134657809527203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (853, 1), (1373, 1), (134657809527203, 1)] : List FactorBlock).map factorBlockValue).prod) = 1577070521261648103071 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_5
      · exact prime_fiftySixBB_853
      · exact prime_fiftySixBB_1373
      · exact prime_fiftySixBB_134657809527203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 1577070521261648103071) ^ 788535260630824051535 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (23 : ZMod 1577070521261648103071) ^ 315414104252329620614 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (23 : ZMod 1577070521261648103071) ^ 1848851724808497190 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (23 : ZMod 1577070521261648103071) ^ 1148631115267041590 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (23 : ZMod 1577070521261648103071) ^ 11711690 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_1902570600659509135997 : Nat.Prime 1902570600659509135997 := by
  apply lucas_primality 1902570600659509135997 (3 : ZMod 1902570600659509135997)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (23, 1), (10331, 1), (117750204835019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (23, 1), (10331, 1), (117750204835019, 1)] : List FactorBlock).map factorBlockValue).prod) = 1902570600659509135997 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_17
      · exact prime_fiftySixBB_23
      · exact prime_fiftySixBB_10331
      · exact prime_fiftySixBB_117750204835019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1902570600659509135997) ^ 951285300329754567998 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1902570600659509135997) ^ 111915917685853478588 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1902570600659509135997) ^ 82720460898239527652 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1902570600659509135997) ^ 184161320361969716 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 1902570600659509135997) ^ 16157684 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_2700786291404912899423 : Nat.Prime 2700786291404912899423 := by
  apply lucas_primality 2700786291404912899423 (3 : ZMod 2700786291404912899423)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (19, 2), (173, 1), (365983, 1), (1514891051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (19, 2), (173, 1), (365983, 1), (1514891051, 1)] : List FactorBlock).map factorBlockValue).prod) = 2700786291404912899423 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_13
      · exact prime_fiftySixBB_19
      · exact prime_fiftySixBB_173
      · exact prime_fiftySixBB_365983
      · exact prime_fiftySixBB_1514891051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2700786291404912899423) ^ 1350393145702456449711 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 2700786291404912899423) ^ 900262097134970966474 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 2700786291404912899423) ^ 207752791646531761494 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 2700786291404912899423) ^ 142146646916048047338 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 2700786291404912899423) ^ 15611481453207589014 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 2700786291404912899423) ^ 7379540283032034 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 2700786291404912899423) ^ 1782825431322 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_7843930395590947037537 : Nat.Prime 7843930395590947037537 := by
  apply lucas_primality 7843930395590947037537 (3 : ZMod 7843930395590947037537)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (13, 1), (251, 1), (2753, 1), (27287293850357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (13, 1), (251, 1), (2753, 1), (27287293850357, 1)] : List FactorBlock).map factorBlockValue).prod) = 7843930395590947037537 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_13
      · exact prime_fiftySixBB_251
      · exact prime_fiftySixBB_2753
      · exact prime_fiftySixBB_27287293850357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 7843930395590947037537) ^ 3921965197795473518768 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 7843930395590947037537) ^ 603379261199303618272 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 7843930395590947037537) ^ 31250718707533653536 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 7843930395590947037537) ^ 2849230074678876512 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 7843930395590947037537) ^ 287457248 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_8118157752825337199963 : Nat.Prime 8118157752825337199963 := by
  apply lucas_primality 8118157752825337199963 (2 : ZMod 8118157752825337199963)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (31, 1), (677, 1), (3947126526734887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (31, 1), (677, 1), (3947126526734887, 1)] : List FactorBlock).map factorBlockValue).prod) = 8118157752825337199963 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_7
      · exact prime_fiftySixBB_31
      · exact prime_fiftySixBB_677
      · exact prime_fiftySixBB_3947126526734887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8118157752825337199963) ^ 4059078876412668599981 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 8118157752825337199963) ^ 1159736821832191028566 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 8118157752825337199963) ^ 261876056542752812902 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 8118157752825337199963) ^ 11991370388220586706 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 8118157752825337199963) ^ 2056726 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_36199092443853851589797 : Nat.Prime 36199092443853851589797 := by
  apply lucas_primality 36199092443853851589797 (3 : ZMod 36199092443853851589797)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (83, 1), (3533, 1), (30861423995319391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (83, 1), (3533, 1), (30861423995319391, 1)] : List FactorBlock).map factorBlockValue).prod) = 36199092443853851589797 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_83
      · exact prime_fiftySixBB_3533
      · exact prime_fiftySixBB_30861423995319391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 36199092443853851589797) ^ 18099546221926925794898 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 36199092443853851589797) ^ 436133643901853633612 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 36199092443853851589797) ^ 10245992766446037812 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 36199092443853851589797) ^ 1172956 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_41801193361857475018601 : Nat.Prime 41801193361857475018601 := by
  apply lucas_primality 41801193361857475018601 (11 : ZMod 41801193361857475018601)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (17, 1), (71089, 1), (315521, 1), (548124341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (17, 1), (71089, 1), (315521, 1), (548124341, 1)] : List FactorBlock).map factorBlockValue).prod) = 41801193361857475018601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_5
      · exact prime_fiftySixBB_17
      · exact prime_fiftySixBB_71089
      · exact prime_fiftySixBB_315521
      · exact prime_fiftySixBB_548124341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 41801193361857475018601) ^ 20900596680928737509300 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (11 : ZMod 41801193361857475018601) ^ 8360238672371495003720 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (11 : ZMod 41801193361857475018601) ^ 2458893727168086765800 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (11 : ZMod 41801193361857475018601) ^ 588012116668647400 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (11 : ZMod 41801193361857475018601) ^ 132483078342986600 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (11 : ZMod 41801193361857475018601) ^ 76262246054600 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_46128886410655942045787 : Nat.Prime 46128886410655942045787 := by
  apply lucas_primality 46128886410655942045787 (2 : ZMod 46128886410655942045787)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (541, 1), (1091, 1), (39076976989226203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (541, 1), (1091, 1), (39076976989226203, 1)] : List FactorBlock).map factorBlockValue).prod) = 46128886410655942045787 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_541
      · exact prime_fiftySixBB_1091
      · exact prime_fiftySixBB_39076976989226203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 46128886410655942045787) ^ 23064443205327971022893 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 46128886410655942045787) ^ 85265963790491574946 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 46128886410655942045787) ^ 42281289102342751646 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 46128886410655942045787) ^ 1180462 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_47262419189211912150119 : Nat.Prime 47262419189211912150119 := by
  apply lucas_primality 47262419189211912150119 (7 : ZMod 47262419189211912150119)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (67, 1), (21287767, 1), (720365997697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (67, 1), (21287767, 1), (720365997697, 1)] : List FactorBlock).map factorBlockValue).prod) = 47262419189211912150119 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_23
      · exact prime_fiftySixBB_67
      · exact prime_fiftySixBB_21287767
      · exact prime_fiftySixBB_720365997697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 47262419189211912150119) ^ 23631209594605956075059 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 47262419189211912150119) ^ 2054887790835300528266 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 47262419189211912150119) ^ 705409241630028539554 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 47262419189211912150119) ^ 2220168004902154 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 47262419189211912150119) ^ 65608897894 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_54690720495103998431017 : Nat.Prime 54690720495103998431017 := by
  apply lucas_primality 54690720495103998431017 (5 : ZMod 54690720495103998431017)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (58543, 1), (3538626651473483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (58543, 1), (3538626651473483, 1)] : List FactorBlock).map factorBlockValue).prod) = 54690720495103998431017 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_11
      · exact prime_fiftySixBB_58543
      · exact prime_fiftySixBB_3538626651473483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 54690720495103998431017) ^ 27345360247551999215508 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 54690720495103998431017) ^ 18230240165034666143672 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 54690720495103998431017) ^ 4971883681373090766456 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 54690720495103998431017) ^ 934197435988999512 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 54690720495103998431017) ^ 15455352 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_62831809214198923791337 : Nat.Prime 62831809214198923791337 := by
  apply lucas_primality 62831809214198923791337 (5 : ZMod 62831809214198923791337)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (72421, 1), (52181341, 1), (692769199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (72421, 1), (52181341, 1), (692769199, 1)] : List FactorBlock).map factorBlockValue).prod) = 62831809214198923791337 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_72421
      · exact prime_fiftySixBB_52181341
      · exact prime_fiftySixBB_692769199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 62831809214198923791337) ^ 31415904607099461895668 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 62831809214198923791337) ^ 20943936404732974597112 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 62831809214198923791337) ^ 867591019375580616 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 62831809214198923791337) ^ 1204104915858696 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 62831809214198923791337) ^ 90696597517464 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_155545716738576805869323 : Nat.Prime 155545716738576805869323 := by
  apply lucas_primality 155545716738576805869323 (2 : ZMod 155545716738576805869323)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (2141, 1), (6361, 1), (28591, 1), (6887453099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (2141, 1), (6361, 1), (28591, 1), (6887453099, 1)] : List FactorBlock).map factorBlockValue).prod) = 155545716738576805869323 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_29
      · exact prime_fiftySixBB_2141
      · exact prime_fiftySixBB_6361
      · exact prime_fiftySixBB_28591
      · exact prime_fiftySixBB_6887453099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 155545716738576805869323) ^ 77772858369288402934661 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 155545716738576805869323) ^ 5363645404778510547218 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 155545716738576805869323) ^ 72650965314608503442 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 155545716738576805869323) ^ 24453028885171640602 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 155545716738576805869323) ^ 5440373430050603542 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 155545716738576805869323) ^ 22583923912478 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_282683182583752321134697 : Nat.Prime 282683182583752321134697 := by
  apply lucas_primality 282683182583752321134697 (5 : ZMod 282683182583752321134697)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (19, 1), (137, 1), (362429, 1), (12485088396817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (19, 1), (137, 1), (362429, 1), (12485088396817, 1)] : List FactorBlock).map factorBlockValue).prod) = 282683182583752321134697 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_19
      · exact prime_fiftySixBB_137
      · exact prime_fiftySixBB_362429
      · exact prime_fiftySixBB_12485088396817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 282683182583752321134697) ^ 141341591291876160567348 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 282683182583752321134697) ^ 94227727527917440378232 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 282683182583752321134697) ^ 14878062241250122164984 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 282683182583752321134697) ^ 2063380894771914752808 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 282683182583752321134697) ^ 779968442325951624 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 282683182583752321134697) ^ 22641664488 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_399539826138496918559371 : Nat.Prime 399539826138496918559371 := by
  apply lucas_primality 399539826138496918559371 (3 : ZMod 399539826138496918559371)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (1902570600659509135997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (1902570600659509135997, 1)] : List FactorBlock).map factorBlockValue).prod) = 399539826138496918559371 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_5
      · exact prime_fiftySixBB_7
      · exact prime_fiftySixBB_1902570600659509135997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 399539826138496918559371) ^ 199769913069248459279685 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 399539826138496918559371) ^ 133179942046165639519790 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 399539826138496918559371) ^ 79907965227699383711874 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 399539826138496918559371) ^ 57077118019785274079910 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 399539826138496918559371) ^ 210 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_1467873038084383810319179 : Nat.Prime 1467873038084383810319179 := by
  apply lucas_primality 1467873038084383810319179 (2 : ZMod 1467873038084383810319179)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (3853, 1), (2048219706030468941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (3853, 1), (2048219706030468941, 1)] : List FactorBlock).map factorBlockValue).prod) = 1467873038084383810319179 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_31
      · exact prime_fiftySixBB_3853
      · exact prime_fiftySixBB_2048219706030468941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1467873038084383810319179) ^ 733936519042191905159589 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1467873038084383810319179) ^ 489291012694794603439726 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1467873038084383810319179) ^ 47350743164012380978038 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1467873038084383810319179) ^ 380968865321667223026 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1467873038084383810319179) ^ 716658 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_1980702013694670238157011 : Nat.Prime 1980702013694670238157011 := by
  apply lucas_primality 1980702013694670238157011 (12 : ZMod 1980702013694670238157011)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 1), (727, 1), (4324582462598349901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 1), (727, 1), (4324582462598349901, 1)] : List FactorBlock).map factorBlockValue).prod) = 1980702013694670238157011 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_5
      · exact prime_fiftySixBB_7
      · exact prime_fiftySixBB_727
      · exact prime_fiftySixBB_4324582462598349901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (12 : ZMod 1980702013694670238157011) ^ 990351006847335119078505 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (12 : ZMod 1980702013694670238157011) ^ 660234004564890079385670 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (12 : ZMod 1980702013694670238157011) ^ 396140402738934047631402 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (12 : ZMod 1980702013694670238157011) ^ 282957430527810034022430 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (12 : ZMod 1980702013694670238157011) ^ 2724486951436960437630 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (12 : ZMod 1980702013694670238157011) ^ 458010 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_2015923071364656457604173 : Nat.Prime 2015923071364656457604173 := by
  apply lucas_primality 2015923071364656457604173 (5 : ZMod 2015923071364656457604173)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (13, 1), (1174780344618098168767, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (13, 1), (1174780344618098168767, 1)] : List FactorBlock).map factorBlockValue).prod) = 2015923071364656457604173 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_11
      · exact prime_fiftySixBB_13
      · exact prime_fiftySixBB_1174780344618098168767
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2015923071364656457604173) ^ 1007961535682328228802086 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 2015923071364656457604173) ^ 671974357121552152534724 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 2015923071364656457604173) ^ 183265733760423314327652 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 2015923071364656457604173) ^ 155071005489588958277244 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 2015923071364656457604173) ^ 1716 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_4930881470898789556910423 : Nat.Prime 4930881470898789556910423 := by
  apply lucas_primality 4930881470898789556910423 (5 : ZMod 4930881470898789556910423)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (31, 1), (41, 1), (149212657232306165857, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (31, 1), (41, 1), (149212657232306165857, 1)] : List FactorBlock).map factorBlockValue).prod) = 4930881470898789556910423 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_13
      · exact prime_fiftySixBB_31
      · exact prime_fiftySixBB_41
      · exact prime_fiftySixBB_149212657232306165857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 4930881470898789556910423) ^ 2465440735449394778455211 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 4930881470898789556910423) ^ 379298574684522273608494 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 4930881470898789556910423) ^ 159060692609638372803562 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 4930881470898789556910423) ^ 120265401729238769680742 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 4930881470898789556910423) ^ 33046 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_6592347456911087063689759 : Nat.Prime 6592347456911087063689759 := by
  apply lucas_primality 6592347456911087063689759 (3 : ZMod 6592347456911087063689759)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (977, 1), (8543, 1), (858457, 1), (153343482659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (977, 1), (8543, 1), (858457, 1), (153343482659, 1)] : List FactorBlock).map factorBlockValue).prod) = 6592347456911087063689759 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_977
      · exact prime_fiftySixBB_8543
      · exact prime_fiftySixBB_858457
      · exact prime_fiftySixBB_153343482659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 6592347456911087063689759) ^ 3296173728455543531844879 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 6592347456911087063689759) ^ 2197449152303695687896586 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 6592347456911087063689759) ^ 6747540897554848581054 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 6592347456911087063689759) ^ 771666564077149369506 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 6592347456911087063689759) ^ 7679298388749916494 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (3 : ZMod 6592347456911087063689759) ^ 42990724761162 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_8492425026905855230969247 : Nat.Prime 8492425026905855230969247 := by
  apply lucas_primality 8492425026905855230969247 (5 : ZMod 8492425026905855230969247)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (8987357, 1), (42951372623209649, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (8987357, 1), (42951372623209649, 1)] : List FactorBlock).map factorBlockValue).prod) = 8492425026905855230969247 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_11
      · exact prime_fiftySixBB_8987357
      · exact prime_fiftySixBB_42951372623209649
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 8492425026905855230969247) ^ 4246212513452927615484623 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 8492425026905855230969247) ^ 772038638809623202815386 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 8492425026905855230969247) ^ 944930197710612278 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 8492425026905855230969247) ^ 197721854 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_10236076918639153893110119 : Nat.Prime 10236076918639153893110119 := by
  apply lucas_primality 10236076918639153893110119 (6 : ZMod 10236076918639153893110119)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (9859, 1), (15731014760608141297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (9859, 1), (15731014760608141297, 1)] : List FactorBlock).map factorBlockValue).prod) = 10236076918639153893110119 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_11
      · exact prime_fiftySixBB_9859
      · exact prime_fiftySixBB_15731014760608141297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 10236076918639153893110119) ^ 5118038459319576946555059 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (6 : ZMod 10236076918639153893110119) ^ 3412025639546384631036706 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (6 : ZMod 10236076918639153893110119) ^ 930552447149013990282738 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (6 : ZMod 10236076918639153893110119) ^ 1038246974200137325602 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (6 : ZMod 10236076918639153893110119) ^ 650694 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_15300888724233429022564421 : Nat.Prime 15300888724233429022564421 := by
  apply lucas_primality 15300888724233429022564421 (2 : ZMod 15300888724233429022564421)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (727, 1), (11861749, 1), (88716320317727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (727, 1), (11861749, 1), (88716320317727, 1)] : List FactorBlock).map factorBlockValue).prod) = 15300888724233429022564421 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_5
      · exact prime_fiftySixBB_727
      · exact prime_fiftySixBB_11861749
      · exact prime_fiftySixBB_88716320317727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 15300888724233429022564421) ^ 7650444362116714511282210 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 15300888724233429022564421) ^ 3060177744846685804512884 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 15300888724233429022564421) ^ 21046614476249558490460 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 15300888724233429022564421) ^ 1289935297419750580 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 15300888724233429022564421) ^ 172469830460 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_55823731458480647032576939 : Nat.Prime 55823731458480647032576939 := by
  apply lucas_primality 55823731458480647032576939 (2 : ZMod 55823731458480647032576939)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (283, 1), (19387, 1), (238382671, 1), (7113705553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (283, 1), (19387, 1), (238382671, 1), (7113705553, 1)] : List FactorBlock).map factorBlockValue).prod) = 55823731458480647032576939 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_283
      · exact prime_fiftySixBB_19387
      · exact prime_fiftySixBB_238382671
      · exact prime_fiftySixBB_7113705553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 55823731458480647032576939) ^ 27911865729240323516288469 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 55823731458480647032576939) ^ 18607910486160215677525646 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 55823731458480647032576939) ^ 197257001620072957712286 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 55823731458480647032576939) ^ 2879441453472979162974 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 55823731458480647032576939) ^ 234176969426106678 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 55823731458480647032576939) ^ 7847349182865546 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_122378827189940937856998613 : Nat.Prime 122378827189940937856998613 := by
  apply lucas_primality 122378827189940937856998613 (5 : ZMod 122378827189940937856998613)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (293, 1), (41957, 1), (28180973, 1), (3270803843, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (293, 1), (41957, 1), (28180973, 1), (3270803843, 1)] : List FactorBlock).map factorBlockValue).prod) = 122378827189940937856998613 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_293
      · exact prime_fiftySixBB_41957
      · exact prime_fiftySixBB_28180973
      · exact prime_fiftySixBB_3270803843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 122378827189940937856998613) ^ 61189413594970468928499306 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 122378827189940937856998613) ^ 40792942396646979285666204 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 122378827189940937856998613) ^ 417675178122665316918084 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 122378827189940937856998613) ^ 2916767814427650638916 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 122378827189940937856998613) ^ 4342604749308724644 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 122378827189940937856998613) ^ 37415520179190684 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_135948553408127407352435831 : Nat.Prime 135948553408127407352435831 := by
  apply lucas_primality 135948553408127407352435831 (11 : ZMod 135948553408127407352435831)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (524065109329, 1), (25941157117327, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (524065109329, 1), (25941157117327, 1)] : List FactorBlock).map factorBlockValue).prod) = 135948553408127407352435831 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_5
      · exact prime_fiftySixBB_524065109329
      · exact prime_fiftySixBB_25941157117327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 135948553408127407352435831) ^ 67974276704063703676217915 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (11 : ZMod 135948553408127407352435831) ^ 27189710681625481470487166 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (11 : ZMod 135948553408127407352435831) ^ 259411571173270 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (11 : ZMod 135948553408127407352435831) ^ 5240651093290 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_215657802963381261826176709 : Nat.Prime 215657802963381261826176709 := by
  apply lucas_primality 215657802963381261826176709 (2 : ZMod 215657802963381261826176709)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (66776672329, 1), (38446881338053, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (66776672329, 1), (38446881338053, 1)] : List FactorBlock).map factorBlockValue).prod) = 215657802963381261826176709 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_7
      · exact prime_fiftySixBB_66776672329
      · exact prime_fiftySixBB_38446881338053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 215657802963381261826176709) ^ 107828901481690630913088354 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 215657802963381261826176709) ^ 71885934321127087275392236 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 215657802963381261826176709) ^ 30808257566197323118025244 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 215657802963381261826176709) ^ 3229538032396452 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 215657802963381261826176709) ^ 5609240475636 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_222919008450363795894398147 : Nat.Prime 222919008450363795894398147 := by
  apply lucas_primality 222919008450363795894398147 (2 : ZMod 222919008450363795894398147)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3847, 1), (2400031, 1), (12071967827583689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3847, 1), (2400031, 1), (12071967827583689, 1)] : List FactorBlock).map factorBlockValue).prod) = 222919008450363795894398147 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3847
      · exact prime_fiftySixBB_2400031
      · exact prime_fiftySixBB_12071967827583689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 222919008450363795894398147) ^ 111459504225181897947199073 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 222919008450363795894398147) ^ 57946194034407017388718 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 222919008450363795894398147) ^ 92881720465428903166 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 222919008450363795894398147) ^ 18465838514 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_275862272957325197419317707 : Nat.Prime 275862272957325197419317707 := by
  apply lucas_primality 275862272957325197419317707 (2 : ZMod 275862272957325197419317707)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (2170603, 1), (9077868255217730393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (2170603, 1), (9077868255217730393, 1)] : List FactorBlock).map factorBlockValue).prod) = 275862272957325197419317707 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_7
      · exact prime_fiftySixBB_2170603
      · exact prime_fiftySixBB_9077868255217730393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 275862272957325197419317707) ^ 137931136478662598709658853 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 275862272957325197419317707) ^ 39408896136760742488473958 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 275862272957325197419317707) ^ 127090155573048225502 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 275862272957325197419317707) ^ 30388442 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_1789376905669136415692871611 : Nat.Prime 1789376905669136415692871611 := by
  apply lucas_primality 1789376905669136415692871611 (2 : ZMod 1789376905669136415692871611)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (2957, 1), (129127, 1), (367781, 1), (920279, 1), (1384601, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (2957, 1), (129127, 1), (367781, 1), (920279, 1), (1384601, 1)] : List FactorBlock).map factorBlockValue).prod) = 1789376905669136415692871611 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_5
      · exact prime_fiftySixBB_2957
      · exact prime_fiftySixBB_129127
      · exact prime_fiftySixBB_367781
      · exact prime_fiftySixBB_920279
      · exact prime_fiftySixBB_1384601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1789376905669136415692871611) ^ 894688452834568207846435805 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1789376905669136415692871611) ^ 357875381133827283138574322 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1789376905669136415692871611) ^ 605132534889799261309730 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1789376905669136415692871611) ^ 13857496152385917861430 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1789376905669136415692871611) ^ 4865332645430667749810 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1789376905669136415692871611) ^ 1944385241507343333590 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (2 : ZMod 1789376905669136415692871611) ^ 1292341191194529265610 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_3678163639431002632257569423 : Nat.Prime 3678163639431002632257569423 := by
  apply lucas_primality 3678163639431002632257569423 (5 : ZMod 3678163639431002632257569423)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (181, 1), (9495361613, 1), (1070066991781687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (181, 1), (9495361613, 1), (1070066991781687, 1)] : List FactorBlock).map factorBlockValue).prod) = 3678163639431002632257569423 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_181
      · exact prime_fiftySixBB_9495361613
      · exact prime_fiftySixBB_1070066991781687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 3678163639431002632257569423) ^ 1839081819715501316128784711 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 3678163639431002632257569423) ^ 20321346074204434432362262 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 3678163639431002632257569423) ^ 387364251024970694 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (5 : ZMod 3678163639431002632257569423) ^ 3437320903906 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_8275868188719755922579531209 : Nat.Prime 8275868188719755922579531209 := by
  apply lucas_primality 8275868188719755922579531209 (6 : ZMod 8275868188719755922579531209)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (157, 1), (40746703, 1), (23101139984032133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (157, 1), (40746703, 1), (23101139984032133, 1)] : List FactorBlock).map factorBlockValue).prod) = 8275868188719755922579531209 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_7
      · exact prime_fiftySixBB_157
      · exact prime_fiftySixBB_40746703
      · exact prime_fiftySixBB_23101139984032133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 8275868188719755922579531209) ^ 4137934094359877961289765604 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (6 : ZMod 8275868188719755922579531209) ^ 1182266884102822274654218744 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (6 : ZMod 8275868188719755922579531209) ^ 52712536233883795685219944 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (6 : ZMod 8275868188719755922579531209) ^ 203105222739610513336 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (6 : ZMod 8275868188719755922579531209) ^ 358245012776 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_66206945509758047380636249609 : Nat.Prime 66206945509758047380636249609 := by
  apply lucas_primality 66206945509758047380636249609 (31 : ZMod 66206945509758047380636249609)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (106379677, 1), (3704551212047837153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (106379677, 1), (3704551212047837153, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249609 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_3
      · exact prime_fiftySixBB_7
      · exact prime_fiftySixBB_106379677
      · exact prime_fiftySixBB_3704551212047837153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (31 : ZMod 66206945509758047380636249609) ^ 33103472754879023690318124804 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (31 : ZMod 66206945509758047380636249609) ^ 22068981836586015793545416536 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (31 : ZMod 66206945509758047380636249609) ^ 9458135072822578197233749944 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (31 : ZMod 66206945509758047380636249609) ^ 622364603624036641704 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (31 : ZMod 66206945509758047380636249609) ^ 17871785736 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem prime_fiftySixBB_66206945509758047380636249631 : Nat.Prime 66206945509758047380636249631 := by
  apply lucas_primality 66206945509758047380636249631 (7 : ZMod 66206945509758047380636249631)
  · rw [← fiftySixBBFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (79, 1), (131, 1), (461, 1), (1387727643836568978667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (79, 1), (131, 1), (461, 1), (1387727643836568978667, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249631 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_fiftySixBB_2
      · exact prime_fiftySixBB_5
      · exact prime_fiftySixBB_79
      · exact prime_fiftySixBB_131
      · exact prime_fiftySixBB_461
      · exact prime_fiftySixBB_1387727643836568978667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 66206945509758047380636249631) ^ 33103472754879023690318124815 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 66206945509758047380636249631) ^ 13241389101951609476127249926 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 66206945509758047380636249631) ^ 838062601389342371906787970 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 66206945509758047380636249631) ^ 505396530608840056340734730 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 66206945509758047380636249631) ^ 143615933860646523602247830 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide
    · change (7 : ZMod 66206945509758047380636249631) ^ 47708890 ≠ 1
      rw [← fiftySixBBFastPow_eq_pow]
      decide

private theorem phi_fiftySixBB_66206945509758047380636249600 : Nat.totient 66206945509758047380636249600 = 26214413889179480527171584000 := by
  rw [← show ((([(2, 9), (5, 2), (151, 1), (283, 1), (1155703, 1), (104733100103693, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249600 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_2, prime_fiftySixBB_5, prime_fiftySixBB_151, prime_fiftySixBB_283, prime_fiftySixBB_1155703, prime_fiftySixBB_104733100103693]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249601 : Nat.totient 66206945509758047380636249601 = 52449134739280926285907008000 := by
  rw [← show ((([(7, 1), (19, 1), (41, 1), (51203, 1), (145679, 1), (216071, 1), (7533195071, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249601 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_7, prime_fiftySixBB_19, prime_fiftySixBB_41, prime_fiftySixBB_51203, prime_fiftySixBB_145679, prime_fiftySixBB_216071, prime_fiftySixBB_7533195071]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249602 : Nat.totient 66206945509758047380636249602 = 21606217959697307210024815680 := by
  rw [← show ((([(2, 1), (3, 1), (67, 1), (163, 1), (5138383, 1), (178266971, 1), (1103043239, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249602 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_2, prime_fiftySixBB_3, prime_fiftySixBB_67, prime_fiftySixBB_163, prime_fiftySixBB_5138383, prime_fiftySixBB_178266971, prime_fiftySixBB_1103043239]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249603 : Nat.totient 66206945509758047380636249603 = 65082052670635614659549890248 := by
  rw [← show ((([(59, 1), (23743, 1), (47262419189211912150119, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249603 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_59, prime_fiftySixBB_23743, prime_fiftySixBB_47262419189211912150119]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249604 : Nat.totient 66206945509758047380636249604 = 28785577931144632365802594560 := by
  rw [← show ((([(2, 2), (11, 1), (23, 1), (581687, 1), (27031369, 1), (4160692695739, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249604 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_2, prime_fiftySixBB_11, prime_fiftySixBB_23, prime_fiftySixBB_581687, prime_fiftySixBB_27031369, prime_fiftySixBB_4160692695739]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249605 : Nat.totient 66206945509758047380636249605 = 32939190380676340280119541760 := by
  rw [← show ((([(3, 3), (5, 1), (17, 1), (113, 1), (114682684871, 1), (2226099472853, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249605 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_3, prime_fiftySixBB_5, prime_fiftySixBB_17, prime_fiftySixBB_113, prime_fiftySixBB_114682684871, prime_fiftySixBB_2226099472853]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249606 : Nat.totient 66206945509758047380636249606 = 32382989970092309428198133760 := by
  rw [← show ((([(2, 1), (47, 1), (2017, 1), (357661, 1), (976333550724236977, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249606 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_2, prime_fiftySixBB_47, prime_fiftySixBB_2017, prime_fiftySixBB_357661, prime_fiftySixBB_976333550724236977]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249607 : Nat.totient 66206945509758047380636249607 = 64417568604088910964943377960 := by
  rw [← show ((([(37, 1), (1789376905669136415692871611, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249607 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_37, prime_fiftySixBB_1789376905669136415692871611]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249608 : Nat.totient 66206945509758047380636249608 = 18916269967826698211065092096 := by
  rw [← show ((([(2, 3), (3, 1), (7, 1), (106379677, 1), (3704551212047837153, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249608 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_2, prime_fiftySixBB_3, prime_fiftySixBB_7, prime_fiftySixBB_106379677, prime_fiftySixBB_3704551212047837153]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249609 : Nat.totient 66206945509758047380636249609 = 66206945509758047380636249608 := by
  rw [← show ((([(66206945509758047380636249609, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249609 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_66206945509758047380636249609]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249610 : Nat.totient 66206945509758047380636249610 = 24444495350384520594538266624 := by
  rw [← show ((([(2, 1), (5, 1), (13, 1), (38707, 1), (61057, 1), (214147, 1), (1006290171149, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249610 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_2, prime_fiftySixBB_5, prime_fiftySixBB_13, prime_fiftySixBB_38707, prime_fiftySixBB_61057, prime_fiftySixBB_214147, prime_fiftySixBB_1006290171149]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249611 : Nat.totient 66206945509758047380636249611 = 44136534380776384253529248000 := by
  rw [← show ((([(3, 1), (30881, 1), (93233501927, 1), (7665119763551, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249611 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_3, prime_fiftySixBB_30881, prime_fiftySixBB_93233501927, prime_fiftySixBB_7665119763551]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249612 : Nat.totient 66206945509758047380636249612 = 33086487904825211979856182416 := by
  rw [← show ((([(2, 2), (1949, 1), (8492425026905855230969247, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249612 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_2, prime_fiftySixBB_1949, prime_fiftySixBB_8492425026905855230969247]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249613 : Nat.totient 66206945509758047380636249613 = 66096781551963209514319552800 := by
  rw [← show ((([(601, 1), (24934747, 1), (4417983747923694479, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249613 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_601, prime_fiftySixBB_24934747, prime_fiftySixBB_4417983747923694479]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249614 : Nat.totient 66206945509758047380636249614 = 22068981836586015793545416532 := by
  rw [← show ((([(2, 1), (3, 2), (3678163639431002632257569423, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249614 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_2, prime_fiftySixBB_3, prime_fiftySixBB_3678163639431002632257569423]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249615 : Nat.totient 66206945509758047380636249615 = 41271860523351998617484803200 := by
  rw [← show ((([(5, 1), (7, 1), (11, 1), (32646343, 1), (118781783, 1), (44346407471, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249615 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_5, prime_fiftySixBB_7, prime_fiftySixBB_11, prime_fiftySixBB_32646343, prime_fiftySixBB_118781783, prime_fiftySixBB_44346407471]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249616 : Nat.totient 66206945509758047380636249616 = 33091729770574348619835548832 := by
  rw [← show ((([(2, 4), (2819, 1), (1467873038084383810319179, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249616 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_2, prime_fiftySixBB_2819, prime_fiftySixBB_1467873038084383810319179]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249617 : Nat.totient 66206945509758047380636249617 = 42711277540574667759411398400 := by
  rw [← show ((([(3, 1), (31, 1), (14827, 1), (2571178417, 1), (18673903145791, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249617 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_3, prime_fiftySixBB_31, prime_fiftySixBB_14827, prime_fiftySixBB_2571178417, prime_fiftySixBB_18673903145791]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249618 : Nat.totient 66206945509758047380636249618 = 33103215866760889441915699200 := by
  rw [← show ((([(2, 1), (128873, 1), (1727404801, 1), (148702234825633, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249618 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_2, prime_fiftySixBB_128873, prime_fiftySixBB_1727404801, prime_fiftySixBB_148702234825633]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249619 : Nat.totient 66206945509758047380636249619 = 66206945506447994349024804000 := by
  rw [← show ((([(20001778001, 1), (3310053011609667619, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249619 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_20001778001, prime_fiftySixBB_3310053011609667619]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249620 : Nat.totient 66206945509758047380636249620 = 16712680062126290426956450944 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (19, 1), (1259, 1), (46128886410655942045787, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249620 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_2, prime_fiftySixBB_3, prime_fiftySixBB_5, prime_fiftySixBB_19, prime_fiftySixBB_1259, prime_fiftySixBB_46128886410655942045787]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249621 : Nat.totient 66206945509758047380636249621 = 63785882707546741708193218992 := by
  rw [← show ((([(29, 1), (463, 1), (4930881470898789556910423, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249621 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_29, prime_fiftySixBB_463, prime_fiftySixBB_4930881470898789556910423]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249622 : Nat.totient 66206945509758047380636249622 = 26705014162699271274346521600 := by
  rw [← show ((([(2, 1), (7, 1), (17, 1), (86599, 1), (1595739571, 1), (2013036748361, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249622 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_2, prime_fiftySixBB_7, prime_fiftySixBB_17, prime_fiftySixBB_86599, prime_fiftySixBB_1595739571, prime_fiftySixBB_2013036748361]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249623 : Nat.totient 66206945509758047380636249623 = 40443560807076720732099796992 := by
  rw [← show ((([(3, 2), (13, 1), (139, 1), (6673, 1), (610072944166959921377, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249623 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_3, prime_fiftySixBB_13, prime_fiftySixBB_139, prime_fiftySixBB_6673, prime_fiftySixBB_610072944166959921377]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249624 : Nat.totient 66206945509758047380636249624 = 33103472754873428975495958432 := by
  rw [← show ((([(2, 3), (5942163459247, 1), (1392736542082349, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249624 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_2, prime_fiftySixBB_5942163459247, prime_fiftySixBB_1392736542082349]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249625 : Nat.totient 66206945509758047380636249625 = 52714494288991278567869472000 := by
  rw [← show ((([(5, 3), (211, 1), (1319167, 1), (93899453, 1), (20265076277, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249625 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_5, prime_fiftySixBB_211, prime_fiftySixBB_1319167, prime_fiftySixBB_93899453, prime_fiftySixBB_20265076277]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249626 : Nat.totient 66206945509758047380636249626 = 19592979522170378691421716480 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (43, 1), (9413, 1), (18307, 1), (4404193, 1), (30738281129, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249626 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_2, prime_fiftySixBB_3, prime_fiftySixBB_11, prime_fiftySixBB_43, prime_fiftySixBB_9413, prime_fiftySixBB_18307, prime_fiftySixBB_4404193, prime_fiftySixBB_30738281129]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249627 : Nat.totient 66206945509758047380636249627 = 62903359959029912374514074624 := by
  rw [← show ((([(23, 1), (149, 1), (1332086172569, 1), (14502975966929, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249627 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_23, prime_fiftySixBB_149, prime_fiftySixBB_1332086172569, prime_fiftySixBB_14502975966929]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249628 : Nat.totient 66206945509758047380636249628 = 33101841969430899281044635648 := by
  rw [← show ((([(2, 2), (29363, 1), (70529, 1), (972029, 1), (8222354312929, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249628 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_2, prime_fiftySixBB_29363, prime_fiftySixBB_70529, prime_fiftySixBB_972029, prime_fiftySixBB_8222354312929]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249629 : Nat.totient 66206945509758047380636249629 = 37831786309579742401848901632 := by
  rw [← show ((([(3, 1), (7, 1), (50177, 1), (62831809214198923791337, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249629 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_3, prime_fiftySixBB_7, prime_fiftySixBB_50177, prime_fiftySixBB_62831809214198923791337]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249630 : Nat.totient 66206945509758047380636249630 = 25891667287645169376358761600 := by
  rw [← show ((([(2, 1), (5, 1), (79, 1), (131, 1), (461, 1), (1387727643836568978667, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249630 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_2, prime_fiftySixBB_5, prime_fiftySixBB_79, prime_fiftySixBB_131, prime_fiftySixBB_461, prime_fiftySixBB_1387727643836568978667]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249631 : Nat.totient 66206945509758047380636249631 = 66206945509758047380636249630 := by
  rw [← show ((([(66206945509758047380636249631, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249631 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_66206945509758047380636249631]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249632 : Nat.totient 66206945509758047380636249632 = 22009815665273936571069726720 := by
  rw [← show ((([(2, 5), (3, 4), (373, 1), (249193476541, 1), (274804002497, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249632 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_2, prime_fiftySixBB_3, prime_fiftySixBB_373, prime_fiftySixBB_249193476541, prime_fiftySixBB_274804002497]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249633 : Nat.totient 66206945509758047380636249633 = 66084566682568106442779250480 := by
  rw [← show ((([(541, 1), (122378827189940937856998613, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249633 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_541, prime_fiftySixBB_122378827189940937856998613]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249634 : Nat.totient 66206945509758047380636249634 = 32649994379334424271770092672 := by
  rw [← show ((([(2, 1), (73, 1), (6989579, 1), (22138973, 1), (2930503252087, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249634 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_2, prime_fiftySixBB_73, prime_fiftySixBB_6989579, prime_fiftySixBB_22138973, prime_fiftySixBB_2930503252087]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249635 : Nat.totient 66206945509758047380636249635 = 35310370938376321976459555328 := by
  rw [← show ((([(3, 1), (5, 1), (218909072497, 1), (20162692742566397, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249635 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_3, prime_fiftySixBB_5, prime_fiftySixBB_218909072497, prime_fiftySixBB_20162692742566397]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249636 : Nat.totient 66206945509758047380636249636 = 25697245681693586517696571392 := by
  rw [← show ((([(2, 2), (7, 1), (13, 1), (53, 2), (78277, 1), (45551269, 1), (18159997147, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249636 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_2, prime_fiftySixBB_7, prime_fiftySixBB_13, prime_fiftySixBB_53, prime_fiftySixBB_78277, prime_fiftySixBB_45551269, prime_fiftySixBB_18159997147]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249637 : Nat.totient 66206945509758047380636249637 = 59462974061338005314481617160 := by
  rw [← show ((([(11, 2), (83, 1), (6592347456911087063689759, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249637 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_11, prime_fiftySixBB_83, prime_fiftySixBB_6592347456911087063689759]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249638 : Nat.totient 66206945509758047380636249638 = 22068981674936341060027891968 := by
  rw [← show ((([(2, 1), (3, 1), (219634633, 1), (361725197, 1), (138890556173, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249638 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_2, prime_fiftySixBB_3, prime_fiftySixBB_219634633, prime_fiftySixBB_361725197, prime_fiftySixBB_138890556173]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249639 : Nat.totient 66206945509758047380636249639 = 59031913918521013853981939712 := by
  rw [← show ((([(17, 1), (19, 1), (65543, 1), (15973147, 1), (195787168385233, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249639 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_17, prime_fiftySixBB_19, prime_fiftySixBB_65543, prime_fiftySixBB_15973147, prime_fiftySixBB_195787168385233]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249640 : Nat.totient 66206945509758047380636249640 = 26424980990394090144954101760 := by
  rw [← show ((([(2, 3), (5, 1), (859, 1), (983, 1), (455381, 1), (4304492668989713, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249640 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_2, prime_fiftySixBB_5, prime_fiftySixBB_859, prime_fiftySixBB_983, prime_fiftySixBB_455381, prime_fiftySixBB_4304492668989713]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249641 : Nat.totient 66206945509758047380636249641 = 44137961932375613323565510400 := by
  rw [← show ((([(3, 2), (27036833, 1), (407861903, 1), (667101754351, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249641 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_3, prime_fiftySixBB_27036833, prime_fiftySixBB_407861903, prime_fiftySixBB_667101754351]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249642 : Nat.totient 66206945509758047380636249642 = 32251967511577132808499978240 := by
  rw [← show ((([(2, 1), (41, 1), (967, 1), (3137, 1), (76919, 1), (28709383, 1), (120528907, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249642 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_2, prime_fiftySixBB_41, prime_fiftySixBB_967, prime_fiftySixBB_3137, prime_fiftySixBB_76919, prime_fiftySixBB_28709383, prime_fiftySixBB_120528907]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249643 : Nat.totient 66206945509758047380636249643 = 56706105389660127441084351888 := by
  rw [← show ((([(7, 2), (1459, 1), (14887, 1), (62207821345309824479, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249643 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_7, prime_fiftySixBB_1459, prime_fiftySixBB_14887, prime_fiftySixBB_62207821345309824479]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249644 : Nat.totient 66206945509758047380636249644 = 21193067325138216148795392000 := by
  rw [← show ((([(2, 2), (3, 1), (37, 1), (127, 1), (193, 1), (38016983041, 1), (160022813851, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249644 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_2, prime_fiftySixBB_3, prime_fiftySixBB_37, prime_fiftySixBB_127, prime_fiftySixBB_193, prime_fiftySixBB_38016983041, prime_fiftySixBB_160022813851]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249645 : Nat.totient 66206945509758047380636249645 = 52217289571413020924107577920 := by
  rw [← show ((([(5, 1), (71, 1), (22973, 1), (8118157752825337199963, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249645 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_5, prime_fiftySixBB_71, prime_fiftySixBB_22973, prime_fiftySixBB_8118157752825337199963]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249646 : Nat.totient 66206945509758047380636249646 = 32955014492686467236010848256 := by
  rw [← show ((([(2, 1), (223, 1), (2713457, 1), (651269809, 1), (84001067177, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249646 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_2, prime_fiftySixBB_223, prime_fiftySixBB_2713457, prime_fiftySixBB_651269809, prime_fiftySixBB_84001067177]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249647 : Nat.totient 66206945509758047380636249647 = 44134602782871035721993449472 := by
  rw [← show ((([(3, 1), (13163, 1), (6007609, 1), (130167463, 1), (2143992769, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249647 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_3, prime_fiftySixBB_13163, prime_fiftySixBB_6007609, prime_fiftySixBB_130167463, prime_fiftySixBB_2143992769]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249648 : Nat.totient 66206945509758047380636249648 = 29123289702124690121950176000 := by
  rw [← show ((([(2, 4), (11, 1), (31, 1), (261073973, 1), (46479945701182171, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249648 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_2, prime_fiftySixBB_11, prime_fiftySixBB_31, prime_fiftySixBB_261073973, prime_fiftySixBB_46479945701182171]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249649 : Nat.totient 66206945509758047380636249649 = 60968177010790088347700977728 := by
  rw [← show ((([(13, 2), (419, 1), (877397, 1), (1065630590924394647, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249649 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_13, prime_fiftySixBB_419, prime_fiftySixBB_877397, prime_fiftySixBB_1065630590924394647]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249650 : Nat.totient 66206945509758047380636249650 = 13746805299587518638391296000 := by
  rw [← show ((([(2, 1), (3, 2), (5, 2), (7, 1), (23, 1), (29, 1), (61, 1), (66253633, 1), (7797001747441, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249650 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_2, prime_fiftySixBB_3, prime_fiftySixBB_5, prime_fiftySixBB_7, prime_fiftySixBB_23, prime_fiftySixBB_29, prime_fiftySixBB_61, prime_fiftySixBB_66253633, prime_fiftySixBB_7797001747441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249651 : Nat.totient 66206945509758047380636249651 = 65971333549891601990257532160 := by
  rw [← show ((([(281, 1), (1218582427, 1), (193349174014205873, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249651 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_281, prime_fiftySixBB_1218582427, prime_fiftySixBB_193349174014205873]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249652 : Nat.totient 66206945509758047380636249652 = 33103466089764985205061797088 := by
  rw [← show ((([(2, 2), (4967827, 1), (25733689453, 1), (129471756923, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249652 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_2, prime_fiftySixBB_4967827, prime_fiftySixBB_25733689453, prime_fiftySixBB_129471756923]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249653 : Nat.totient 66206945509758047380636249653 = 43018109703007869831341483200 := by
  rw [← show ((([(3, 1), (47, 2), (239, 1), (41801193361857475018601, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249653 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_3, prime_fiftySixBB_47, prime_fiftySixBB_239, prime_fiftySixBB_41801193361857475018601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249654 : Nat.totient 66206945509758047380636249654 = 33047649023420543043285547296 := by
  rw [← show ((([(2, 1), (593, 1), (55823731458480647032576939, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249654 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_2, prime_fiftySixBB_593, prime_fiftySixBB_55823731458480647032576939]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249655 : Nat.totient 66206945509758047380636249655 = 52965556407715608146459700000 := by
  rw [← show ((([(5, 1), (583144971181, 1), (22706856367353751, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249655 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_5, prime_fiftySixBB_583144971181, prime_fiftySixBB_22706856367353751]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249656 : Nat.totient 66206945509758047380636249656 = 20770802247761726338177597440 := by
  rw [← show ((([(2, 3), (3, 1), (17, 1), (4988713, 1), (922196281, 1), (35272115069, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249656 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_2, prime_fiftySixBB_3, prime_fiftySixBB_17, prime_fiftySixBB_4988713, prime_fiftySixBB_922196281, prime_fiftySixBB_35272115069]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249657 : Nat.totient 66206945509758047380636249657 = 56498841605174455435733714880 := by
  rw [← show ((([(7, 1), (229, 1), (26189, 1), (1577070521261648103071, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249657 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_7, prime_fiftySixBB_229, prime_fiftySixBB_26189, prime_fiftySixBB_1577070521261648103071]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249658 : Nat.totient 66206945509758047380636249658 = 31359822200668934396515929600 := by
  rw [← show ((([(2, 1), (19, 1), (23027, 1), (53744533, 1), (1407823793269601, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249658 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_2, prime_fiftySixBB_19, prime_fiftySixBB_23027, prime_fiftySixBB_53744533, prime_fiftySixBB_1407823793269601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249659 : Nat.totient 66206945509758047380636249659 = 40125421521065483260991666280 := by
  rw [← show ((([(3, 3), (11, 1), (222919008450363795894398147, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249659 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_3, prime_fiftySixBB_11, prime_fiftySixBB_222919008450363795894398147]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249660 : Nat.totient 66206945509758047380636249660 = 26208968347129297351628869632 := by
  rw [← show ((([(2, 2), (5, 1), (97, 1), (33113, 1), (1030631217342895000603, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249660 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_2, prime_fiftySixBB_5, prime_fiftySixBB_97, prime_fiftySixBB_33113, prime_fiftySixBB_1030631217342895000603]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249661 : Nat.totient 66206945509758047380636249661 = 66206899798612765566600885120 := by
  rw [← show ((([(1448411, 1), (66571457767, 1), (686631416353, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249661 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_1448411, prime_fiftySixBB_66571457767, prime_fiftySixBB_686631416353]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249662 : Nat.totient 66206945509758047380636249662 = 19966575711605298862035511296 := by
  rw [← show ((([(2, 1), (3, 1), (13, 1), (59, 1), (337, 1), (221567, 1), (192673487897095589, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249662 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_2, prime_fiftySixBB_3, prime_fiftySixBB_13, prime_fiftySixBB_59, prime_fiftySixBB_337, prime_fiftySixBB_221567, prime_fiftySixBB_192673487897095589]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249663 : Nat.totient 66206945509758047380636249663 = 65991287706794666118810072648 := by
  rw [← show ((([(307, 1), (215657802963381261826176709, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249663 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_307, prime_fiftySixBB_215657802963381261826176709]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249664 : Nat.totient 66206945509758047380636249664 = 28193675830883358412890544128 := by
  rw [← show ((([(2, 6), (7, 1), (157, 1), (40746703, 1), (23101139984032133, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249664 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_2, prime_fiftySixBB_7, prime_fiftySixBB_157, prime_fiftySixBB_40746703, prime_fiftySixBB_23101139984032133]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249665 : Nat.totient 66206945509758047380636249665 = 35310370885657868298072638592 := by
  rw [← show ((([(3, 1), (5, 1), (667748359, 1), (6609969620782255129, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249665 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_3, prime_fiftySixBB_5, prime_fiftySixBB_667748359, prime_fiftySixBB_6609969620782255129]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249666 : Nat.totient 66206945509758047380636249666 = 33101456831807659033860504240 := by
  rw [← show ((([(2, 1), (16421, 1), (2015923071364656457604173, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249666 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_2, prime_fiftySixBB_16421, prime_fiftySixBB_2015923071364656457604173]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249667 : Nat.totient 66206945509758047380636249667 = 66191644621033813951613680920 := by
  rw [← show ((([(4327, 1), (15300888724233429022564421, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249667 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_4327, prime_fiftySixBB_15300888724233429022564421]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249668 : Nat.totient 66206945509758047380636249668 = 22064187358672353830522648880 := by
  rw [← show ((([(2, 2), (3, 2), (4603, 1), (399539826138496918559371, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249668 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_2, prime_fiftySixBB_3, prime_fiftySixBB_4603, prime_fiftySixBB_399539826138496918559371]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249669 : Nat.totient 66206945509758047380636249669 = 63106719589857054421176672960 := by
  rw [← show ((([(43, 1), (67, 1), (107, 1), (228285181, 1), (940803220869947, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249669 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_43, prime_fiftySixBB_67, prime_fiftySixBB_107, prime_fiftySixBB_228285181, prime_fiftySixBB_940803220869947]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249670 : Nat.totient 66206945509758047380636249670 = 24075249279736124159419680000 := by
  rw [← show ((([(2, 1), (5, 1), (11, 1), (6627001, 1), (90822579144922755997, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249670 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_2, prime_fiftySixBB_5, prime_fiftySixBB_11, prime_fiftySixBB_6627001, prime_fiftySixBB_90822579144922755997]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249671 : Nat.totient 66206945509758047380636249671 = 37612496860180510733134645248 := by
  rw [← show ((([(3, 1), (7, 1), (173, 1), (27763, 1), (11037937, 1), (59468070831677, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249671 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_3, prime_fiftySixBB_7, prime_fiftySixBB_173, prime_fiftySixBB_27763, prime_fiftySixBB_11037937, prime_fiftySixBB_59468070831677]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249672 : Nat.totient 66206945509758047380636249672 = 33103472754879023690318124832 := by
  rw [← show ((([(2, 3), (8275868188719755922579531209, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249672 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_2, prime_fiftySixBB_8275868188719755922579531209]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249673 : Nat.totient 66206945509758047380636249673 = 59503679201149528589568969216 := by
  rw [← show ((([(17, 1), (23, 1), (599, 1), (282683182583752321134697, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249673 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_17, prime_fiftySixBB_23, prime_fiftySixBB_599, prime_fiftySixBB_282683182583752321134697]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249674 : Nat.totient 66206945509758047380636249674 = 22066071472136005290568099200 := by
  rw [← show ((([(2, 1), (3, 1), (7603, 1), (2866901, 1), (506237852249668793, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249674 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_2, prime_fiftySixBB_3, prime_fiftySixBB_7603, prime_fiftySixBB_2866901, prime_fiftySixBB_506237852249668793]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249675 : Nat.totient 66206945509758047380636249675 = 48891272938363222795817312640 := by
  rw [← show ((([(5, 2), (13, 1), (4938707, 1), (41248383127722139157, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249675 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_5, prime_fiftySixBB_13, prime_fiftySixBB_4938707, prime_fiftySixBB_41248383127722139157]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249676 : Nat.totient 66206945509758047380636249676 = 33103344481949068951415343552 := by
  rw [← show ((([(2, 2), (260453, 1), (28213219, 1), (2252483178934717, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249676 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_2, prime_fiftySixBB_260453, prime_fiftySixBB_28213219, prime_fiftySixBB_2252483178934717]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249677 : Nat.totient 66206945509758047380636249677 = 41597801998094301292855138176 := by
  rw [← show ((([(3, 2), (19, 1), (197, 1), (13103, 1), (24799, 1), (6048341521768043, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249677 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_3, prime_fiftySixBB_19, prime_fiftySixBB_197, prime_fiftySixBB_13103, prime_fiftySixBB_24799, prime_fiftySixBB_6048341521768043]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249678 : Nat.totient 66206945509758047380636249678 = 28128570464961606474991497600 := by
  rw [← show ((([(2, 1), (7, 1), (271, 1), (293, 1), (631, 1), (94386361719004958389, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249678 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_2, prime_fiftySixBB_7, prime_fiftySixBB_271, prime_fiftySixBB_293, prime_fiftySixBB_631, prime_fiftySixBB_94386361719004958389]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249679 : Nat.totient 66206945509758047380636249679 = 61861879123255130007233376000 := by
  rw [← show ((([(29, 1), (31, 1), (12027451, 1), (205508873, 1), (29794745927, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249679 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_29, prime_fiftySixBB_31, prime_fiftySixBB_12027451, prime_fiftySixBB_205508873, prime_fiftySixBB_29794745927]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249680 : Nat.totient 66206945509758047380636249680 = 17655185469268812634836333184 := by
  rw [← show ((([(2, 4), (3, 1), (5, 1), (275862272957325197419317707, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249680 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_2, prime_fiftySixBB_3, prime_fiftySixBB_5, prime_fiftySixBB_275862272957325197419317707]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249681 : Nat.totient 66206945509758047380636249681 = 58413916090433971037952495360 := by
  rw [← show ((([(11, 1), (37, 1), (397, 1), (2423336687, 1), (169084920951997, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249681 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_11, prime_fiftySixBB_37, prime_fiftySixBB_397, prime_fiftySixBB_2423336687, prime_fiftySixBB_169084920951997]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249682 : Nat.totient 66206945509758047380636249682 = 33086011730313235966743744000 := by
  rw [← show ((([(2, 1), (1951, 1), (71023, 1), (1193161, 1), (200224964144497, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249682 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_2, prime_fiftySixBB_1951, prime_fiftySixBB_71023, prime_fiftySixBB_1193161, prime_fiftySixBB_200224964144497]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249683 : Nat.totient 66206945509758047380636249683 = 43060660402653689428089600000 := by
  rw [← show ((([(3, 1), (41, 1), (56101, 1), (32563365641, 1), (294644644781, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249683 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_3, prime_fiftySixBB_41, prime_fiftySixBB_56101, prime_fiftySixBB_32563365641, prime_fiftySixBB_294644644781]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249684 : Nat.totient 66206945509758047380636249684 = 33103457067018232508419829504 := by
  rw [← show ((([(2, 2), (2110133, 1), (7843930395590947037537, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249684 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_2, prime_fiftySixBB_2110133, prime_fiftySixBB_7843930395590947037537]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249685 : Nat.totient 66206945509758047380636249685 = 45396174443494375633417908480 := by
  rw [← show ((([(5, 1), (7, 1), (15797, 1), (15764043973, 1), (7596145097711, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249685 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_5, prime_fiftySixBB_7, prime_fiftySixBB_15797, prime_fiftySixBB_15764043973, prime_fiftySixBB_7596145097711]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249686 : Nat.totient 66206945509758047380636249686 = 22033329200339511729258579240 := by
  rw [← show ((([(2, 1), (3, 3), (619, 1), (1980702013694670238157011, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249686 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_2, prime_fiftySixBB_3, prime_fiftySixBB_619, prime_fiftySixBB_1980702013694670238157011]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249687 : Nat.totient 66206945509758047380636249687 = 65463044542590021776033249280 := by
  rw [← show ((([(89, 1), (24218543, 1), (30716061827277751681, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249687 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_89, prime_fiftySixBB_24218543, prime_fiftySixBB_30716061827277751681]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249688 : Nat.totient 66206945509758047380636249688 = 30556978958265534205470369792 := by
  rw [← show ((([(2, 3), (13, 1), (421469, 1), (97264499, 1), (15529240709137, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249688 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_2, prime_fiftySixBB_13, prime_fiftySixBB_421469, prime_fiftySixBB_97264499, prime_fiftySixBB_15529240709137]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249689 : Nat.totient 66206945509758047380636249689 = 43288995151212879380655789888 := by
  rw [← show ((([(3, 1), (53, 1), (2677, 1), (155545716738576805869323, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249689 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_3, prime_fiftySixBB_53, prime_fiftySixBB_2677, prime_fiftySixBB_155545716738576805869323]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249690 : Nat.totient 66206945509758047380636249690 = 24921467515208990005045370880 := by
  rw [← show ((([(2, 1), (5, 1), (17, 1), (7121, 1), (54690720495103998431017, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249690 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_2, prime_fiftySixBB_5, prime_fiftySixBB_17, prime_fiftySixBB_7121, prime_fiftySixBB_54690720495103998431017]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249691 : Nat.totient 66206945509758047380636249691 = 66206945508323673291019089672 := by
  rw [← show ((([(46157378413, 1), (1434374043459781607, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249691 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_46157378413, prime_fiftySixBB_1434374043459781607]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249692 : Nat.totient 66206945509758047380636249692 = 17196609223313778540424998240 := by
  rw [← show ((([(2, 2), (3, 1), (7, 2), (11, 1), (10236076918639153893110119, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249692 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_2, prime_fiftySixBB_3, prime_fiftySixBB_7, prime_fiftySixBB_11, prime_fiftySixBB_10236076918639153893110119]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249693 : Nat.totient 66206945509758047380636249693 = 66206945404228806965419999200 := by
  rw [← show ((([(627380101, 1), (105529240414588870393, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249693 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_627380101, prime_fiftySixBB_105529240414588870393]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249694 : Nat.totient 66206945509758047380636249694 = 32781948965256846495980090592 := by
  rw [← show ((([(2, 1), (103, 1), (252727, 1), (28835819, 1), (44101402262573, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249694 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_2, prime_fiftySixBB_103, prime_fiftySixBB_252727, prime_fiftySixBB_28835819, prime_fiftySixBB_44101402262573]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249695 : Nat.totient 66206945509758047380636249695 = 34839425510278242217371648000 := by
  rw [← show ((([(3, 2), (5, 1), (101, 1), (347, 1), (1789, 1), (31657, 1), (741242125656041, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249695 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_3, prime_fiftySixBB_5, prime_fiftySixBB_101, prime_fiftySixBB_347, prime_fiftySixBB_1789, prime_fiftySixBB_31657, prime_fiftySixBB_741242125656041]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249696 : Nat.totient 66206945509758047380636249696 = 29980542762982357285052611584 := by
  rw [← show ((([(2, 5), (19, 1), (23, 1), (1753, 1), (2700786291404912899423, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249696 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_2, prime_fiftySixBB_19, prime_fiftySixBB_23, prime_fiftySixBB_1753, prime_fiftySixBB_2700786291404912899423]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249697 : Nat.totient 66206945509758047380636249697 = 66070996956349919973283813380 := by
  rw [← show ((([(487, 1), (135948553408127407352435831, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249697 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_487, prime_fiftySixBB_135948553408127407352435831]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249698 : Nat.totient 66206945509758047380636249698 = 22056778956714399689379840000 := by
  rw [← show ((([(2, 1), (3, 1), (1861, 1), (64081, 1), (9278554063, 1), (9972323201, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249698 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_2, prime_fiftySixBB_3, prime_fiftySixBB_1861, prime_fiftySixBB_64081, prime_fiftySixBB_9278554063, prime_fiftySixBB_9972323201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249699 : Nat.totient 66206945509758047380636249699 = 56748593242380806060291393280 := by
  rw [← show ((([(7, 1), (261281, 1), (36199092443853851589797, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249699 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_7, prime_fiftySixBB_261281, prime_fiftySixBB_36199092443853851589797]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_fiftySixBB_66206945509758047380636249700 : Nat.totient 66206945509758047380636249700 = 25919314794813543527771856000 := by
  rw [← show ((([(2, 2), (5, 2), (47, 1), (602086141, 1), (23396293639338811, 1)] : List FactorBlock).map factorBlockValue).prod) = 66206945509758047380636249700 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_fiftySixBB_2, prime_fiftySixBB_5, prime_fiftySixBB_47, prime_fiftySixBB_602086141, prime_fiftySixBB_23396293639338811]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64FiftySixBB : certifiedKill 1 66206945509758047380636249599 100 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_fiftySixBB_66206945509758047380636249600, phi_fiftySixBB_66206945509758047380636249601, phi_fiftySixBB_66206945509758047380636249602,
    phi_fiftySixBB_66206945509758047380636249603, phi_fiftySixBB_66206945509758047380636249604, phi_fiftySixBB_66206945509758047380636249605,
    phi_fiftySixBB_66206945509758047380636249606, phi_fiftySixBB_66206945509758047380636249607, phi_fiftySixBB_66206945509758047380636249608,
    phi_fiftySixBB_66206945509758047380636249609, phi_fiftySixBB_66206945509758047380636249610, phi_fiftySixBB_66206945509758047380636249611,
    phi_fiftySixBB_66206945509758047380636249612, phi_fiftySixBB_66206945509758047380636249613, phi_fiftySixBB_66206945509758047380636249614,
    phi_fiftySixBB_66206945509758047380636249615, phi_fiftySixBB_66206945509758047380636249616, phi_fiftySixBB_66206945509758047380636249617,
    phi_fiftySixBB_66206945509758047380636249618, phi_fiftySixBB_66206945509758047380636249619, phi_fiftySixBB_66206945509758047380636249620,
    phi_fiftySixBB_66206945509758047380636249621, phi_fiftySixBB_66206945509758047380636249622, phi_fiftySixBB_66206945509758047380636249623,
    phi_fiftySixBB_66206945509758047380636249624, phi_fiftySixBB_66206945509758047380636249625, phi_fiftySixBB_66206945509758047380636249626,
    phi_fiftySixBB_66206945509758047380636249627, phi_fiftySixBB_66206945509758047380636249628, phi_fiftySixBB_66206945509758047380636249629,
    phi_fiftySixBB_66206945509758047380636249630, phi_fiftySixBB_66206945509758047380636249631, phi_fiftySixBB_66206945509758047380636249632,
    phi_fiftySixBB_66206945509758047380636249633, phi_fiftySixBB_66206945509758047380636249634, phi_fiftySixBB_66206945509758047380636249635,
    phi_fiftySixBB_66206945509758047380636249636, phi_fiftySixBB_66206945509758047380636249637, phi_fiftySixBB_66206945509758047380636249638,
    phi_fiftySixBB_66206945509758047380636249639, phi_fiftySixBB_66206945509758047380636249640, phi_fiftySixBB_66206945509758047380636249641,
    phi_fiftySixBB_66206945509758047380636249642, phi_fiftySixBB_66206945509758047380636249643, phi_fiftySixBB_66206945509758047380636249644,
    phi_fiftySixBB_66206945509758047380636249645, phi_fiftySixBB_66206945509758047380636249646, phi_fiftySixBB_66206945509758047380636249647,
    phi_fiftySixBB_66206945509758047380636249648, phi_fiftySixBB_66206945509758047380636249649, phi_fiftySixBB_66206945509758047380636249650,
    phi_fiftySixBB_66206945509758047380636249651, phi_fiftySixBB_66206945509758047380636249652, phi_fiftySixBB_66206945509758047380636249653,
    phi_fiftySixBB_66206945509758047380636249654, phi_fiftySixBB_66206945509758047380636249655, phi_fiftySixBB_66206945509758047380636249656,
    phi_fiftySixBB_66206945509758047380636249657, phi_fiftySixBB_66206945509758047380636249658, phi_fiftySixBB_66206945509758047380636249659,
    phi_fiftySixBB_66206945509758047380636249660, phi_fiftySixBB_66206945509758047380636249661, phi_fiftySixBB_66206945509758047380636249662,
    phi_fiftySixBB_66206945509758047380636249663, phi_fiftySixBB_66206945509758047380636249664, phi_fiftySixBB_66206945509758047380636249665,
    phi_fiftySixBB_66206945509758047380636249666, phi_fiftySixBB_66206945509758047380636249667, phi_fiftySixBB_66206945509758047380636249668,
    phi_fiftySixBB_66206945509758047380636249669, phi_fiftySixBB_66206945509758047380636249670, phi_fiftySixBB_66206945509758047380636249671,
    phi_fiftySixBB_66206945509758047380636249672, phi_fiftySixBB_66206945509758047380636249673, phi_fiftySixBB_66206945509758047380636249674,
    phi_fiftySixBB_66206945509758047380636249675, phi_fiftySixBB_66206945509758047380636249676, phi_fiftySixBB_66206945509758047380636249677,
    phi_fiftySixBB_66206945509758047380636249678, phi_fiftySixBB_66206945509758047380636249679, phi_fiftySixBB_66206945509758047380636249680,
    phi_fiftySixBB_66206945509758047380636249681, phi_fiftySixBB_66206945509758047380636249682, phi_fiftySixBB_66206945509758047380636249683,
    phi_fiftySixBB_66206945509758047380636249684, phi_fiftySixBB_66206945509758047380636249685, phi_fiftySixBB_66206945509758047380636249686,
    phi_fiftySixBB_66206945509758047380636249687, phi_fiftySixBB_66206945509758047380636249688, phi_fiftySixBB_66206945509758047380636249689,
    phi_fiftySixBB_66206945509758047380636249690, phi_fiftySixBB_66206945509758047380636249691, phi_fiftySixBB_66206945509758047380636249692,
    phi_fiftySixBB_66206945509758047380636249693, phi_fiftySixBB_66206945509758047380636249694, phi_fiftySixBB_66206945509758047380636249695,
    phi_fiftySixBB_66206945509758047380636249696, phi_fiftySixBB_66206945509758047380636249697, phi_fiftySixBB_66206945509758047380636249698,
    phi_fiftySixBB_66206945509758047380636249699, phi_fiftySixBB_66206945509758047380636249700]

end TotientTailPeriodKiller
end Erdos249257
