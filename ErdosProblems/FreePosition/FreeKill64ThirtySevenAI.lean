import Erdos249257.DiagonalPincerCertificatesT64

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def thirtySevenAIFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem thirtySevenAIFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) :
    thirtySevenAIFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [thirtySevenAIFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [thirtySevenAIFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then thirtySevenAIFastPow a n * thirtySevenAIFastPow a n * a
        else thirtySevenAIFastPow a n * thirtySevenAIFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_thirtySevenAI_2 : Nat.Prime 2 := by norm_num
private theorem prime_thirtySevenAI_3 : Nat.Prime 3 := by norm_num
private theorem prime_thirtySevenAI_5 : Nat.Prime 5 := by norm_num
private theorem prime_thirtySevenAI_7 : Nat.Prime 7 := by norm_num
private theorem prime_thirtySevenAI_11 : Nat.Prime 11 := by norm_num
private theorem prime_thirtySevenAI_13 : Nat.Prime 13 := by norm_num
private theorem prime_thirtySevenAI_17 : Nat.Prime 17 := by norm_num
private theorem prime_thirtySevenAI_19 : Nat.Prime 19 := by norm_num
private theorem prime_thirtySevenAI_23 : Nat.Prime 23 := by norm_num
private theorem prime_thirtySevenAI_29 : Nat.Prime 29 := by norm_num
private theorem prime_thirtySevenAI_31 : Nat.Prime 31 := by norm_num
private theorem prime_thirtySevenAI_37 : Nat.Prime 37 := by norm_num
private theorem prime_thirtySevenAI_41 : Nat.Prime 41 := by norm_num
private theorem prime_thirtySevenAI_43 : Nat.Prime 43 := by norm_num
private theorem prime_thirtySevenAI_47 : Nat.Prime 47 := by norm_num
private theorem prime_thirtySevenAI_53 : Nat.Prime 53 := by norm_num
private theorem prime_thirtySevenAI_59 : Nat.Prime 59 := by norm_num
private theorem prime_thirtySevenAI_61 : Nat.Prime 61 := by norm_num
private theorem prime_thirtySevenAI_67 : Nat.Prime 67 := by norm_num
private theorem prime_thirtySevenAI_71 : Nat.Prime 71 := by norm_num
private theorem prime_thirtySevenAI_73 : Nat.Prime 73 := by norm_num
private theorem prime_thirtySevenAI_79 : Nat.Prime 79 := by norm_num
private theorem prime_thirtySevenAI_83 : Nat.Prime 83 := by norm_num
private theorem prime_thirtySevenAI_89 : Nat.Prime 89 := by norm_num
private theorem prime_thirtySevenAI_97 : Nat.Prime 97 := by norm_num
private theorem prime_thirtySevenAI_101 : Nat.Prime 101 := by norm_num
private theorem prime_thirtySevenAI_103 : Nat.Prime 103 := by norm_num
private theorem prime_thirtySevenAI_107 : Nat.Prime 107 := by norm_num
private theorem prime_thirtySevenAI_109 : Nat.Prime 109 := by norm_num
private theorem prime_thirtySevenAI_113 : Nat.Prime 113 := by norm_num
private theorem prime_thirtySevenAI_127 : Nat.Prime 127 := by norm_num
private theorem prime_thirtySevenAI_131 : Nat.Prime 131 := by norm_num
private theorem prime_thirtySevenAI_137 : Nat.Prime 137 := by norm_num
private theorem prime_thirtySevenAI_139 : Nat.Prime 139 := by norm_num
private theorem prime_thirtySevenAI_149 : Nat.Prime 149 := by norm_num
private theorem prime_thirtySevenAI_151 : Nat.Prime 151 := by norm_num
private theorem prime_thirtySevenAI_163 : Nat.Prime 163 := by norm_num
private theorem prime_thirtySevenAI_167 : Nat.Prime 167 := by norm_num
private theorem prime_thirtySevenAI_173 : Nat.Prime 173 := by norm_num
private theorem prime_thirtySevenAI_179 : Nat.Prime 179 := by norm_num
private theorem prime_thirtySevenAI_181 : Nat.Prime 181 := by norm_num
private theorem prime_thirtySevenAI_191 : Nat.Prime 191 := by norm_num
private theorem prime_thirtySevenAI_193 : Nat.Prime 193 := by norm_num
private theorem prime_thirtySevenAI_197 : Nat.Prime 197 := by norm_num
private theorem prime_thirtySevenAI_199 : Nat.Prime 199 := by norm_num
private theorem prime_thirtySevenAI_211 : Nat.Prime 211 := by norm_num
private theorem prime_thirtySevenAI_223 : Nat.Prime 223 := by norm_num
private theorem prime_thirtySevenAI_227 : Nat.Prime 227 := by norm_num
private theorem prime_thirtySevenAI_229 : Nat.Prime 229 := by norm_num
private theorem prime_thirtySevenAI_233 : Nat.Prime 233 := by norm_num
private theorem prime_thirtySevenAI_239 : Nat.Prime 239 := by norm_num
private theorem prime_thirtySevenAI_241 : Nat.Prime 241 := by norm_num
private theorem prime_thirtySevenAI_251 : Nat.Prime 251 := by norm_num
private theorem prime_thirtySevenAI_257 : Nat.Prime 257 := by norm_num
private theorem prime_thirtySevenAI_263 : Nat.Prime 263 := by norm_num
private theorem prime_thirtySevenAI_271 : Nat.Prime 271 := by norm_num
private theorem prime_thirtySevenAI_277 : Nat.Prime 277 := by norm_num
private theorem prime_thirtySevenAI_281 : Nat.Prime 281 := by norm_num
private theorem prime_thirtySevenAI_293 : Nat.Prime 293 := by norm_num
private theorem prime_thirtySevenAI_307 : Nat.Prime 307 := by norm_num
private theorem prime_thirtySevenAI_311 : Nat.Prime 311 := by norm_num
private theorem prime_thirtySevenAI_317 : Nat.Prime 317 := by norm_num
private theorem prime_thirtySevenAI_337 : Nat.Prime 337 := by norm_num
private theorem prime_thirtySevenAI_347 : Nat.Prime 347 := by norm_num
private theorem prime_thirtySevenAI_353 : Nat.Prime 353 := by norm_num
private theorem prime_thirtySevenAI_373 : Nat.Prime 373 := by norm_num
private theorem prime_thirtySevenAI_383 : Nat.Prime 383 := by norm_num
private theorem prime_thirtySevenAI_397 : Nat.Prime 397 := by norm_num
private theorem prime_thirtySevenAI_409 : Nat.Prime 409 := by norm_num
private theorem prime_thirtySevenAI_421 : Nat.Prime 421 := by norm_num
private theorem prime_thirtySevenAI_431 : Nat.Prime 431 := by norm_num
private theorem prime_thirtySevenAI_433 : Nat.Prime 433 := by norm_num
private theorem prime_thirtySevenAI_443 : Nat.Prime 443 := by norm_num
private theorem prime_thirtySevenAI_449 : Nat.Prime 449 := by norm_num
private theorem prime_thirtySevenAI_461 : Nat.Prime 461 := by norm_num
private theorem prime_thirtySevenAI_463 : Nat.Prime 463 := by norm_num
private theorem prime_thirtySevenAI_467 : Nat.Prime 467 := by norm_num
private theorem prime_thirtySevenAI_523 : Nat.Prime 523 := by norm_num
private theorem prime_thirtySevenAI_541 : Nat.Prime 541 := by norm_num
private theorem prime_thirtySevenAI_547 : Nat.Prime 547 := by norm_num
private theorem prime_thirtySevenAI_587 : Nat.Prime 587 := by norm_num
private theorem prime_thirtySevenAI_593 : Nat.Prime 593 := by norm_num
private theorem prime_thirtySevenAI_607 : Nat.Prime 607 := by norm_num
private theorem prime_thirtySevenAI_617 : Nat.Prime 617 := by norm_num
private theorem prime_thirtySevenAI_619 : Nat.Prime 619 := by norm_num
private theorem prime_thirtySevenAI_643 : Nat.Prime 643 := by norm_num
private theorem prime_thirtySevenAI_653 : Nat.Prime 653 := by norm_num
private theorem prime_thirtySevenAI_701 : Nat.Prime 701 := by norm_num
private theorem prime_thirtySevenAI_719 : Nat.Prime 719 := by norm_num
private theorem prime_thirtySevenAI_809 : Nat.Prime 809 := by norm_num
private theorem prime_thirtySevenAI_821 : Nat.Prime 821 := by norm_num
private theorem prime_thirtySevenAI_823 : Nat.Prime 823 := by norm_num
private theorem prime_thirtySevenAI_827 : Nat.Prime 827 := by norm_num
private theorem prime_thirtySevenAI_859 : Nat.Prime 859 := by norm_num
private theorem prime_thirtySevenAI_863 : Nat.Prime 863 := by norm_num
private theorem prime_thirtySevenAI_907 : Nat.Prime 907 := by norm_num
private theorem prime_thirtySevenAI_967 : Nat.Prime 967 := by norm_num
private theorem prime_thirtySevenAI_997 : Nat.Prime 997 := by norm_num
private theorem prime_thirtySevenAI_1009 : Nat.Prime 1009 := by norm_num
private theorem prime_thirtySevenAI_1013 : Nat.Prime 1013 := by norm_num
private theorem prime_thirtySevenAI_1019 : Nat.Prime 1019 := by norm_num
private theorem prime_thirtySevenAI_1021 : Nat.Prime 1021 := by norm_num
private theorem prime_thirtySevenAI_1031 : Nat.Prime 1031 := by norm_num
private theorem prime_thirtySevenAI_1063 : Nat.Prime 1063 := by norm_num
private theorem prime_thirtySevenAI_1103 : Nat.Prime 1103 := by norm_num
private theorem prime_thirtySevenAI_1151 : Nat.Prime 1151 := by norm_num
private theorem prime_thirtySevenAI_1259 : Nat.Prime 1259 := by norm_num
private theorem prime_thirtySevenAI_1277 : Nat.Prime 1277 := by norm_num
private theorem prime_thirtySevenAI_1279 : Nat.Prime 1279 := by norm_num
private theorem prime_thirtySevenAI_1283 : Nat.Prime 1283 := by norm_num
private theorem prime_thirtySevenAI_1291 : Nat.Prime 1291 := by norm_num
private theorem prime_thirtySevenAI_1327 : Nat.Prime 1327 := by norm_num
private theorem prime_thirtySevenAI_1429 : Nat.Prime 1429 := by norm_num
private theorem prime_thirtySevenAI_1483 : Nat.Prime 1483 := by norm_num
private theorem prime_thirtySevenAI_1609 : Nat.Prime 1609 := by norm_num
private theorem prime_thirtySevenAI_1663 : Nat.Prime 1663 := by norm_num
private theorem prime_thirtySevenAI_1759 : Nat.Prime 1759 := by norm_num
private theorem prime_thirtySevenAI_1777 : Nat.Prime 1777 := by norm_num
private theorem prime_thirtySevenAI_1801 : Nat.Prime 1801 := by norm_num
private theorem prime_thirtySevenAI_1867 : Nat.Prime 1867 := by norm_num
private theorem prime_thirtySevenAI_1871 : Nat.Prime 1871 := by norm_num
private theorem prime_thirtySevenAI_1873 : Nat.Prime 1873 := by norm_num
private theorem prime_thirtySevenAI_1879 : Nat.Prime 1879 := by norm_num
private theorem prime_thirtySevenAI_2017 : Nat.Prime 2017 := by norm_num
private theorem prime_thirtySevenAI_2039 : Nat.Prime 2039 := by norm_num
private theorem prime_thirtySevenAI_2179 : Nat.Prime 2179 := by norm_num
private theorem prime_thirtySevenAI_2207 : Nat.Prime 2207 := by norm_num
private theorem prime_thirtySevenAI_2237 : Nat.Prime 2237 := by norm_num
private theorem prime_thirtySevenAI_2243 : Nat.Prime 2243 := by norm_num
private theorem prime_thirtySevenAI_2309 : Nat.Prime 2309 := by norm_num
private theorem prime_thirtySevenAI_2347 : Nat.Prime 2347 := by norm_num
private theorem prime_thirtySevenAI_2371 : Nat.Prime 2371 := by norm_num
private theorem prime_thirtySevenAI_2423 : Nat.Prime 2423 := by norm_num
private theorem prime_thirtySevenAI_2441 : Nat.Prime 2441 := by norm_num
private theorem prime_thirtySevenAI_2473 : Nat.Prime 2473 := by norm_num
private theorem prime_thirtySevenAI_2531 : Nat.Prime 2531 := by norm_num
private theorem prime_thirtySevenAI_2647 : Nat.Prime 2647 := by norm_num
private theorem prime_thirtySevenAI_2707 : Nat.Prime 2707 := by norm_num
private theorem prime_thirtySevenAI_2897 : Nat.Prime 2897 := by norm_num
private theorem prime_thirtySevenAI_2927 : Nat.Prime 2927 := by norm_num
private theorem prime_thirtySevenAI_2953 : Nat.Prime 2953 := by norm_num
private theorem prime_thirtySevenAI_2957 : Nat.Prime 2957 := by norm_num
private theorem prime_thirtySevenAI_3023 : Nat.Prime 3023 := by norm_num
private theorem prime_thirtySevenAI_3067 : Nat.Prime 3067 := by norm_num
private theorem prime_thirtySevenAI_3371 : Nat.Prime 3371 := by norm_num
private theorem prime_thirtySevenAI_3433 : Nat.Prime 3433 := by norm_num
private theorem prime_thirtySevenAI_3539 : Nat.Prime 3539 := by norm_num
private theorem prime_thirtySevenAI_3691 : Nat.Prime 3691 := by norm_num
private theorem prime_thirtySevenAI_3709 : Nat.Prime 3709 := by norm_num
private theorem prime_thirtySevenAI_3733 : Nat.Prime 3733 := by norm_num
private theorem prime_thirtySevenAI_3877 : Nat.Prime 3877 := by norm_num
private theorem prime_thirtySevenAI_3931 : Nat.Prime 3931 := by norm_num
private theorem prime_thirtySevenAI_4021 : Nat.Prime 4021 := by norm_num
private theorem prime_thirtySevenAI_4397 : Nat.Prime 4397 := by norm_num
private theorem prime_thirtySevenAI_4463 : Nat.Prime 4463 := by norm_num
private theorem prime_thirtySevenAI_4663 : Nat.Prime 4663 := by norm_num
private theorem prime_thirtySevenAI_4721 : Nat.Prime 4721 := by norm_num
private theorem prime_thirtySevenAI_5009 : Nat.Prime 5009 := by norm_num
private theorem prime_thirtySevenAI_5107 : Nat.Prime 5107 := by norm_num
private theorem prime_thirtySevenAI_5441 : Nat.Prime 5441 := by norm_num
private theorem prime_thirtySevenAI_5573 : Nat.Prime 5573 := by norm_num
private theorem prime_thirtySevenAI_5591 : Nat.Prime 5591 := by norm_num
private theorem prime_thirtySevenAI_5701 : Nat.Prime 5701 := by norm_num
private theorem prime_thirtySevenAI_5903 : Nat.Prime 5903 := by norm_num
private theorem prime_thirtySevenAI_6047 : Nat.Prime 6047 := by norm_num
private theorem prime_thirtySevenAI_6173 : Nat.Prime 6173 := by norm_num
private theorem prime_thirtySevenAI_6247 : Nat.Prime 6247 := by norm_num
private theorem prime_thirtySevenAI_6361 : Nat.Prime 6361 := by norm_num
private theorem prime_thirtySevenAI_6659 : Nat.Prime 6659 := by norm_num
private theorem prime_thirtySevenAI_6701 : Nat.Prime 6701 := by norm_num
private theorem prime_thirtySevenAI_6763 : Nat.Prime 6763 := by norm_num
private theorem prime_thirtySevenAI_6971 : Nat.Prime 6971 := by norm_num
private theorem prime_thirtySevenAI_7187 : Nat.Prime 7187 := by norm_num
private theorem prime_thirtySevenAI_7253 : Nat.Prime 7253 := by norm_num
private theorem prime_thirtySevenAI_7369 : Nat.Prime 7369 := by norm_num
private theorem prime_thirtySevenAI_7573 : Nat.Prime 7573 := by norm_num
private theorem prime_thirtySevenAI_7703 : Nat.Prime 7703 := by norm_num
private theorem prime_thirtySevenAI_7727 : Nat.Prime 7727 := by norm_num
private theorem prime_thirtySevenAI_7793 : Nat.Prime 7793 := by norm_num
private theorem prime_thirtySevenAI_8419 : Nat.Prime 8419 := by norm_num
private theorem prime_thirtySevenAI_8719 : Nat.Prime 8719 := by norm_num
private theorem prime_thirtySevenAI_8753 : Nat.Prime 8753 := by norm_num
private theorem prime_thirtySevenAI_9157 : Nat.Prime 9157 := by norm_num
private theorem prime_thirtySevenAI_9283 : Nat.Prime 9283 := by norm_num
private theorem prime_thirtySevenAI_9319 : Nat.Prime 9319 := by norm_num
private theorem prime_thirtySevenAI_9719 : Nat.Prime 9719 := by norm_num
private theorem prime_thirtySevenAI_10159 : Nat.Prime 10159 := by norm_num
private theorem prime_thirtySevenAI_10631 : Nat.Prime 10631 := by norm_num
private theorem prime_thirtySevenAI_10889 : Nat.Prime 10889 := by norm_num
private theorem prime_thirtySevenAI_10903 : Nat.Prime 10903 := by norm_num
private theorem prime_thirtySevenAI_11579 : Nat.Prime 11579 := by norm_num
private theorem prime_thirtySevenAI_11717 : Nat.Prime 11717 := by norm_num
private theorem prime_thirtySevenAI_12409 : Nat.Prime 12409 := by norm_num
private theorem prime_thirtySevenAI_12437 : Nat.Prime 12437 := by norm_num
private theorem prime_thirtySevenAI_12527 : Nat.Prime 12527 := by norm_num
private theorem prime_thirtySevenAI_12703 : Nat.Prime 12703 := by norm_num
private theorem prime_thirtySevenAI_13009 : Nat.Prime 13009 := by norm_num
private theorem prime_thirtySevenAI_13441 : Nat.Prime 13441 := by norm_num
private theorem prime_thirtySevenAI_14321 : Nat.Prime 14321 := by norm_num
private theorem prime_thirtySevenAI_16433 : Nat.Prime 16433 := by norm_num
private theorem prime_thirtySevenAI_16883 : Nat.Prime 16883 := by norm_num
private theorem prime_thirtySevenAI_17099 : Nat.Prime 17099 := by norm_num
private theorem prime_thirtySevenAI_17623 : Nat.Prime 17623 := by norm_num
private theorem prime_thirtySevenAI_17939 : Nat.Prime 17939 := by norm_num
private theorem prime_thirtySevenAI_19163 : Nat.Prime 19163 := by norm_num
private theorem prime_thirtySevenAI_21031 : Nat.Prime 21031 := by norm_num
private theorem prime_thirtySevenAI_21061 : Nat.Prime 21061 := by norm_num
private theorem prime_thirtySevenAI_21319 : Nat.Prime 21319 := by norm_num
private theorem prime_thirtySevenAI_21737 : Nat.Prime 21737 := by norm_num
private theorem prime_thirtySevenAI_22027 : Nat.Prime 22027 := by norm_num
private theorem prime_thirtySevenAI_22109 : Nat.Prime 22109 := by norm_num
private theorem prime_thirtySevenAI_24239 : Nat.Prime 24239 := by norm_num
private theorem prime_thirtySevenAI_26113 : Nat.Prime 26113 := by norm_num
private theorem prime_thirtySevenAI_27197 : Nat.Prime 27197 := by norm_num
private theorem prime_thirtySevenAI_27407 : Nat.Prime 27407 := by norm_num
private theorem prime_thirtySevenAI_27427 : Nat.Prime 27427 := by norm_num
private theorem prime_thirtySevenAI_28151 : Nat.Prime 28151 := by norm_num
private theorem prime_thirtySevenAI_28949 : Nat.Prime 28949 := by norm_num
private theorem prime_thirtySevenAI_32497 : Nat.Prime 32497 := by norm_num
private theorem prime_thirtySevenAI_34337 : Nat.Prime 34337 := by norm_num
private theorem prime_thirtySevenAI_35279 : Nat.Prime 35279 := by norm_num
private theorem prime_thirtySevenAI_35423 : Nat.Prime 35423 := by norm_num
private theorem prime_thirtySevenAI_35923 : Nat.Prime 35923 := by norm_num
private theorem prime_thirtySevenAI_36947 : Nat.Prime 36947 := by norm_num
private theorem prime_thirtySevenAI_37309 : Nat.Prime 37309 := by norm_num
private theorem prime_thirtySevenAI_37321 : Nat.Prime 37321 := by norm_num
private theorem prime_thirtySevenAI_37397 : Nat.Prime 37397 := by norm_num
private theorem prime_thirtySevenAI_38119 : Nat.Prime 38119 := by norm_num
private theorem prime_thirtySevenAI_38351 : Nat.Prime 38351 := by norm_num
private theorem prime_thirtySevenAI_39019 : Nat.Prime 39019 := by norm_num
private theorem prime_thirtySevenAI_42013 : Nat.Prime 42013 := by norm_num
private theorem prime_thirtySevenAI_43189 : Nat.Prime 43189 := by norm_num
private theorem prime_thirtySevenAI_44533 : Nat.Prime 44533 := by norm_num
private theorem prime_thirtySevenAI_46447 : Nat.Prime 46447 := by norm_num
private theorem prime_thirtySevenAI_46589 : Nat.Prime 46589 := by norm_num
private theorem prime_thirtySevenAI_52609 : Nat.Prime 52609 := by norm_num
private theorem prime_thirtySevenAI_54311 : Nat.Prime 54311 := by norm_num
private theorem prime_thirtySevenAI_56611 : Nat.Prime 56611 := by norm_num
private theorem prime_thirtySevenAI_57713 : Nat.Prime 57713 := by norm_num
private theorem prime_thirtySevenAI_58043 : Nat.Prime 58043 := by norm_num
private theorem prime_thirtySevenAI_58711 : Nat.Prime 58711 := by norm_num
private theorem prime_thirtySevenAI_60013 : Nat.Prime 60013 := by norm_num
private theorem prime_thirtySevenAI_60761 : Nat.Prime 60761 := by norm_num
private theorem prime_thirtySevenAI_61651 : Nat.Prime 61651 := by norm_num
private theorem prime_thirtySevenAI_61717 : Nat.Prime 61717 := by norm_num
private theorem prime_thirtySevenAI_63823 : Nat.Prime 63823 := by norm_num
private theorem prime_thirtySevenAI_64109 : Nat.Prime 64109 := by norm_num
private theorem prime_thirtySevenAI_64901 : Nat.Prime 64901 := by norm_num
private theorem prime_thirtySevenAI_71479 : Nat.Prime 71479 := by norm_num
private theorem prime_thirtySevenAI_71881 : Nat.Prime 71881 := by norm_num
private theorem prime_thirtySevenAI_73121 : Nat.Prime 73121 := by norm_num
private theorem prime_thirtySevenAI_76603 : Nat.Prime 76603 := by norm_num
private theorem prime_thirtySevenAI_79181 : Nat.Prime 79181 := by norm_num
private theorem prime_thirtySevenAI_80251 : Nat.Prime 80251 := by norm_num
private theorem prime_thirtySevenAI_87323 : Nat.Prime 87323 := by norm_num
private theorem prime_thirtySevenAI_89611 : Nat.Prime 89611 := by norm_num
private theorem prime_thirtySevenAI_98849 : Nat.Prime 98849 := by norm_num
private theorem prime_thirtySevenAI_99901 : Nat.Prime 99901 := by norm_num
private theorem prime_thirtySevenAI_109049 : Nat.Prime 109049 := by norm_num
private theorem prime_thirtySevenAI_115079 : Nat.Prime 115079 := by norm_num
private theorem prime_thirtySevenAI_116107 : Nat.Prime 116107 := by norm_num
private theorem prime_thirtySevenAI_116141 : Nat.Prime 116141 := by norm_num
private theorem prime_thirtySevenAI_119293 : Nat.Prime 119293 := by norm_num
private theorem prime_thirtySevenAI_119551 : Nat.Prime 119551 := by norm_num
private theorem prime_thirtySevenAI_128819 : Nat.Prime 128819 := by norm_num
private theorem prime_thirtySevenAI_137659 : Nat.Prime 137659 := by norm_num
private theorem prime_thirtySevenAI_137777 : Nat.Prime 137777 := by norm_num
private theorem prime_thirtySevenAI_138077 : Nat.Prime 138077 := by norm_num
private theorem prime_thirtySevenAI_149491 : Nat.Prime 149491 := by norm_num
private theorem prime_thirtySevenAI_153949 : Nat.Prime 153949 := by norm_num
private theorem prime_thirtySevenAI_161969 : Nat.Prime 161969 := by norm_num
private theorem prime_thirtySevenAI_169919 : Nat.Prime 169919 := by norm_num
private theorem prime_thirtySevenAI_176237 : Nat.Prime 176237 := by norm_num
private theorem prime_thirtySevenAI_176713 : Nat.Prime 176713 := by norm_num
private theorem prime_thirtySevenAI_178853 : Nat.Prime 178853 := by norm_num
private theorem prime_thirtySevenAI_182579 : Nat.Prime 182579 := by norm_num
private theorem prime_thirtySevenAI_183349 : Nat.Prime 183349 := by norm_num
private theorem prime_thirtySevenAI_190901 : Nat.Prime 190901 := by norm_num
private theorem prime_thirtySevenAI_203393 : Nat.Prime 203393 := by norm_num
private theorem prime_thirtySevenAI_219599 : Nat.Prime 219599 := by norm_num
private theorem prime_thirtySevenAI_220699 : Nat.Prime 220699 := by norm_num
private theorem prime_thirtySevenAI_221461 : Nat.Prime 221461 := by norm_num
private theorem prime_thirtySevenAI_243433 : Nat.Prime 243433 := by norm_num
private theorem prime_thirtySevenAI_258623 : Nat.Prime 258623 := by norm_num
private theorem prime_thirtySevenAI_266129 : Nat.Prime 266129 := by norm_num
private theorem prime_thirtySevenAI_289453 : Nat.Prime 289453 := by norm_num
private theorem prime_thirtySevenAI_319399 : Nat.Prime 319399 := by norm_num
private theorem prime_thirtySevenAI_322351 : Nat.Prime 322351 := by norm_num
private theorem prime_thirtySevenAI_334843 : Nat.Prime 334843 := by norm_num
private theorem prime_thirtySevenAI_362863 : Nat.Prime 362863 := by norm_num
private theorem prime_thirtySevenAI_363157 : Nat.Prime 363157 := by norm_num
private theorem prime_thirtySevenAI_370439 : Nat.Prime 370439 := by norm_num
private theorem prime_thirtySevenAI_446933 : Nat.Prime 446933 := by norm_num
private theorem prime_thirtySevenAI_551951 : Nat.Prime 551951 := by norm_num
private theorem prime_thirtySevenAI_556943 : Nat.Prime 556943 := by norm_num
private theorem prime_thirtySevenAI_585113 : Nat.Prime 585113 := by norm_num
private theorem prime_thirtySevenAI_621431 : Nat.Prime 621431 := by norm_num
private theorem prime_thirtySevenAI_623621 : Nat.Prime 623621 := by norm_num
private theorem prime_thirtySevenAI_636287 : Nat.Prime 636287 := by norm_num
private theorem prime_thirtySevenAI_655693 : Nat.Prime 655693 := by norm_num
private theorem prime_thirtySevenAI_655927 : Nat.Prime 655927 := by norm_num
private theorem prime_thirtySevenAI_659963 : Nat.Prime 659963 := by norm_num
private theorem prime_thirtySevenAI_660853 : Nat.Prime 660853 := by norm_num
private theorem prime_thirtySevenAI_671467 : Nat.Prime 671467 := by norm_num
private theorem prime_thirtySevenAI_675347 : Nat.Prime 675347 := by norm_num
private theorem prime_thirtySevenAI_695441 : Nat.Prime 695441 := by norm_num
private theorem prime_thirtySevenAI_702503 : Nat.Prime 702503 := by norm_num
private theorem prime_thirtySevenAI_705113 : Nat.Prime 705113 := by norm_num
private theorem prime_thirtySevenAI_857951 : Nat.Prime 857951 := by norm_num
private theorem prime_thirtySevenAI_859603 : Nat.Prime 859603 := by norm_num
private theorem prime_thirtySevenAI_880343 : Nat.Prime 880343 := by norm_num
private theorem prime_thirtySevenAI_910621 : Nat.Prime 910621 := by norm_num
private theorem prime_thirtySevenAI_914713 : Nat.Prime 914713 := by norm_num
private theorem prime_thirtySevenAI_941513 : Nat.Prime 941513 := by norm_num
private theorem prime_thirtySevenAI_1009037 : Nat.Prime 1009037 := by norm_num
private theorem prime_thirtySevenAI_1028761 : Nat.Prime 1028761 := by norm_num
private theorem prime_thirtySevenAI_1097017 : Nat.Prime 1097017 := by norm_num
private theorem prime_thirtySevenAI_1201153 : Nat.Prime 1201153 := by norm_num
private theorem prime_thirtySevenAI_1268143 : Nat.Prime 1268143 := by norm_num
private theorem prime_thirtySevenAI_1322557 : Nat.Prime 1322557 := by norm_num
private theorem prime_thirtySevenAI_1345471 : Nat.Prime 1345471 := by norm_num
private theorem prime_thirtySevenAI_1441061 : Nat.Prime 1441061 := by norm_num
private theorem prime_thirtySevenAI_1585993 : Nat.Prime 1585993 := by norm_num
private theorem prime_thirtySevenAI_1661117 : Nat.Prime 1661117 := by norm_num
private theorem prime_thirtySevenAI_1875901 : Nat.Prime 1875901 := by norm_num
private theorem prime_thirtySevenAI_2032157 : Nat.Prime 2032157 := by norm_num
private theorem prime_thirtySevenAI_2080157 : Nat.Prime 2080157 := by norm_num
private theorem prime_thirtySevenAI_2335547 : Nat.Prime 2335547 := by norm_num
private theorem prime_thirtySevenAI_2454703 : Nat.Prime 2454703 := by norm_num
private theorem prime_thirtySevenAI_2565257 : Nat.Prime 2565257 := by norm_num
private theorem prime_thirtySevenAI_2678227 : Nat.Prime 2678227 := by norm_num
private theorem prime_thirtySevenAI_2689163 : Nat.Prime 2689163 := by norm_num
private theorem prime_thirtySevenAI_2692973 : Nat.Prime 2692973 := by norm_num
private theorem prime_thirtySevenAI_2761039 : Nat.Prime 2761039 := by norm_num
private theorem prime_thirtySevenAI_2880719 : Nat.Prime 2880719 := by norm_num
private theorem prime_thirtySevenAI_3205759 : Nat.Prime 3205759 := by norm_num
private theorem prime_thirtySevenAI_3249143 : Nat.Prime 3249143 := by norm_num
private theorem prime_thirtySevenAI_3278369 : Nat.Prime 3278369 := by norm_num
private theorem prime_thirtySevenAI_3428141 : Nat.Prime 3428141 := by norm_num
private theorem prime_thirtySevenAI_3447551 : Nat.Prime 3447551 := by norm_num
private theorem prime_thirtySevenAI_3466867 : Nat.Prime 3466867 := by norm_num
private theorem prime_thirtySevenAI_3522367 : Nat.Prime 3522367 := by norm_num
private theorem prime_thirtySevenAI_4017463 : Nat.Prime 4017463 := by norm_num
private theorem prime_thirtySevenAI_4524449 : Nat.Prime 4524449 := by norm_num
private theorem prime_thirtySevenAI_4537229 : Nat.Prime 4537229 := by norm_num
private theorem prime_thirtySevenAI_4773739 : Nat.Prime 4773739 := by norm_num
private theorem prime_thirtySevenAI_5085463 : Nat.Prime 5085463 := by norm_num
private theorem prime_thirtySevenAI_5273407 : Nat.Prime 5273407 := by norm_num
private theorem prime_thirtySevenAI_5331779 : Nat.Prime 5331779 := by norm_num
private theorem prime_thirtySevenAI_5442289 : Nat.Prime 5442289 := by norm_num
private theorem prime_thirtySevenAI_5824043 : Nat.Prime 5824043 := by norm_num
private theorem prime_thirtySevenAI_5853587 : Nat.Prime 5853587 := by norm_num
private theorem prime_thirtySevenAI_6061309 : Nat.Prime 6061309 := by norm_num
private theorem prime_thirtySevenAI_6459151 : Nat.Prime 6459151 := by norm_num
private theorem prime_thirtySevenAI_7190123 : Nat.Prime 7190123 := by norm_num
private theorem prime_thirtySevenAI_7319017 : Nat.Prime 7319017 := by norm_num
private theorem prime_thirtySevenAI_7490023 : Nat.Prime 7490023 := by norm_num
private theorem prime_thirtySevenAI_8002823 : Nat.Prime 8002823 := by norm_num
private theorem prime_thirtySevenAI_8377729 : Nat.Prime 8377729 := by norm_num
private theorem prime_thirtySevenAI_8582597 : Nat.Prime 8582597 := by norm_num
private theorem prime_thirtySevenAI_8831791 : Nat.Prime 8831791 := by norm_num
private theorem prime_thirtySevenAI_9303353 : Nat.Prime 9303353 := by norm_num
private theorem prime_thirtySevenAI_10029797 : Nat.Prime 10029797 := by norm_num
private theorem prime_thirtySevenAI_10566653 : Nat.Prime 10566653 := by norm_num
private theorem prime_thirtySevenAI_11174963 : Nat.Prime 11174963 := by norm_num
private theorem prime_thirtySevenAI_12427759 : Nat.Prime 12427759 := by norm_num
private theorem prime_thirtySevenAI_13732183 : Nat.Prime 13732183 := by norm_num
private theorem prime_thirtySevenAI_14582509 : Nat.Prime 14582509 := by norm_num
private theorem prime_thirtySevenAI_16608877 : Nat.Prime 16608877 := by norm_num
private theorem prime_thirtySevenAI_18156227 : Nat.Prime 18156227 := by norm_num
private theorem prime_thirtySevenAI_18305669 : Nat.Prime 18305669 := by norm_num
private theorem prime_thirtySevenAI_18479933 : Nat.Prime 18479933 := by norm_num
private theorem prime_thirtySevenAI_18780269 : Nat.Prime 18780269 := by norm_num
private theorem prime_thirtySevenAI_21344903 : Nat.Prime 21344903 := by norm_num
private theorem prime_thirtySevenAI_24017051 : Nat.Prime 24017051 := by norm_num
private theorem prime_thirtySevenAI_24040823 : Nat.Prime 24040823 := by norm_num
private theorem prime_thirtySevenAI_24924281 : Nat.Prime 24924281 := by norm_num
private theorem prime_thirtySevenAI_26812879 : Nat.Prime 26812879 := by norm_num
private theorem prime_thirtySevenAI_27895139 : Nat.Prime 27895139 := by norm_num
private theorem prime_thirtySevenAI_27996421 : Nat.Prime 27996421 := by norm_num
private theorem prime_thirtySevenAI_29250029 : Nat.Prime 29250029 := by norm_num

private theorem prime_thirtySevenAI_30172643 : Nat.Prime 30172643 := by
  apply lucas_primality 30172643 (2 : ZMod 30172643)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (655927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (655927, 1)] : List FactorBlock).map factorBlockValue).prod) = 30172643 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_23
      · exact prime_thirtySevenAI_655927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 30172643) ^ 15086321 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 30172643) ^ 1311854 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 30172643) ^ 46 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_31894921 : Nat.Prime 31894921 := by
  apply lucas_primality 31894921 (26 : ZMod 31894921)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (19, 1), (4663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (19, 1), (4663, 1)] : List FactorBlock).map factorBlockValue).prod) = 31894921 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_5
      · exact prime_thirtySevenAI_19
      · exact prime_thirtySevenAI_4663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (26 : ZMod 31894921) ^ 15947460 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (26 : ZMod 31894921) ^ 10631640 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (26 : ZMod 31894921) ^ 6378984 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (26 : ZMod 31894921) ^ 1678680 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (26 : ZMod 31894921) ^ 6840 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_31935481 : Nat.Prime 31935481 := by
  apply lucas_primality 31935481 (13 : ZMod 31935481)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (266129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (266129, 1)] : List FactorBlock).map factorBlockValue).prod) = 31935481 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_5
      · exact prime_thirtySevenAI_266129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 31935481) ^ 15967740 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (13 : ZMod 31935481) ^ 10645160 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (13 : ZMod 31935481) ^ 6387096 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (13 : ZMod 31935481) ^ 120 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_33658813 : Nat.Prime 33658813 := by
  apply lucas_primality 33658813 (2 : ZMod 33658813)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (11, 2), (7727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (11, 2), (7727, 1)] : List FactorBlock).map factorBlockValue).prod) = 33658813 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_11
      · exact prime_thirtySevenAI_7727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 33658813) ^ 16829406 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 33658813) ^ 11219604 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 33658813) ^ 3059892 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 33658813) ^ 4356 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_36611339 : Nat.Prime 36611339 := by
  apply lucas_primality 36611339 (2 : ZMod 36611339)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (18305669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (18305669, 1)] : List FactorBlock).map factorBlockValue).prod) = 36611339 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_18305669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 36611339) ^ 18305669 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 36611339) ^ 2 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_39802223 : Nat.Prime 39802223 := by
  apply lucas_primality 39802223 (5 : ZMod 39802223)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (109, 1), (182579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (109, 1), (182579, 1)] : List FactorBlock).map factorBlockValue).prod) = 39802223 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_109
      · exact prime_thirtySevenAI_182579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 39802223) ^ 19901111 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 39802223) ^ 365158 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 39802223) ^ 218 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_40000963 : Nat.Prime 40000963 := by
  apply lucas_primality 40000963 (5 : ZMod 40000963)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (317, 1), (21031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (317, 1), (21031, 1)] : List FactorBlock).map factorBlockValue).prod) = 40000963 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_317
      · exact prime_thirtySevenAI_21031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 40000963) ^ 20000481 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 40000963) ^ 13333654 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 40000963) ^ 126186 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 40000963) ^ 1902 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_45591383 : Nat.Prime 45591383 := by
  apply lucas_primality 45591383 (5 : ZMod 45591383)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (23, 1), (173, 1), (337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (23, 1), (173, 1), (337, 1)] : List FactorBlock).map factorBlockValue).prod) = 45591383 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_17
      · exact prime_thirtySevenAI_23
      · exact prime_thirtySevenAI_173
      · exact prime_thirtySevenAI_337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 45591383) ^ 22795691 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 45591383) ^ 2681846 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 45591383) ^ 1982234 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 45591383) ^ 263534 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 45591383) ^ 135286 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_49299209 : Nat.Prime 49299209 := by
  apply lucas_primality 49299209 (3 : ZMod 49299209)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (880343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (880343, 1)] : List FactorBlock).map factorBlockValue).prod) = 49299209 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_7
      · exact prime_thirtySevenAI_880343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 49299209) ^ 24649604 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 49299209) ^ 7042744 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 49299209) ^ 56 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_52902281 : Nat.Prime 52902281 := by
  apply lucas_primality 52902281 (3 : ZMod 52902281)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (1322557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (1322557, 1)] : List FactorBlock).map factorBlockValue).prod) = 52902281 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_5
      · exact prime_thirtySevenAI_1322557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 52902281) ^ 26451140 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 52902281) ^ 10580456 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 52902281) ^ 40 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_54928733 : Nat.Prime 54928733 := by
  apply lucas_primality 54928733 (2 : ZMod 54928733)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13732183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13732183, 1)] : List FactorBlock).map factorBlockValue).prod) = 54928733 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_13732183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 54928733) ^ 27464366 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 54928733) ^ 4 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_56290049 : Nat.Prime 56290049 := by
  apply lucas_primality 56290049 (3 : ZMod 56290049)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (31, 1), (41, 1), (173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (31, 1), (41, 1), (173, 1)] : List FactorBlock).map factorBlockValue).prod) = 56290049 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_31
      · exact prime_thirtySevenAI_41
      · exact prime_thirtySevenAI_173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 56290049) ^ 28145024 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 56290049) ^ 1815808 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 56290049) ^ 1372928 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 56290049) ^ 325376 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_57028157 : Nat.Prime 57028157 := by
  apply lucas_primality 57028157 (2 : ZMod 57028157)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (271, 1), (52609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (271, 1), (52609, 1)] : List FactorBlock).map factorBlockValue).prod) = 57028157 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_271
      · exact prime_thirtySevenAI_52609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 57028157) ^ 28514078 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 57028157) ^ 210436 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 57028157) ^ 1084 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_57145379 : Nat.Prime 57145379 := by
  apply lucas_primality 57145379 (2 : ZMod 57145379)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (239, 1), (119551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (239, 1), (119551, 1)] : List FactorBlock).map factorBlockValue).prod) = 57145379 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_239
      · exact prime_thirtySevenAI_119551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 57145379) ^ 28572689 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 57145379) ^ 239102 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 57145379) ^ 478 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_58330037 : Nat.Prime 58330037 := by
  apply lucas_primality 58330037 (2 : ZMod 58330037)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (14582509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (14582509, 1)] : List FactorBlock).map factorBlockValue).prod) = 58330037 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_14582509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 58330037) ^ 29165018 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 58330037) ^ 4 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_60742859 : Nat.Prime 60742859 := by
  apply lucas_primality 60742859 (2 : ZMod 60742859)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (2761039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (2761039, 1)] : List FactorBlock).map factorBlockValue).prod) = 60742859 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_11
      · exact prime_thirtySevenAI_2761039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 60742859) ^ 30371429 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 60742859) ^ 5522078 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 60742859) ^ 22 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_69243563 : Nat.Prime 69243563 := by
  apply lucas_primality 69243563 (2 : ZMod 69243563)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (67, 1), (27197, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (67, 1), (27197, 1)] : List FactorBlock).map factorBlockValue).prod) = 69243563 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_19
      · exact prime_thirtySevenAI_67
      · exact prime_thirtySevenAI_27197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 69243563) ^ 34621781 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 69243563) ^ 3644398 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 69243563) ^ 1033486 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 69243563) ^ 2546 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_69993659 : Nat.Prime 69993659 := by
  apply lucas_primality 69993659 (2 : ZMod 69993659)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (17, 1), (42013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (17, 1), (42013, 1)] : List FactorBlock).map factorBlockValue).prod) = 69993659 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_7
      · exact prime_thirtySevenAI_17
      · exact prime_thirtySevenAI_42013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 69993659) ^ 34996829 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 69993659) ^ 9999094 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 69993659) ^ 4117274 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 69993659) ^ 1666 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_75328873 : Nat.Prime 75328873 := by
  apply lucas_primality 75328873 (5 : ZMod 75328873)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (191, 1), (16433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (191, 1), (16433, 1)] : List FactorBlock).map factorBlockValue).prod) = 75328873 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_191
      · exact prime_thirtySevenAI_16433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 75328873) ^ 37664436 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 75328873) ^ 25109624 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 75328873) ^ 394392 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 75328873) ^ 4584 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_75338867 : Nat.Prime 75338867 := by
  apply lucas_primality 75338867 (2 : ZMod 75338867)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (31, 1), (71479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (31, 1), (71479, 1)] : List FactorBlock).map factorBlockValue).prod) = 75338867 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_17
      · exact prime_thirtySevenAI_31
      · exact prime_thirtySevenAI_71479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 75338867) ^ 37669433 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 75338867) ^ 4431698 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 75338867) ^ 2430286 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 75338867) ^ 1054 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_80352689 : Nat.Prime 80352689 := by
  apply lucas_primality 80352689 (3 : ZMod 80352689)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (13, 1), (71, 1), (5441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (13, 1), (71, 1), (5441, 1)] : List FactorBlock).map factorBlockValue).prod) = 80352689 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_13
      · exact prime_thirtySevenAI_71
      · exact prime_thirtySevenAI_5441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 80352689) ^ 40176344 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 80352689) ^ 6180976 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 80352689) ^ 1131728 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 80352689) ^ 14768 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_86421571 : Nat.Prime 86421571 := by
  apply lucas_primality 86421571 (11 : ZMod 86421571)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (2880719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (2880719, 1)] : List FactorBlock).map factorBlockValue).prod) = 86421571 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_5
      · exact prime_thirtySevenAI_2880719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 86421571) ^ 43210785 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (11 : ZMod 86421571) ^ 28807190 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (11 : ZMod 86421571) ^ 17284314 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (11 : ZMod 86421571) ^ 30 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_88054289 : Nat.Prime 88054289 := by
  apply lucas_primality 88054289 (3 : ZMod 88054289)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (17, 1), (103, 1), (449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (17, 1), (103, 1), (449, 1)] : List FactorBlock).map factorBlockValue).prod) = 88054289 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_7
      · exact prime_thirtySevenAI_17
      · exact prime_thirtySevenAI_103
      · exact prime_thirtySevenAI_449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 88054289) ^ 44027144 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 88054289) ^ 12579184 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 88054289) ^ 5179664 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 88054289) ^ 854896 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 88054289) ^ 196112 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_93866963 : Nat.Prime 93866963 := by
  apply lucas_primality 93866963 (2 : ZMod 93866963)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (17, 1), (181, 1), (2179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (17, 1), (181, 1), (2179, 1)] : List FactorBlock).map factorBlockValue).prod) = 93866963 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_7
      · exact prime_thirtySevenAI_17
      · exact prime_thirtySevenAI_181
      · exact prime_thirtySevenAI_2179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 93866963) ^ 46933481 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 93866963) ^ 13409566 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 93866963) ^ 5521586 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 93866963) ^ 518602 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 93866963) ^ 43078 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_97482823 : Nat.Prime 97482823 := by
  apply lucas_primality 97482823 (5 : ZMod 97482823)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1279, 1), (12703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1279, 1), (12703, 1)] : List FactorBlock).map factorBlockValue).prod) = 97482823 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_1279
      · exact prime_thirtySevenAI_12703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 97482823) ^ 48741411 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 97482823) ^ 32494274 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 97482823) ^ 76218 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 97482823) ^ 7674 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_112580099 : Nat.Prime 112580099 := by
  apply lucas_primality 112580099 (2 : ZMod 112580099)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (56290049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (56290049, 1)] : List FactorBlock).map factorBlockValue).prod) = 112580099 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_56290049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 112580099) ^ 56290049 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 112580099) ^ 2 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_113572271 : Nat.Prime 113572271 := by
  apply lucas_primality 113572271 (14 : ZMod 113572271)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (149, 1), (10889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (149, 1), (10889, 1)] : List FactorBlock).map factorBlockValue).prod) = 113572271 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_5
      · exact prime_thirtySevenAI_7
      · exact prime_thirtySevenAI_149
      · exact prime_thirtySevenAI_10889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 113572271) ^ 56786135 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (14 : ZMod 113572271) ^ 22714454 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (14 : ZMod 113572271) ^ 16224610 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (14 : ZMod 113572271) ^ 762230 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (14 : ZMod 113572271) ^ 10430 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_117302411 : Nat.Prime 117302411 := by
  apply lucas_primality 117302411 (6 : ZMod 117302411)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (101, 1), (116141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (101, 1), (116141, 1)] : List FactorBlock).map factorBlockValue).prod) = 117302411 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_5
      · exact prime_thirtySevenAI_101
      · exact prime_thirtySevenAI_116141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 117302411) ^ 58651205 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (6 : ZMod 117302411) ^ 23460482 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (6 : ZMod 117302411) ^ 1161410 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (6 : ZMod 117302411) ^ 1010 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_121084441 : Nat.Prime 121084441 := by
  apply lucas_primality 121084441 (37 : ZMod 121084441)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (1009037, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (1009037, 1)] : List FactorBlock).map factorBlockValue).prod) = 121084441 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_5
      · exact prime_thirtySevenAI_1009037
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (37 : ZMod 121084441) ^ 60542220 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (37 : ZMod 121084441) ^ 40361480 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (37 : ZMod 121084441) ^ 24216888 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (37 : ZMod 121084441) ^ 120 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_130910579 : Nat.Prime 130910579 := by
  apply lucas_primality 130910579 (2 : ZMod 130910579)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1021, 1), (64109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1021, 1), (64109, 1)] : List FactorBlock).map factorBlockValue).prod) = 130910579 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_1021
      · exact prime_thirtySevenAI_64109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 130910579) ^ 65455289 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 130910579) ^ 128218 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 130910579) ^ 2042 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_144102307 : Nat.Prime 144102307 := by
  apply lucas_primality 144102307 (3 : ZMod 144102307)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (24017051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (24017051, 1)] : List FactorBlock).map factorBlockValue).prod) = 144102307 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_24017051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 144102307) ^ 72051153 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 144102307) ^ 48034102 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 144102307) ^ 6 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_161055133 : Nat.Prime 161055133 := by
  apply lucas_primality 161055133 (2 : ZMod 161055133)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (59, 1), (32497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (59, 1), (32497, 1)] : List FactorBlock).map factorBlockValue).prod) = 161055133 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_7
      · exact prime_thirtySevenAI_59
      · exact prime_thirtySevenAI_32497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 161055133) ^ 80527566 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 161055133) ^ 53685044 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 161055133) ^ 23007876 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 161055133) ^ 2729748 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 161055133) ^ 4956 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_172078549 : Nat.Prime 172078549 := by
  apply lucas_primality 172078549 (2 : ZMod 172078549)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (23, 1), (101, 1), (6173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (23, 1), (101, 1), (6173, 1)] : List FactorBlock).map factorBlockValue).prod) = 172078549 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_23
      · exact prime_thirtySevenAI_101
      · exact prime_thirtySevenAI_6173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 172078549) ^ 86039274 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 172078549) ^ 57359516 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 172078549) ^ 7481676 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 172078549) ^ 1703748 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 172078549) ^ 27876 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_191393383 : Nat.Prime 191393383 := by
  apply lucas_primality 191393383 (3 : ZMod 191393383)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (181, 1), (176237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (181, 1), (176237, 1)] : List FactorBlock).map factorBlockValue).prod) = 191393383 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_181
      · exact prime_thirtySevenAI_176237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 191393383) ^ 95696691 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 191393383) ^ 63797794 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 191393383) ^ 1057422 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 191393383) ^ 1086 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_195269027 : Nat.Prime 195269027 := by
  apply lucas_primality 195269027 (2 : ZMod 195269027)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (89, 1), (1097017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (89, 1), (1097017, 1)] : List FactorBlock).map factorBlockValue).prod) = 195269027 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_89
      · exact prime_thirtySevenAI_1097017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 195269027) ^ 97634513 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 195269027) ^ 2194034 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 195269027) ^ 178 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_201356587 : Nat.Prime 201356587 := by
  apply lucas_primality 201356587 (2 : ZMod 201356587)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (1283, 1), (8719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (1283, 1), (8719, 1)] : List FactorBlock).map factorBlockValue).prod) = 201356587 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_1283
      · exact prime_thirtySevenAI_8719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 201356587) ^ 100678293 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 201356587) ^ 67118862 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 201356587) ^ 156942 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 201356587) ^ 23094 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_240903251 : Nat.Prime 240903251 := by
  apply lucas_primality 240903251 (2 : ZMod 240903251)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 3), (7, 1), (137659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 3), (7, 1), (137659, 1)] : List FactorBlock).map factorBlockValue).prod) = 240903251 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_5
      · exact prime_thirtySevenAI_7
      · exact prime_thirtySevenAI_137659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 240903251) ^ 120451625 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 240903251) ^ 48180650 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 240903251) ^ 34414750 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 240903251) ^ 1750 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_310715501 : Nat.Prime 310715501 := by
  apply lucas_primality 310715501 (2 : ZMod 310715501)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 3), (621431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 3), (621431, 1)] : List FactorBlock).map factorBlockValue).prod) = 310715501 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_5
      · exact prime_thirtySevenAI_621431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 310715501) ^ 155357750 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 310715501) ^ 62143100 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 310715501) ^ 500 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_311561927 : Nat.Prime 311561927 := by
  apply lucas_primality 311561927 (5 : ZMod 311561927)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (67, 1), (178853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (67, 1), (178853, 1)] : List FactorBlock).map factorBlockValue).prod) = 311561927 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_13
      · exact prime_thirtySevenAI_67
      · exact prime_thirtySevenAI_178853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 311561927) ^ 155780963 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 311561927) ^ 23966302 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 311561927) ^ 4650178 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 311561927) ^ 1742 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_319354811 : Nat.Prime 319354811 := by
  apply lucas_primality 319354811 (2 : ZMod 319354811)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (31935481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (31935481, 1)] : List FactorBlock).map factorBlockValue).prod) = 319354811 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_5
      · exact prime_thirtySevenAI_31935481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 319354811) ^ 159677405 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 319354811) ^ 63870962 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 319354811) ^ 10 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_330541181 : Nat.Prime 330541181 := by
  apply lucas_primality 330541181 (2 : ZMod 330541181)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (41, 1), (163, 1), (2473, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (41, 1), (163, 1), (2473, 1)] : List FactorBlock).map factorBlockValue).prod) = 330541181 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_5
      · exact prime_thirtySevenAI_41
      · exact prime_thirtySevenAI_163
      · exact prime_thirtySevenAI_2473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 330541181) ^ 165270590 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 330541181) ^ 66108236 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 330541181) ^ 8061980 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 330541181) ^ 2027860 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 330541181) ^ 133660 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_333754049 : Nat.Prime 333754049 := by
  apply lucas_primality 333754049 (3 : ZMod 333754049)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (719, 1), (7253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (719, 1), (7253, 1)] : List FactorBlock).map factorBlockValue).prod) = 333754049 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_719
      · exact prime_thirtySevenAI_7253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 333754049) ^ 166877024 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 333754049) ^ 464192 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 333754049) ^ 46016 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_377940569 : Nat.Prime 377940569 := by
  apply lucas_primality 377940569 (3 : ZMod 377940569)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (67, 1), (705113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (67, 1), (705113, 1)] : List FactorBlock).map factorBlockValue).prod) = 377940569 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_67
      · exact prime_thirtySevenAI_705113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 377940569) ^ 188970284 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 377940569) ^ 5640904 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 377940569) ^ 536 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_392986703 : Nat.Prime 392986703 := by
  apply lucas_primality 392986703 (5 : ZMod 392986703)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (191, 1), (1028761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (191, 1), (1028761, 1)] : List FactorBlock).map factorBlockValue).prod) = 392986703 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_191
      · exact prime_thirtySevenAI_1028761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 392986703) ^ 196493351 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 392986703) ^ 2057522 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 392986703) ^ 382 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_412250023 : Nat.Prime 412250023 := by
  apply lucas_primality 412250023 (3 : ZMod 412250023)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (23, 1), (29, 1), (34337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (23, 1), (29, 1), (34337, 1)] : List FactorBlock).map factorBlockValue).prod) = 412250023 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_23
      · exact prime_thirtySevenAI_29
      · exact prime_thirtySevenAI_34337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 412250023) ^ 206125011 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 412250023) ^ 137416674 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 412250023) ^ 17923914 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 412250023) ^ 14215518 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 412250023) ^ 12006 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_426554057 : Nat.Prime 426554057 := by
  apply lucas_primality 426554057 (3 : ZMod 426554057)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (37, 1), (1441061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (37, 1), (1441061, 1)] : List FactorBlock).map factorBlockValue).prod) = 426554057 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_37
      · exact prime_thirtySevenAI_1441061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 426554057) ^ 213277028 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 426554057) ^ 11528488 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 426554057) ^ 296 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_472551349 : Nat.Prime 472551349 := by
  apply lucas_primality 472551349 (2 : ZMod 472551349)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (47, 1), (227, 1), (3691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (47, 1), (227, 1), (3691, 1)] : List FactorBlock).map factorBlockValue).prod) = 472551349 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_47
      · exact prime_thirtySevenAI_227
      · exact prime_thirtySevenAI_3691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 472551349) ^ 236275674 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 472551349) ^ 157517116 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 472551349) ^ 10054284 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 472551349) ^ 2081724 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 472551349) ^ 128028 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_492139451 : Nat.Prime 492139451 := by
  apply lucas_primality 492139451 (2 : ZMod 492139451)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (11, 1), (53, 1), (16883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (11, 1), (53, 1), (16883, 1)] : List FactorBlock).map factorBlockValue).prod) = 492139451 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_5
      · exact prime_thirtySevenAI_11
      · exact prime_thirtySevenAI_53
      · exact prime_thirtySevenAI_16883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 492139451) ^ 246069725 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 492139451) ^ 98427890 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 492139451) ^ 44739950 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 492139451) ^ 9285650 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 492139451) ^ 29150 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_590391287 : Nat.Prime 590391287 := by
  apply lucas_primality 590391287 (5 : ZMod 590391287)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2707, 1), (109049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2707, 1), (109049, 1)] : List FactorBlock).map factorBlockValue).prod) = 590391287 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_2707
      · exact prime_thirtySevenAI_109049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 590391287) ^ 295195643 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 590391287) ^ 218098 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 590391287) ^ 5414 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_591590509 : Nat.Prime 591590509 := by
  apply lucas_primality 591590509 (2 : ZMod 591590509)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (49299209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (49299209, 1)] : List FactorBlock).map factorBlockValue).prod) = 591590509 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_49299209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 591590509) ^ 295795254 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 591590509) ^ 197196836 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 591590509) ^ 12 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_659004103 : Nat.Prime 659004103 := by
  apply lucas_primality 659004103 (5 : ZMod 659004103)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (36611339, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (36611339, 1)] : List FactorBlock).map factorBlockValue).prod) = 659004103 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_36611339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 659004103) ^ 329502051 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 659004103) ^ 219668034 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 659004103) ^ 18 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_682615099 : Nat.Prime 682615099 := by
  apply lucas_primality 682615099 (2 : ZMod 682615099)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (3447551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (3447551, 1)] : List FactorBlock).map factorBlockValue).prod) = 682615099 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_11
      · exact prime_thirtySevenAI_3447551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 682615099) ^ 341307549 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 682615099) ^ 227538366 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 682615099) ^ 62055918 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 682615099) ^ 198 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_713372141 : Nat.Prime 713372141 := by
  apply lucas_primality 713372141 (3 : ZMod 713372141)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (13, 1), (23, 1), (119293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (13, 1), (23, 1), (119293, 1)] : List FactorBlock).map factorBlockValue).prod) = 713372141 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_5
      · exact prime_thirtySevenAI_13
      · exact prime_thirtySevenAI_23
      · exact prime_thirtySevenAI_119293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 713372141) ^ 356686070 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 713372141) ^ 142674428 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 713372141) ^ 54874780 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 713372141) ^ 31016180 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 713372141) ^ 5980 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_793500649 : Nat.Prime 793500649 := by
  apply lucas_primality 793500649 (11 : ZMod 793500649)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (19, 1), (79, 1), (22027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (19, 1), (79, 1), (22027, 1)] : List FactorBlock).map factorBlockValue).prod) = 793500649 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_19
      · exact prime_thirtySevenAI_79
      · exact prime_thirtySevenAI_22027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 793500649) ^ 396750324 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (11 : ZMod 793500649) ^ 264500216 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (11 : ZMod 793500649) ^ 41763192 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (11 : ZMod 793500649) ^ 10044312 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (11 : ZMod 793500649) ^ 36024 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_1034857799 : Nat.Prime 1034857799 := by
  apply lucas_primality 1034857799 (17 : ZMod 1034857799)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (39802223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (39802223, 1)] : List FactorBlock).map factorBlockValue).prod) = 1034857799 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_13
      · exact prime_thirtySevenAI_39802223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (17 : ZMod 1034857799) ^ 517428899 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (17 : ZMod 1034857799) ^ 79604446 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (17 : ZMod 1034857799) ^ 26 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_1113067973 : Nat.Prime 1113067973 := by
  apply lucas_primality 1113067973 (2 : ZMod 1113067973)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (79, 1), (3522367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (79, 1), (3522367, 1)] : List FactorBlock).map factorBlockValue).prod) = 1113067973 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_79
      · exact prime_thirtySevenAI_3522367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1113067973) ^ 556533986 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1113067973) ^ 14089468 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1113067973) ^ 316 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_1141205281 : Nat.Prime 1141205281 := by
  apply lucas_primality 1141205281 (11 : ZMod 1141205281)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 1), (1013, 1), (2347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 1), (1013, 1), (2347, 1)] : List FactorBlock).map factorBlockValue).prod) = 1141205281 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_5
      · exact prime_thirtySevenAI_1013
      · exact prime_thirtySevenAI_2347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 1141205281) ^ 570602640 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (11 : ZMod 1141205281) ^ 380401760 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (11 : ZMod 1141205281) ^ 228241056 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (11 : ZMod 1141205281) ^ 1126560 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (11 : ZMod 1141205281) ^ 486240 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_1195314569 : Nat.Prime 1195314569 := by
  apply lucas_primality 1195314569 (3 : ZMod 1195314569)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (21344903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (21344903, 1)] : List FactorBlock).map factorBlockValue).prod) = 1195314569 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_7
      · exact prime_thirtySevenAI_21344903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1195314569) ^ 597657284 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1195314569) ^ 170759224 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1195314569) ^ 56 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_1222615931 : Nat.Prime 1222615931 := by
  apply lucas_primality 1222615931 (2 : ZMod 1222615931)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (29, 1), (113, 1), (37309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (29, 1), (113, 1), (37309, 1)] : List FactorBlock).map factorBlockValue).prod) = 1222615931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_5
      · exact prime_thirtySevenAI_29
      · exact prime_thirtySevenAI_113
      · exact prime_thirtySevenAI_37309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1222615931) ^ 611307965 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 244523186 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 42159170 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 10819610 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222615931) ^ 32770 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_1243931243 : Nat.Prime 1243931243 := by
  apply lucas_primality 1243931243 (2 : ZMod 1243931243)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (73, 1), (173, 1), (2897, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (73, 1), (173, 1), (2897, 1)] : List FactorBlock).map factorBlockValue).prod) = 1243931243 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_17
      · exact prime_thirtySevenAI_73
      · exact prime_thirtySevenAI_173
      · exact prime_thirtySevenAI_2897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1243931243) ^ 621965621 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1243931243) ^ 73172426 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1243931243) ^ 17040154 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1243931243) ^ 7190354 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1243931243) ^ 429386 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_1411531951 : Nat.Prime 1411531951 := by
  apply lucas_primality 1411531951 (3 : ZMod 1411531951)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (1277, 1), (7369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (1277, 1), (7369, 1)] : List FactorBlock).map factorBlockValue).prod) = 1411531951 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_5
      · exact prime_thirtySevenAI_1277
      · exact prime_thirtySevenAI_7369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1411531951) ^ 705765975 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1411531951) ^ 470510650 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1411531951) ^ 282306390 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1411531951) ^ 1105350 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1411531951) ^ 191550 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_1426744283 : Nat.Prime 1426744283 := by
  apply lucas_primality 1426744283 (2 : ZMod 1426744283)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (713372141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (713372141, 1)] : List FactorBlock).map factorBlockValue).prod) = 1426744283 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_713372141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 1426744283) ^ 713372141 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1426744283) ^ 2 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_1453236077 : Nat.Prime 1453236077 := by
  apply lucas_primality 1453236077 (2 : ZMod 1453236077)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (101, 1), (307, 1), (11717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (101, 1), (307, 1), (11717, 1)] : List FactorBlock).map factorBlockValue).prod) = 1453236077 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_101
      · exact prime_thirtySevenAI_307
      · exact prime_thirtySevenAI_11717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1453236077) ^ 726618038 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1453236077) ^ 14388476 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1453236077) ^ 4733668 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1453236077) ^ 124028 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_1530253061 : Nat.Prime 1530253061 := by
  apply lucas_primality 1530253061 (2 : ZMod 1530253061)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (71, 1), (153949, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (71, 1), (153949, 1)] : List FactorBlock).map factorBlockValue).prod) = 1530253061 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_5
      · exact prime_thirtySevenAI_7
      · exact prime_thirtySevenAI_71
      · exact prime_thirtySevenAI_153949
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1530253061) ^ 765126530 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1530253061) ^ 306050612 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1530253061) ^ 218607580 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1530253061) ^ 21552860 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1530253061) ^ 9940 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_1574434369 : Nat.Prime 1574434369 := by
  apply lucas_primality 1574434369 (11 : ZMod 1574434369)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (13, 1), (109, 1), (643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (13, 1), (109, 1), (643, 1)] : List FactorBlock).map factorBlockValue).prod) = 1574434369 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_13
      · exact prime_thirtySevenAI_109
      · exact prime_thirtySevenAI_643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 1574434369) ^ 787217184 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (11 : ZMod 1574434369) ^ 524811456 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (11 : ZMod 1574434369) ^ 121110336 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (11 : ZMod 1574434369) ^ 14444352 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (11 : ZMod 1574434369) ^ 2448576 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_1604427889 : Nat.Prime 1604427889 := by
  apply lucas_primality 1604427889 (19 : ZMod 1604427889)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (7, 1), (197, 1), (24239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (7, 1), (197, 1), (24239, 1)] : List FactorBlock).map factorBlockValue).prod) = 1604427889 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_7
      · exact prime_thirtySevenAI_197
      · exact prime_thirtySevenAI_24239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 1604427889) ^ 802213944 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (19 : ZMod 1604427889) ^ 534809296 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (19 : ZMod 1604427889) ^ 229203984 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (19 : ZMod 1604427889) ^ 8144304 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (19 : ZMod 1604427889) ^ 66192 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_1805730461 : Nat.Prime 1805730461 := by
  apply lucas_primality 1805730461 (2 : ZMod 1805730461)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (23, 1), (1483, 1), (2647, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (23, 1), (1483, 1), (2647, 1)] : List FactorBlock).map factorBlockValue).prod) = 1805730461 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_5
      · exact prime_thirtySevenAI_23
      · exact prime_thirtySevenAI_1483
      · exact prime_thirtySevenAI_2647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1805730461) ^ 902865230 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1805730461) ^ 361146092 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1805730461) ^ 78510020 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1805730461) ^ 1217620 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1805730461) ^ 682180 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_1859406863 : Nat.Prime 1859406863 := by
  apply lucas_primality 1859406863 (5 : ZMod 1859406863)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (859, 1), (37321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (859, 1), (37321, 1)] : List FactorBlock).map factorBlockValue).prod) = 1859406863 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_29
      · exact prime_thirtySevenAI_859
      · exact prime_thirtySevenAI_37321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1859406863) ^ 929703431 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 1859406863) ^ 64117478 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 1859406863) ^ 2164618 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 1859406863) ^ 49822 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_1864293007 : Nat.Prime 1864293007 := by
  apply lucas_primality 1864293007 (3 : ZMod 1864293007)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (310715501, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (310715501, 1)] : List FactorBlock).map factorBlockValue).prod) = 1864293007 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_310715501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1864293007) ^ 932146503 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1864293007) ^ 621431002 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1864293007) ^ 6 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_2776917799 : Nat.Prime 2776917799 := by
  apply lucas_primality 2776917799 (3 : ZMod 2776917799)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (277, 1), (556943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (277, 1), (556943, 1)] : List FactorBlock).map factorBlockValue).prod) = 2776917799 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_277
      · exact prime_thirtySevenAI_556943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2776917799) ^ 1388458899 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 2776917799) ^ 925639266 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 2776917799) ^ 10024974 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 2776917799) ^ 4986 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_3201093227 : Nat.Prime 3201093227 := by
  apply lucas_primality 3201093227 (2 : ZMod 3201093227)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2441, 1), (655693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2441, 1), (655693, 1)] : List FactorBlock).map factorBlockValue).prod) = 3201093227 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_2441
      · exact prime_thirtySevenAI_655693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3201093227) ^ 1600546613 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3201093227) ^ 1311386 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3201093227) ^ 4882 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_3565850021 : Nat.Prime 3565850021 := by
  apply lucas_primality 3565850021 (2 : ZMod 3565850021)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (31, 1), (541, 1), (10631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (31, 1), (541, 1), (10631, 1)] : List FactorBlock).map factorBlockValue).prod) = 3565850021 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_5
      · exact prime_thirtySevenAI_31
      · exact prime_thirtySevenAI_541
      · exact prime_thirtySevenAI_10631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3565850021) ^ 1782925010 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3565850021) ^ 713170004 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3565850021) ^ 115027420 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3565850021) ^ 6591220 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3565850021) ^ 335420 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_3954024619 : Nat.Prime 3954024619 := by
  apply lucas_primality 3954024619 (2 : ZMod 3954024619)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (659004103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (659004103, 1)] : List FactorBlock).map factorBlockValue).prod) = 3954024619 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_659004103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3954024619) ^ 1977012309 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3954024619) ^ 1318008206 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3954024619) ^ 6 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_3982788877 : Nat.Prime 3982788877 := by
  apply lucas_primality 3982788877 (2 : ZMod 3982788877)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (30172643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (30172643, 1)] : List FactorBlock).map factorBlockValue).prod) = 3982788877 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_11
      · exact prime_thirtySevenAI_30172643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3982788877) ^ 1991394438 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3982788877) ^ 1327596292 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3982788877) ^ 362071716 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3982788877) ^ 132 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_4289947163 : Nat.Prime 4289947163 := by
  apply lucas_primality 4289947163 (2 : ZMod 4289947163)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (9719, 1), (220699, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (9719, 1), (220699, 1)] : List FactorBlock).map factorBlockValue).prod) = 4289947163 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_9719
      · exact prime_thirtySevenAI_220699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4289947163) ^ 2144973581 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 4289947163) ^ 441398 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 4289947163) ^ 19438 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_5222542651 : Nat.Prime 5222542651 := by
  apply lucas_primality 5222542651 (2 : ZMod 5222542651)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (13, 1), (2678227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (13, 1), (2678227, 1)] : List FactorBlock).map factorBlockValue).prod) = 5222542651 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_5
      · exact prime_thirtySevenAI_13
      · exact prime_thirtySevenAI_2678227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5222542651) ^ 2611271325 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 5222542651) ^ 1740847550 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 5222542651) ^ 1044508530 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 5222542651) ^ 401734050 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 5222542651) ^ 1950 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_6751396753 : Nat.Prime 6751396753 := by
  apply lucas_primality 6751396753 (7 : ZMod 6751396753)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (31, 1), (4537229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (31, 1), (4537229, 1)] : List FactorBlock).map factorBlockValue).prod) = 6751396753 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_31
      · exact prime_thirtySevenAI_4537229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 6751396753) ^ 3375698376 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (7 : ZMod 6751396753) ^ 2250465584 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (7 : ZMod 6751396753) ^ 217786992 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (7 : ZMod 6751396753) ^ 1488 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_7355196109 : Nat.Prime 7355196109 := by
  apply lucas_primality 7355196109 (2 : ZMod 7355196109)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (13, 1), (29, 1), (37, 1), (97, 1), (151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (13, 1), (29, 1), (37, 1), (97, 1), (151, 1)] : List FactorBlock).map factorBlockValue).prod) = 7355196109 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_13
      · exact prime_thirtySevenAI_29
      · exact prime_thirtySevenAI_37
      · exact prime_thirtySevenAI_97
      · exact prime_thirtySevenAI_151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7355196109) ^ 3677598054 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 7355196109) ^ 2451732036 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 7355196109) ^ 565784316 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 7355196109) ^ 253627452 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 7355196109) ^ 198789084 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 7355196109) ^ 75826764 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 7355196109) ^ 48709908 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_8288812769 : Nat.Prime 8288812769 := by
  apply lucas_primality 8288812769 (3 : ZMod 8288812769)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (59, 1), (353, 1), (12437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (59, 1), (353, 1), (12437, 1)] : List FactorBlock).map factorBlockValue).prod) = 8288812769 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_59
      · exact prime_thirtySevenAI_353
      · exact prime_thirtySevenAI_12437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 8288812769) ^ 4144406384 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 8288812769) ^ 140488352 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 8288812769) ^ 23481056 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 8288812769) ^ 666464 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_8786883271 : Nat.Prime 8786883271 := by
  apply lucas_primality 8786883271 (6 : ZMod 8786883271)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 2), (827, 1), (2927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 2), (827, 1), (2927, 1)] : List FactorBlock).map factorBlockValue).prod) = 8786883271 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_5
      · exact prime_thirtySevenAI_11
      · exact prime_thirtySevenAI_827
      · exact prime_thirtySevenAI_2927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 8786883271) ^ 4393441635 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (6 : ZMod 8786883271) ^ 2928961090 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (6 : ZMod 8786883271) ^ 1757376654 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (6 : ZMod 8786883271) ^ 798807570 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (6 : ZMod 8786883271) ^ 10625010 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (6 : ZMod 8786883271) ^ 3002010 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_9346904353 : Nat.Prime 9346904353 := by
  apply lucas_primality 9346904353 (5 : ZMod 9346904353)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (191, 1), (169919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (191, 1), (169919, 1)] : List FactorBlock).map factorBlockValue).prod) = 9346904353 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_191
      · exact prime_thirtySevenAI_169919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 9346904353) ^ 4673452176 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 9346904353) ^ 3115634784 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 9346904353) ^ 48936672 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 9346904353) ^ 55008 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_9978011677 : Nat.Prime 9978011677 := by
  apply lucas_primality 9978011677 (2 : ZMod 9978011677)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (3371, 1), (27407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (3371, 1), (27407, 1)] : List FactorBlock).map factorBlockValue).prod) = 9978011677 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_3371
      · exact prime_thirtySevenAI_27407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 9978011677) ^ 4989005838 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 9978011677) ^ 3326003892 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 9978011677) ^ 2959956 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 9978011677) ^ 364068 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_10581611773 : Nat.Prime 10581611773 := by
  apply lucas_primality 10581611773 (2 : ZMod 10581611773)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (41, 1), (47, 1), (193, 1), (2371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (41, 1), (47, 1), (193, 1), (2371, 1)] : List FactorBlock).map factorBlockValue).prod) = 10581611773 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_41
      · exact prime_thirtySevenAI_47
      · exact prime_thirtySevenAI_193
      · exact prime_thirtySevenAI_2371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 10581611773) ^ 5290805886 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 10581611773) ^ 3527203924 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 10581611773) ^ 258088092 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 10581611773) ^ 225140676 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 10581611773) ^ 54827004 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 10581611773) ^ 4462932 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_11155428877 : Nat.Prime 11155428877 := by
  apply lucas_primality 11155428877 (2 : ZMod 11155428877)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (139, 1), (467, 1), (14321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (139, 1), (467, 1), (14321, 1)] : List FactorBlock).map factorBlockValue).prod) = 11155428877 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_139
      · exact prime_thirtySevenAI_467
      · exact prime_thirtySevenAI_14321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 11155428877) ^ 5577714438 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 11155428877) ^ 3718476292 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 11155428877) ^ 80254884 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 11155428877) ^ 23887428 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 11155428877) ^ 778956 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_12053653841 : Nat.Prime 12053653841 := by
  apply lucas_primality 12053653841 (7 : ZMod 12053653841)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (47, 1), (3205759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (47, 1), (3205759, 1)] : List FactorBlock).map factorBlockValue).prod) = 12053653841 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_5
      · exact prime_thirtySevenAI_47
      · exact prime_thirtySevenAI_3205759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 12053653841) ^ 6026826920 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (7 : ZMod 12053653841) ^ 2410730768 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (7 : ZMod 12053653841) ^ 256460720 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (7 : ZMod 12053653841) ^ 3760 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_13085508353 : Nat.Prime 13085508353 := by
  apply lucas_primality 13085508353 (3 : ZMod 13085508353)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (7, 1), (53, 1), (137777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (7, 1), (53, 1), (137777, 1)] : List FactorBlock).map factorBlockValue).prod) = 13085508353 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_7
      · exact prime_thirtySevenAI_53
      · exact prime_thirtySevenAI_137777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 13085508353) ^ 6542754176 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 13085508353) ^ 1869358336 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 13085508353) ^ 246896384 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 13085508353) ^ 94976 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_13383906967 : Nat.Prime 13383906967 := by
  apply lucas_primality 13383906967 (3 : ZMod 13383906967)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (47, 1), (5273407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (47, 1), (5273407, 1)] : List FactorBlock).map factorBlockValue).prod) = 13383906967 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_47
      · exact prime_thirtySevenAI_5273407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 13383906967) ^ 6691953483 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 13383906967) ^ 4461302322 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 13383906967) ^ 284763978 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 13383906967) ^ 2538 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_14191028167 : Nat.Prime 14191028167 := by
  apply lucas_primality 14191028167 (5 : ZMod 14191028167)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (61, 1), (263, 1), (21061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (61, 1), (263, 1), (21061, 1)] : List FactorBlock).map factorBlockValue).prod) = 14191028167 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_7
      · exact prime_thirtySevenAI_61
      · exact prime_thirtySevenAI_263
      · exact prime_thirtySevenAI_21061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 14191028167) ^ 7095514083 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 14191028167) ^ 4730342722 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 14191028167) ^ 2027289738 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 14191028167) ^ 232639806 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 14191028167) ^ 53958282 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 14191028167) ^ 673806 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_14936747537 : Nat.Prime 14936747537 := by
  apply lucas_primality 14936747537 (5 : ZMod 14936747537)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (17, 1), (89, 1), (97, 1), (6361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (17, 1), (89, 1), (97, 1), (6361, 1)] : List FactorBlock).map factorBlockValue).prod) = 14936747537 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_17
      · exact prime_thirtySevenAI_89
      · exact prime_thirtySevenAI_97
      · exact prime_thirtySevenAI_6361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 14936747537) ^ 7468373768 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 14936747537) ^ 878632208 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 14936747537) ^ 167828624 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 14936747537) ^ 153987088 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 14936747537) ^ 2348176 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_15306898513 : Nat.Prime 15306898513 := by
  apply lucas_primality 15306898513 (5 : ZMod 15306898513)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (43, 1), (83, 1), (199, 1), (449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (43, 1), (83, 1), (199, 1), (449, 1)] : List FactorBlock).map factorBlockValue).prod) = 15306898513 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_43
      · exact prime_thirtySevenAI_83
      · exact prime_thirtySevenAI_199
      · exact prime_thirtySevenAI_449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 15306898513) ^ 7653449256 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 15306898513) ^ 5102299504 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 15306898513) ^ 355974384 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 15306898513) ^ 184420464 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 15306898513) ^ 76919088 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 15306898513) ^ 34091088 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_15350173463 : Nat.Prime 15350173463 := by
  apply lucas_primality 15350173463 (5 : ZMod 15350173463)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (590391287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (590391287, 1)] : List FactorBlock).map factorBlockValue).prod) = 15350173463 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_13
      · exact prime_thirtySevenAI_590391287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 15350173463) ^ 7675086731 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 15350173463) ^ 1180782574 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 15350173463) ^ 26 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_20575320547 : Nat.Prime 20575320547 := by
  apply lucas_primality 20575320547 (3 : ZMod 20575320547)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (127, 1), (2454703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (127, 1), (2454703, 1)] : List FactorBlock).map factorBlockValue).prod) = 20575320547 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_11
      · exact prime_thirtySevenAI_127
      · exact prime_thirtySevenAI_2454703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 20575320547) ^ 10287660273 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 20575320547) ^ 6858440182 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 20575320547) ^ 1870483686 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 20575320547) ^ 162010398 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 20575320547) ^ 8382 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_21311113093 : Nat.Prime 21311113093 := by
  apply lucas_primality 21311113093 (5 : ZMod 21311113093)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (38119, 1), (46589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (38119, 1), (46589, 1)] : List FactorBlock).map factorBlockValue).prod) = 21311113093 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_38119
      · exact prime_thirtySevenAI_46589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 21311113093) ^ 10655556546 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 21311113093) ^ 7103704364 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 21311113093) ^ 559068 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 21311113093) ^ 457428 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_24892895119 : Nat.Prime 24892895119 := by
  apply lucas_primality 24892895119 (3 : ZMod 24892895119)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (13, 1), (45591383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (13, 1), (45591383, 1)] : List FactorBlock).map factorBlockValue).prod) = 24892895119 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_7
      · exact prime_thirtySevenAI_13
      · exact prime_thirtySevenAI_45591383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 24892895119) ^ 12446447559 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 24892895119) ^ 8297631706 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 24892895119) ^ 3556127874 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 24892895119) ^ 1914838086 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 24892895119) ^ 546 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_26403298853 : Nat.Prime 26403298853 := by
  apply lucas_primality 26403298853 (2 : ZMod 26403298853)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (19, 2), (47, 1), (149, 1), (373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (19, 2), (47, 1), (149, 1), (373, 1)] : List FactorBlock).map factorBlockValue).prod) = 26403298853 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_7
      · exact prime_thirtySevenAI_19
      · exact prime_thirtySevenAI_47
      · exact prime_thirtySevenAI_149
      · exact prime_thirtySevenAI_373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 26403298853) ^ 13201649426 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 26403298853) ^ 3771899836 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 26403298853) ^ 1389647308 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 26403298853) ^ 561772316 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 26403298853) ^ 177203348 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 26403298853) ^ 70786324 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_33274018597 : Nat.Prime 33274018597 := by
  apply lucas_primality 33274018597 (5 : ZMod 33274018597)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 2), (13, 2), (334843, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 2), (13, 2), (334843, 1)] : List FactorBlock).map factorBlockValue).prod) = 33274018597 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_7
      · exact prime_thirtySevenAI_13
      · exact prime_thirtySevenAI_334843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 33274018597) ^ 16637009298 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 33274018597) ^ 11091339532 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 33274018597) ^ 4753431228 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 33274018597) ^ 2559539892 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 33274018597) ^ 99372 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_33351827917 : Nat.Prime 33351827917 := by
  apply lucas_primality 33351827917 (2 : ZMod 33351827917)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (19, 1), (53, 1), (83, 1), (3023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (19, 1), (53, 1), (83, 1), (3023, 1)] : List FactorBlock).map factorBlockValue).prod) = 33351827917 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_11
      · exact prime_thirtySevenAI_19
      · exact prime_thirtySevenAI_53
      · exact prime_thirtySevenAI_83
      · exact prime_thirtySevenAI_3023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 33351827917) ^ 16675913958 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 33351827917) ^ 11117275972 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 33351827917) ^ 3031984356 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 33351827917) ^ 1755359364 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 33351827917) ^ 629279772 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 33351827917) ^ 401829252 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 33351827917) ^ 11032692 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_34801939327 : Nat.Prime 34801939327 := by
  apply lucas_primality 34801939327 (3 : ZMod 34801939327)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (11, 1), (75328873, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (11, 1), (75328873, 1)] : List FactorBlock).map factorBlockValue).prod) = 34801939327 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_7
      · exact prime_thirtySevenAI_11
      · exact prime_thirtySevenAI_75328873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 34801939327) ^ 17400969663 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 34801939327) ^ 11600646442 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 34801939327) ^ 4971705618 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 34801939327) ^ 3163812666 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 34801939327) ^ 462 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_46676502739 : Nat.Prime 46676502739 := by
  apply lucas_primality 46676502739 (2 : ZMod 46676502739)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (443, 1), (5853587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (443, 1), (5853587, 1)] : List FactorBlock).map factorBlockValue).prod) = 46676502739 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_443
      · exact prime_thirtySevenAI_5853587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 46676502739) ^ 23338251369 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 46676502739) ^ 15558834246 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 46676502739) ^ 105364566 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 46676502739) ^ 7974 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_52806597707 : Nat.Prime 52806597707 := by
  apply lucas_primality 52806597707 (2 : ZMod 52806597707)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (26403298853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (26403298853, 1)] : List FactorBlock).map factorBlockValue).prod) = 52806597707 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_26403298853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 52806597707) ^ 26403298853 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 52806597707) ^ 2 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_55622907167 : Nat.Prime 55622907167 := by
  apply lucas_primality 55622907167 (5 : ZMod 55622907167)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (997, 1), (27895139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (997, 1), (27895139, 1)] : List FactorBlock).map factorBlockValue).prod) = 55622907167 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_997
      · exact prime_thirtySevenAI_27895139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 55622907167) ^ 27811453583 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 55622907167) ^ 55790278 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 55622907167) ^ 1994 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_83560682417 : Nat.Prime 83560682417 := by
  apply lucas_primality 83560682417 (3 : ZMod 83560682417)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5222542651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5222542651, 1)] : List FactorBlock).map factorBlockValue).prod) = 83560682417 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_5222542651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 83560682417) ^ 41780341208 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 83560682417) ^ 16 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_95586933049 : Nat.Prime 95586933049 := by
  apply lucas_primality 95586933049 (7 : ZMod 95586933049)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (3982788877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (3982788877, 1)] : List FactorBlock).map factorBlockValue).prod) = 95586933049 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_3982788877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 95586933049) ^ 47793466524 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (7 : ZMod 95586933049) ^ 31862311016 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (7 : ZMod 95586933049) ^ 24 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_126968497427 : Nat.Prime 126968497427 := by
  apply lucas_primality 126968497427 (2 : ZMod 126968497427)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (907, 1), (69993659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (907, 1), (69993659, 1)] : List FactorBlock).map factorBlockValue).prod) = 126968497427 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_907
      · exact prime_thirtySevenAI_69993659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 126968497427) ^ 63484248713 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 126968497427) ^ 139987318 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 126968497427) ^ 1814 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_129330077641 : Nat.Prime 129330077641 := by
  apply lucas_primality 129330077641 (11 : ZMod 129330077641)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (10903, 1), (98849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (10903, 1), (98849, 1)] : List FactorBlock).map factorBlockValue).prod) = 129330077641 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_5
      · exact prime_thirtySevenAI_10903
      · exact prime_thirtySevenAI_98849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 129330077641) ^ 64665038820 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (11 : ZMod 129330077641) ^ 43110025880 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (11 : ZMod 129330077641) ^ 25866015528 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (11 : ZMod 129330077641) ^ 11861880 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (11 : ZMod 129330077641) ^ 1308360 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_159534901429 : Nat.Prime 159534901429 := by
  apply lucas_primality 159534901429 (2 : ZMod 159534901429)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (79, 1), (24040823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (79, 1), (24040823, 1)] : List FactorBlock).map factorBlockValue).prod) = 159534901429 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_7
      · exact prime_thirtySevenAI_79
      · exact prime_thirtySevenAI_24040823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 159534901429) ^ 79767450714 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 159534901429) ^ 53178300476 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 159534901429) ^ 22790700204 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 159534901429) ^ 2019429132 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 159534901429) ^ 6636 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_168286941047 : Nat.Prime 168286941047 := by
  apply lucas_primality 168286941047 (5 : ZMod 168286941047)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (97, 1), (5701, 1), (21737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (97, 1), (5701, 1), (21737, 1)] : List FactorBlock).map factorBlockValue).prod) = 168286941047 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_7
      · exact prime_thirtySevenAI_97
      · exact prime_thirtySevenAI_5701
      · exact prime_thirtySevenAI_21737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 168286941047) ^ 84143470523 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 168286941047) ^ 24040991578 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 168286941047) ^ 1734916918 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 168286941047) ^ 29518846 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 168286941047) ^ 7741958 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_173978796149 : Nat.Prime 173978796149 := by
  apply lucas_primality 173978796149 (2 : ZMod 173978796149)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1021, 1), (3433, 1), (12409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1021, 1), (3433, 1), (12409, 1)] : List FactorBlock).map factorBlockValue).prod) = 173978796149 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_1021
      · exact prime_thirtySevenAI_3433
      · exact prime_thirtySevenAI_12409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 173978796149) ^ 86989398074 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 173978796149) ^ 170400388 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 173978796149) ^ 50678356 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 173978796149) ^ 14020372 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_178486862033 : Nat.Prime 178486862033 := by
  apply lucas_primality 178486862033 (3 : ZMod 178486862033)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (11155428877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (11155428877, 1)] : List FactorBlock).map factorBlockValue).prod) = 178486862033 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_11155428877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 178486862033) ^ 89243431016 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 178486862033) ^ 16 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_192457070789 : Nat.Prime 192457070789 := by
  apply lucas_primality 192457070789 (2 : ZMod 192457070789)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (36947, 1), (76603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (36947, 1), (76603, 1)] : List FactorBlock).map factorBlockValue).prod) = 192457070789 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_17
      · exact prime_thirtySevenAI_36947
      · exact prime_thirtySevenAI_76603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 192457070789) ^ 96228535394 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 192457070789) ^ 11321004164 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 192457070789) ^ 5209004 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 192457070789) ^ 2512396 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_226546858061 : Nat.Prime 226546858061 := by
  apply lucas_primality 226546858061 (2 : ZMod 226546858061)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (53, 1), (227, 1), (941513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (53, 1), (227, 1), (941513, 1)] : List FactorBlock).map factorBlockValue).prod) = 226546858061 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_5
      · exact prime_thirtySevenAI_53
      · exact prime_thirtySevenAI_227
      · exact prime_thirtySevenAI_941513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 226546858061) ^ 113273429030 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 226546858061) ^ 45309371612 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 226546858061) ^ 4274469020 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 226546858061) ^ 998003780 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 226546858061) ^ 240620 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_270802711469 : Nat.Prime 270802711469 := by
  apply lucas_primality 270802711469 (2 : ZMod 270802711469)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (43, 1), (1574434369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (43, 1), (1574434369, 1)] : List FactorBlock).map factorBlockValue).prod) = 270802711469 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_43
      · exact prime_thirtySevenAI_1574434369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 270802711469) ^ 135401355734 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 270802711469) ^ 6297737476 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 270802711469) ^ 172 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_275538705823 : Nat.Prime 275538705823 := by
  apply lucas_primality 275538705823 (3 : ZMod 275538705823)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (17, 1), (12527, 1), (71881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (17, 1), (12527, 1), (71881, 1)] : List FactorBlock).map factorBlockValue).prod) = 275538705823 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_17
      · exact prime_thirtySevenAI_12527
      · exact prime_thirtySevenAI_71881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 275538705823) ^ 137769352911 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 275538705823) ^ 91846235274 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 275538705823) ^ 16208159166 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 275538705823) ^ 21995586 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 275538705823) ^ 3833262 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_295617946229 : Nat.Prime 295617946229 := by
  apply lucas_primality 295617946229 (2 : ZMod 295617946229)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (127, 1), (52902281, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (127, 1), (52902281, 1)] : List FactorBlock).map factorBlockValue).prod) = 295617946229 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_11
      · exact prime_thirtySevenAI_127
      · exact prime_thirtySevenAI_52902281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 295617946229) ^ 147808973114 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 295617946229) ^ 26874358748 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 295617946229) ^ 2327700364 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 295617946229) ^ 5588 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_323364945581 : Nat.Prime 323364945581 := by
  apply lucas_primality 323364945581 (3 : ZMod 323364945581)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (23, 1), (433, 1), (1009, 1), (1609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (23, 1), (433, 1), (1009, 1), (1609, 1)] : List FactorBlock).map factorBlockValue).prod) = 323364945581 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_5
      · exact prime_thirtySevenAI_23
      · exact prime_thirtySevenAI_433
      · exact prime_thirtySevenAI_1009
      · exact prime_thirtySevenAI_1609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 323364945581) ^ 161682472790 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 323364945581) ^ 64672989116 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 323364945581) ^ 14059345460 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 323364945581) ^ 746801260 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 323364945581) ^ 320480620 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 323364945581) ^ 200972620 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_333126130973 : Nat.Prime 333126130973 := by
  apply lucas_primality 333126130973 (2 : ZMod 333126130973)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (79, 1), (233, 1), (4524449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (79, 1), (233, 1), (4524449, 1)] : List FactorBlock).map factorBlockValue).prod) = 333126130973 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_79
      · exact prime_thirtySevenAI_233
      · exact prime_thirtySevenAI_4524449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 333126130973) ^ 166563065486 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 333126130973) ^ 4216786468 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 333126130973) ^ 1429725884 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 333126130973) ^ 73628 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_462094662389 : Nat.Prime 462094662389 := by
  apply lucas_primality 462094662389 (2 : ZMod 462094662389)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (397, 1), (2531, 1), (6763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (397, 1), (2531, 1), (6763, 1)] : List FactorBlock).map factorBlockValue).prod) = 462094662389 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_17
      · exact prime_thirtySevenAI_397
      · exact prime_thirtySevenAI_2531
      · exact prime_thirtySevenAI_6763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 462094662389) ^ 231047331194 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 27182038964 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 1163966404 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 182573948 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 462094662389) ^ 68326876 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_496245373489 : Nat.Prime 496245373489 := by
  apply lucas_primality 496245373489 (7 : ZMod 496245373489)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (19, 1), (211, 1), (859603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (19, 1), (211, 1), (859603, 1)] : List FactorBlock).map factorBlockValue).prod) = 496245373489 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_19
      · exact prime_thirtySevenAI_211
      · exact prime_thirtySevenAI_859603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 496245373489) ^ 248122686744 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (7 : ZMod 496245373489) ^ 165415124496 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (7 : ZMod 496245373489) ^ 26118177552 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (7 : ZMod 496245373489) ^ 2351873808 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (7 : ZMod 496245373489) ^ 577296 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_511880589221 : Nat.Prime 511880589221 := by
  apply lucas_primality 511880589221 (2 : ZMod 511880589221)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (11, 1), (13, 1), (41, 1), (623621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (11, 1), (13, 1), (41, 1), (623621, 1)] : List FactorBlock).map factorBlockValue).prod) = 511880589221 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_5
      · exact prime_thirtySevenAI_7
      · exact prime_thirtySevenAI_11
      · exact prime_thirtySevenAI_13
      · exact prime_thirtySevenAI_41
      · exact prime_thirtySevenAI_623621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 511880589221) ^ 255940294610 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 511880589221) ^ 102376117844 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 511880589221) ^ 73125798460 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 511880589221) ^ 46534599020 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 511880589221) ^ 39375429940 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 511880589221) ^ 12484892420 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 511880589221) ^ 820820 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_527411708687 : Nat.Prime 527411708687 := by
  apply lucas_primality 527411708687 (5 : ZMod 527411708687)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (6047, 1), (2565257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (6047, 1), (2565257, 1)] : List FactorBlock).map factorBlockValue).prod) = 527411708687 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_17
      · exact prime_thirtySevenAI_6047
      · exact prime_thirtySevenAI_2565257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 527411708687) ^ 263705854343 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 527411708687) ^ 31024218158 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 527411708687) ^ 87218738 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 527411708687) ^ 205598 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_539623282241 : Nat.Prime 539623282241 := by
  apply lucas_primality 539623282241 (3 : ZMod 539623282241)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (5, 1), (7, 1), (240903251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (5, 1), (7, 1), (240903251, 1)] : List FactorBlock).map factorBlockValue).prod) = 539623282241 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_5
      · exact prime_thirtySevenAI_7
      · exact prime_thirtySevenAI_240903251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 539623282241) ^ 269811641120 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 539623282241) ^ 107924656448 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 539623282241) ^ 77089040320 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 539623282241) ^ 2240 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_589825440623 : Nat.Prime 589825440623 := by
  apply lucas_primality 589825440623 (5 : ZMod 589825440623)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (79, 1), (167, 1), (2032157, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (79, 1), (167, 1), (2032157, 1)] : List FactorBlock).map factorBlockValue).prod) = 589825440623 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_11
      · exact prime_thirtySevenAI_79
      · exact prime_thirtySevenAI_167
      · exact prime_thirtySevenAI_2032157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 589825440623) ^ 294912720311 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 589825440623) ^ 53620494602 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 589825440623) ^ 7466144818 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 589825440623) ^ 3531888866 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 589825440623) ^ 290246 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_755691134491 : Nat.Prime 755691134491 := by
  apply lucas_primality 755691134491 (3 : ZMod 755691134491)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (43, 1), (195269027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (43, 1), (195269027, 1)] : List FactorBlock).map factorBlockValue).prod) = 755691134491 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_5
      · exact prime_thirtySevenAI_43
      · exact prime_thirtySevenAI_195269027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 755691134491) ^ 377845567245 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 755691134491) ^ 251897044830 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 755691134491) ^ 151138226898 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 755691134491) ^ 17574212430 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 755691134491) ^ 3870 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_896516272271 : Nat.Prime 896516272271 := by
  apply lucas_primality 896516272271 (14 : ZMod 896516272271)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 2), (61, 1), (5085463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 2), (61, 1), (5085463, 1)] : List FactorBlock).map factorBlockValue).prod) = 896516272271 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_5
      · exact prime_thirtySevenAI_17
      · exact prime_thirtySevenAI_61
      · exact prime_thirtySevenAI_5085463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 896516272271) ^ 448258136135 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (14 : ZMod 896516272271) ^ 179303254454 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (14 : ZMod 896516272271) ^ 52736251310 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (14 : ZMod 896516272271) ^ 14696988070 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (14 : ZMod 896516272271) ^ 176290 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_906663499619 : Nat.Prime 906663499619 := by
  apply lucas_primality 906663499619 (2 : ZMod 906663499619)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2243, 1), (7369, 1), (27427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2243, 1), (7369, 1), (27427, 1)] : List FactorBlock).map factorBlockValue).prod) = 906663499619 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_2243
      · exact prime_thirtySevenAI_7369
      · exact prime_thirtySevenAI_27427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 906663499619) ^ 453331749809 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 906663499619) ^ 404219126 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 906663499619) ^ 123037522 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 906663499619) ^ 33057334 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_911346020789 : Nat.Prime 911346020789 := by
  apply lucas_primality 911346020789 (2 : ZMod 911346020789)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (967, 1), (33658813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (967, 1), (33658813, 1)] : List FactorBlock).map factorBlockValue).prod) = 911346020789 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_7
      · exact prime_thirtySevenAI_967
      · exact prime_thirtySevenAI_33658813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 911346020789) ^ 455673010394 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 911346020789) ^ 130192288684 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 911346020789) ^ 942446764 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 911346020789) ^ 27076 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_1077813008567 : Nat.Prime 1077813008567 := by
  apply lucas_primality 1077813008567 (5 : ZMod 1077813008567)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (19163, 1), (4017463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (19163, 1), (4017463, 1)] : List FactorBlock).map factorBlockValue).prod) = 1077813008567 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_7
      · exact prime_thirtySevenAI_19163
      · exact prime_thirtySevenAI_4017463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1077813008567) ^ 538906504283 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 1077813008567) ^ 153973286938 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 1077813008567) ^ 56244482 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 1077813008567) ^ 268282 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_1182514485653 : Nat.Prime 1182514485653 := by
  apply lucas_primality 1182514485653 (2 : ZMod 1182514485653)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (137, 1), (113572271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (137, 1), (113572271, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182514485653 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_19
      · exact prime_thirtySevenAI_137
      · exact prime_thirtySevenAI_113572271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1182514485653) ^ 591257242826 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1182514485653) ^ 62237604508 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1182514485653) ^ 8631492596 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1182514485653) ^ 10412 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_1506641962849 : Nat.Prime 1506641962849 := by
  apply lucas_primality 1506641962849 (29 : ZMod 1506641962849)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (11, 1), (1426744283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (11, 1), (1426744283, 1)] : List FactorBlock).map factorBlockValue).prod) = 1506641962849 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_11
      · exact prime_thirtySevenAI_1426744283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (29 : ZMod 1506641962849) ^ 753320981424 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (29 : ZMod 1506641962849) ^ 502213987616 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (29 : ZMod 1506641962849) ^ 136967451168 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (29 : ZMod 1506641962849) ^ 1056 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_1521962095903 : Nat.Prime 1521962095903 := by
  apply lucas_primality 1521962095903 (3 : ZMod 1521962095903)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (35279, 1), (7190123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (35279, 1), (7190123, 1)] : List FactorBlock).map factorBlockValue).prod) = 1521962095903 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_35279
      · exact prime_thirtySevenAI_7190123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1521962095903) ^ 760981047951 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 507320698634 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 43140738 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1521962095903) ^ 211674 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_1793032544543 : Nat.Prime 1793032544543 := by
  apply lucas_primality 1793032544543 (5 : ZMod 1793032544543)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (896516272271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (896516272271, 1)] : List FactorBlock).map factorBlockValue).prod) = 1793032544543 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_896516272271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 1793032544543) ^ 896516272271 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 1793032544543) ^ 2 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_1800933314129 : Nat.Prime 1800933314129 := by
  apply lucas_primality 1800933314129 (3 : ZMod 1800933314129)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (13, 1), (43, 1), (201356587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (13, 1), (43, 1), (201356587, 1)] : List FactorBlock).map factorBlockValue).prod) = 1800933314129 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_13
      · exact prime_thirtySevenAI_43
      · exact prime_thirtySevenAI_201356587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1800933314129) ^ 900466657064 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1800933314129) ^ 138533331856 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1800933314129) ^ 41882170096 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1800933314129) ^ 8944 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_1852526162209 : Nat.Prime 1852526162209 := by
  apply lucas_primality 1852526162209 (11 : ZMod 1852526162209)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (59, 1), (7573, 1), (43189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (59, 1), (7573, 1), (43189, 1)] : List FactorBlock).map factorBlockValue).prod) = 1852526162209 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_59
      · exact prime_thirtySevenAI_7573
      · exact prime_thirtySevenAI_43189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 1852526162209) ^ 926263081104 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (11 : ZMod 1852526162209) ^ 617508720736 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (11 : ZMod 1852526162209) ^ 31398748512 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (11 : ZMod 1852526162209) ^ 244622496 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (11 : ZMod 1852526162209) ^ 42893472 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_2396421365411 : Nat.Prime 2396421365411 := by
  apply lucas_primality 2396421365411 (2 : ZMod 2396421365411)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1663, 1), (144102307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1663, 1), (144102307, 1)] : List FactorBlock).map factorBlockValue).prod) = 2396421365411 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_5
      · exact prime_thirtySevenAI_1663
      · exact prime_thirtySevenAI_144102307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2396421365411) ^ 1198210682705 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2396421365411) ^ 479284273082 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2396421365411) ^ 1441023070 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2396421365411) ^ 16630 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_2539075302139 : Nat.Prime 2539075302139 := by
  apply lucas_primality 2539075302139 (2 : ZMod 2539075302139)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (24892895119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (24892895119, 1)] : List FactorBlock).map factorBlockValue).prod) = 2539075302139 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_17
      · exact prime_thirtySevenAI_24892895119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2539075302139) ^ 1269537651069 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2539075302139) ^ 846358434046 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2539075302139) ^ 149357370714 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2539075302139) ^ 102 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_3164470252123 : Nat.Prime 3164470252123 := by
  apply lucas_primality 3164470252123 (2 : ZMod 3164470252123)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (527411708687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (527411708687, 1)] : List FactorBlock).map factorBlockValue).prod) = 3164470252123 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_527411708687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3164470252123) ^ 1582235126061 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3164470252123) ^ 1054823417374 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3164470252123) ^ 6 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_3211311593459 : Nat.Prime 3211311593459 := by
  apply lucas_primality 3211311593459 (2 : ZMod 3211311593459)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (83, 1), (60013, 1), (322351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (83, 1), (60013, 1), (322351, 1)] : List FactorBlock).map factorBlockValue).prod) = 3211311593459 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_83
      · exact prime_thirtySevenAI_60013
      · exact prime_thirtySevenAI_322351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3211311593459) ^ 1605655796729 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3211311593459) ^ 38690501126 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3211311593459) ^ 53510266 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3211311593459) ^ 9962158 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_3891913610437 : Nat.Prime 3891913610437 := by
  apply lucas_primality 3891913610437 (5 : ZMod 3891913610437)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (19, 1), (701, 2), (11579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (19, 1), (701, 2), (11579, 1)] : List FactorBlock).map factorBlockValue).prod) = 3891913610437 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_19
      · exact prime_thirtySevenAI_701
      · exact prime_thirtySevenAI_11579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 3891913610437) ^ 1945956805218 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 3891913610437) ^ 1297304536812 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 3891913610437) ^ 204837558444 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 3891913610437) ^ 5551945236 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 3891913610437) ^ 336118284 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_4869586326107 : Nat.Prime 4869586326107 := by
  apply lucas_primality 4869586326107 (2 : ZMod 4869586326107)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (137, 1), (311, 1), (57145379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (137, 1), (311, 1), (57145379, 1)] : List FactorBlock).map factorBlockValue).prod) = 4869586326107 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_137
      · exact prime_thirtySevenAI_311
      · exact prime_thirtySevenAI_57145379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4869586326107) ^ 2434793163053 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 4869586326107) ^ 35544425738 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 4869586326107) ^ 15657833846 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 4869586326107) ^ 85214 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_5421204524741 : Nat.Prime 5421204524741 := by
  apply lucas_primality 5421204524741 (2 : ZMod 5421204524741)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (29, 1), (9346904353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (29, 1), (9346904353, 1)] : List FactorBlock).map factorBlockValue).prod) = 5421204524741 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_5
      · exact prime_thirtySevenAI_29
      · exact prime_thirtySevenAI_9346904353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5421204524741) ^ 2710602262370 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 5421204524741) ^ 1084240904948 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 5421204524741) ^ 186938087060 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 5421204524741) ^ 580 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_5778144651281 : Nat.Prime 5778144651281 := by
  apply lucas_primality 5778144651281 (3 : ZMod 5778144651281)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (17, 1), (103, 1), (1103, 1), (37397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (17, 1), (103, 1), (1103, 1), (37397, 1)] : List FactorBlock).map factorBlockValue).prod) = 5778144651281 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_5
      · exact prime_thirtySevenAI_17
      · exact prime_thirtySevenAI_103
      · exact prime_thirtySevenAI_1103
      · exact prime_thirtySevenAI_37397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 5778144651281) ^ 2889072325640 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 5778144651281) ^ 1155628930256 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 5778144651281) ^ 339890861840 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 5778144651281) ^ 56098491760 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 5778144651281) ^ 5238571760 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 5778144651281) ^ 154508240 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_7116623315941 : Nat.Prime 7116623315941 := by
  apply lucas_primality 7116623315941 (6 : ZMod 7116623315941)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (251, 1), (472551349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (251, 1), (472551349, 1)] : List FactorBlock).map factorBlockValue).prod) = 7116623315941 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_5
      · exact prime_thirtySevenAI_251
      · exact prime_thirtySevenAI_472551349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 7116623315941) ^ 3558311657970 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (6 : ZMod 7116623315941) ^ 2372207771980 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (6 : ZMod 7116623315941) ^ 1423324663188 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (6 : ZMod 7116623315941) ^ 28353080940 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (6 : ZMod 7116623315941) ^ 15060 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_7721904893401 : Nat.Prime 7721904893401 := by
  apply lucas_primality 7721904893401 (11 : ZMod 7721904893401)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 2), (4289947163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 2), (4289947163, 1)] : List FactorBlock).map factorBlockValue).prod) = 7721904893401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_5
      · exact prime_thirtySevenAI_4289947163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 7721904893401) ^ 3860952446700 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (11 : ZMod 7721904893401) ^ 2573968297800 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (11 : ZMod 7721904893401) ^ 1544380978680 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (11 : ZMod 7721904893401) ^ 1800 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_8814058220323 : Nat.Prime 8814058220323 := by
  apply lucas_primality 8814058220323 (3 : ZMod 8814058220323)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (67, 1), (83, 1), (88054289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (67, 1), (83, 1), (88054289, 1)] : List FactorBlock).map factorBlockValue).prod) = 8814058220323 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_67
      · exact prime_thirtySevenAI_83
      · exact prime_thirtySevenAI_88054289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 8814058220323) ^ 4407029110161 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 8814058220323) ^ 2938019406774 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 8814058220323) ^ 131553107766 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 8814058220323) ^ 106193472534 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 8814058220323) ^ 100098 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_10438727768941 : Nat.Prime 10438727768941 := by
  apply lucas_primality 10438727768941 (2 : ZMod 10438727768941)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (173978796149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (173978796149, 1)] : List FactorBlock).map factorBlockValue).prod) = 10438727768941 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_5
      · exact prime_thirtySevenAI_173978796149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 10438727768941) ^ 5219363884470 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 10438727768941) ^ 3479575922980 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 10438727768941) ^ 2087745553788 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 10438727768941) ^ 60 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_15815242981667 : Nat.Prime 15815242981667 := by
  apply lucas_primality 15815242981667 (2 : ZMod 15815242981667)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (636287, 1), (12427759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (636287, 1), (12427759, 1)] : List FactorBlock).map factorBlockValue).prod) = 15815242981667 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_636287
      · exact prime_thirtySevenAI_12427759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 15815242981667) ^ 7907621490833 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 15815242981667) ^ 24855518 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 15815242981667) ^ 1272574 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_27136135194503 : Nat.Prime 27136135194503 := by
  apply lucas_primality 27136135194503 (5 : ZMod 27136135194503)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17099, 1), (793500649, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17099, 1), (793500649, 1)] : List FactorBlock).map factorBlockValue).prod) = 27136135194503 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_17099
      · exact prime_thirtySevenAI_793500649
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 27136135194503) ^ 13568067597251 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 27136135194503) ^ 1587001298 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 27136135194503) ^ 34198 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_28275921087847 : Nat.Prime 28275921087847 := by
  apply lucas_primality 28275921087847 (3 : ZMod 28275921087847)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (59, 1), (87323, 1), (914713, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (59, 1), (87323, 1), (914713, 1)] : List FactorBlock).map factorBlockValue).prod) = 28275921087847 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_59
      · exact prime_thirtySevenAI_87323
      · exact prime_thirtySevenAI_914713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 28275921087847) ^ 14137960543923 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 28275921087847) ^ 9425307029282 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 28275921087847) ^ 479252899794 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 28275921087847) ^ 323808402 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 28275921087847) ^ 30912342 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_29934035031001 : Nat.Prime 29934035031001 := by
  apply lucas_primality 29934035031001 (7 : ZMod 29934035031001)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 3), (9978011677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 3), (9978011677, 1)] : List FactorBlock).map factorBlockValue).prod) = 29934035031001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_5
      · exact prime_thirtySevenAI_9978011677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 29934035031001) ^ 14967017515500 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (7 : ZMod 29934035031001) ^ 9978011677000 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (7 : ZMod 29934035031001) ^ 5986807006200 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (7 : ZMod 29934035031001) ^ 3000 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_36533560098481 : Nat.Prime 36533560098481 := by
  apply lucas_primality 36533560098481 (14 : ZMod 36533560098481)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (223, 1), (682615099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (223, 1), (682615099, 1)] : List FactorBlock).map factorBlockValue).prod) = 36533560098481 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_5
      · exact prime_thirtySevenAI_223
      · exact prime_thirtySevenAI_682615099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 36533560098481) ^ 18266780049240 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (14 : ZMod 36533560098481) ^ 12177853366160 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (14 : ZMod 36533560098481) ^ 7306712019696 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (14 : ZMod 36533560098481) ^ 163827623760 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (14 : ZMod 36533560098481) ^ 53520 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_42467431724857 : Nat.Prime 42467431724857 := by
  apply lucas_primality 42467431724857 (5 : ZMod 42467431724857)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (589825440623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (589825440623, 1)] : List FactorBlock).map factorBlockValue).prod) = 42467431724857 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_589825440623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 42467431724857) ^ 21233715862428 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 42467431724857) ^ 14155810574952 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 42467431724857) ^ 72 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_47321092540151 : Nat.Prime 47321092540151 := by
  apply lucas_primality 47321092540151 (22 : ZMod 47321092540151)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (11, 1), (13, 1), (827, 1), (8002823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (11, 1), (13, 1), (827, 1), (8002823, 1)] : List FactorBlock).map factorBlockValue).prod) = 47321092540151 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_5
      · exact prime_thirtySevenAI_11
      · exact prime_thirtySevenAI_13
      · exact prime_thirtySevenAI_827
      · exact prime_thirtySevenAI_8002823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (22 : ZMod 47321092540151) ^ 23660546270075 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (22 : ZMod 47321092540151) ^ 9464218508030 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (22 : ZMod 47321092540151) ^ 4301917503650 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (22 : ZMod 47321092540151) ^ 3640084041550 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (22 : ZMod 47321092540151) ^ 57220184450 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (22 : ZMod 47321092540151) ^ 5913050 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_48877924245389 : Nat.Prime 48877924245389 := by
  apply lucas_primality 48877924245389 (3 : ZMod 48877924245389)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (203393, 1), (8582597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (203393, 1), (8582597, 1)] : List FactorBlock).map factorBlockValue).prod) = 48877924245389 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_7
      · exact prime_thirtySevenAI_203393
      · exact prime_thirtySevenAI_8582597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 48877924245389) ^ 24438962122694 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 48877924245389) ^ 6982560606484 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 48877924245389) ^ 240312716 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 48877924245389) ^ 5695004 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_92335042689059 : Nat.Prime 92335042689059 := by
  apply lucas_primality 92335042689059 (2 : ZMod 92335042689059)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (193, 1), (229, 1), (80352689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (193, 1), (229, 1), (80352689, 1)] : List FactorBlock).map factorBlockValue).prod) = 92335042689059 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_13
      · exact prime_thirtySevenAI_193
      · exact prime_thirtySevenAI_229
      · exact prime_thirtySevenAI_80352689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 92335042689059) ^ 46167521344529 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 92335042689059) ^ 7102695591466 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 92335042689059) ^ 478419910306 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 92335042689059) ^ 403209793402 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 92335042689059) ^ 1149122 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_92440542607271 : Nat.Prime 92440542607271 := by
  apply lucas_primality 92440542607271 (11 : ZMod 92440542607271)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (13, 1), (2309, 1), (27996421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (13, 1), (2309, 1), (27996421, 1)] : List FactorBlock).map factorBlockValue).prod) = 92440542607271 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_5
      · exact prime_thirtySevenAI_11
      · exact prime_thirtySevenAI_13
      · exact prime_thirtySevenAI_2309
      · exact prime_thirtySevenAI_27996421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 92440542607271) ^ 46220271303635 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (11 : ZMod 92440542607271) ^ 18488108521454 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (11 : ZMod 92440542607271) ^ 8403685691570 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (11 : ZMod 92440542607271) ^ 7110810969790 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (11 : ZMod 92440542607271) ^ 40034882030 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (11 : ZMod 92440542607271) ^ 3301870 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_97755848490779 : Nat.Prime 97755848490779 := by
  apply lucas_primality 97755848490779 (2 : ZMod 97755848490779)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (48877924245389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (48877924245389, 1)] : List FactorBlock).map factorBlockValue).prod) = 97755848490779 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_48877924245389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 97755848490779) ^ 48877924245389 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 97755848490779) ^ 2 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_116121417396427 : Nat.Prime 116121417396427 := by
  apply lucas_primality 116121417396427 (5 : ZMod 116121417396427)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (496245373489, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (496245373489, 1)] : List FactorBlock).map factorBlockValue).prod) = 116121417396427 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_13
      · exact prime_thirtySevenAI_496245373489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 116121417396427) ^ 58060708698213 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 116121417396427) ^ 38707139132142 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 116121417396427) ^ 8932416722802 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 116121417396427) ^ 234 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_123155823283931 : Nat.Prime 123155823283931 := by
  apply lucas_primality 123155823283931 (2 : ZMod 123155823283931)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (31, 1), (193, 1), (28151, 1), (73121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (31, 1), (193, 1), (28151, 1), (73121, 1)] : List FactorBlock).map factorBlockValue).prod) = 123155823283931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_5
      · exact prime_thirtySevenAI_31
      · exact prime_thirtySevenAI_193
      · exact prime_thirtySevenAI_28151
      · exact prime_thirtySevenAI_73121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 123155823283931) ^ 61577911641965 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 123155823283931) ^ 24631164656786 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 123155823283931) ^ 3972768493030 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 123155823283931) ^ 638113074010 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 123155823283931) ^ 4374829430 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 123155823283931) ^ 1684274330 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_153416777006431 : Nat.Prime 153416777006431 := by
  apply lucas_primality 153416777006431 (12 : ZMod 153416777006431)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (5, 1), (7, 1), (31, 1), (229, 1), (409, 1), (9319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (5, 1), (7, 1), (31, 1), (229, 1), (409, 1), (9319, 1)] : List FactorBlock).map factorBlockValue).prod) = 153416777006431 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_5
      · exact prime_thirtySevenAI_7
      · exact prime_thirtySevenAI_31
      · exact prime_thirtySevenAI_229
      · exact prime_thirtySevenAI_409
      · exact prime_thirtySevenAI_9319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (12 : ZMod 153416777006431) ^ 76708388503215 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (12 : ZMod 153416777006431) ^ 51138925668810 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (12 : ZMod 153416777006431) ^ 30683355401286 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (12 : ZMod 153416777006431) ^ 21916682429490 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (12 : ZMod 153416777006431) ^ 4948928290530 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (12 : ZMod 153416777006431) ^ 669942257670 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (12 : ZMod 153416777006431) ^ 375102144270 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (12 : ZMod 153416777006431) ^ 16462793970 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_174544682690047 : Nat.Prime 174544682690047 := by
  apply lucas_primality 174544682690047 (5 : ZMod 174544682690047)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (523, 1), (55622907167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (523, 1), (55622907167, 1)] : List FactorBlock).map factorBlockValue).prod) = 174544682690047 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_523
      · exact prime_thirtySevenAI_55622907167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 174544682690047) ^ 87272341345023 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 174544682690047) ^ 58181560896682 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 174544682690047) ^ 333737443002 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 174544682690047) ^ 3138 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_186836305930397 : Nat.Prime 186836305930397 := by
  apply lucas_primality 186836305930397 (2 : ZMod 186836305930397)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (6247, 1), (58043, 1), (128819, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (6247, 1), (58043, 1), (128819, 1)] : List FactorBlock).map factorBlockValue).prod) = 186836305930397 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_6247
      · exact prime_thirtySevenAI_58043
      · exact prime_thirtySevenAI_128819
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 186836305930397) ^ 93418152965198 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 186836305930397) ^ 29908164868 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 186836305930397) ^ 3218929172 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 186836305930397) ^ 1450378484 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_193551523862569 : Nat.Prime 193551523862569 := by
  apply lucas_primality 193551523862569 (7 : ZMod 193551523862569)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7793, 1), (1034857799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7793, 1), (1034857799, 1)] : List FactorBlock).map factorBlockValue).prod) = 193551523862569 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_7793
      · exact prime_thirtySevenAI_1034857799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 193551523862569) ^ 96775761931284 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (7 : ZMod 193551523862569) ^ 64517174620856 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (7 : ZMod 193551523862569) ^ 24836587176 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (7 : ZMod 193551523862569) ^ 187032 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_327365068419373 : Nat.Prime 327365068419373 := by
  apply lucas_primality 327365068419373 (2 : ZMod 327365068419373)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (3709, 1), (7355196109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (3709, 1), (7355196109, 1)] : List FactorBlock).map factorBlockValue).prod) = 327365068419373 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_3709
      · exact prime_thirtySevenAI_7355196109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 327365068419373) ^ 163682534209686 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 327365068419373) ^ 109121689473124 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 327365068419373) ^ 88262353308 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 327365068419373) ^ 44508 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_330810548380849 : Nat.Prime 330810548380849 := by
  apply lucas_primality 330810548380849 (7 : ZMod 330810548380849)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 4), (53, 1), (151, 1), (31894921, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 4), (53, 1), (151, 1), (31894921, 1)] : List FactorBlock).map factorBlockValue).prod) = 330810548380849 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_53
      · exact prime_thirtySevenAI_151
      · exact prime_thirtySevenAI_31894921
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 330810548380849) ^ 165405274190424 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (7 : ZMod 330810548380849) ^ 110270182793616 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (7 : ZMod 330810548380849) ^ 6241708460016 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (7 : ZMod 330810548380849) ^ 2190798333648 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (7 : ZMod 330810548380849) ^ 10371888 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_375794199681877 : Nat.Prime 375794199681877 := by
  apply lucas_primality 375794199681877 (2 : ZMod 375794199681877)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (10438727768941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (10438727768941, 1)] : List FactorBlock).map factorBlockValue).prod) = 375794199681877 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_10438727768941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 375794199681877) ^ 187897099840938 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 375794199681877) ^ 125264733227292 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 375794199681877) ^ 36 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_705539515057079 : Nat.Prime 705539515057079 := by
  apply lucas_primality 705539515057079 (17 : ZMod 705539515057079)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (27136135194503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (27136135194503, 1)] : List FactorBlock).map factorBlockValue).prod) = 705539515057079 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_13
      · exact prime_thirtySevenAI_27136135194503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (17 : ZMod 705539515057079) ^ 352769757528539 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (17 : ZMod 705539515057079) ^ 54272270389006 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (17 : ZMod 705539515057079) ^ 26 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_710934016571957 : Nat.Prime 710934016571957 := by
  apply lucas_primality 710934016571957 (2 : ZMod 710934016571957)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5107, 1), (34801939327, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5107, 1), (34801939327, 1)] : List FactorBlock).map factorBlockValue).prod) = 710934016571957 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_5107
      · exact prime_thirtySevenAI_34801939327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 710934016571957) ^ 355467008285978 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 710934016571957) ^ 139207757308 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 710934016571957) ^ 20428 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_741302869766497 : Nat.Prime 741302869766497 := by
  apply lucas_primality 741302869766497 (5 : ZMod 741302869766497)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (7721904893401, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (7721904893401, 1)] : List FactorBlock).map factorBlockValue).prod) = 741302869766497 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_7721904893401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 741302869766497) ^ 370651434883248 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 741302869766497) ^ 247100956588832 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 741302869766497) ^ 96 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_760541762683613 : Nat.Prime 760541762683613 := by
  apply lucas_primality 760541762683613 (2 : ZMod 760541762683613)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (13, 1), (115079, 1), (18156227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (13, 1), (115079, 1), (18156227, 1)] : List FactorBlock).map factorBlockValue).prod) = 760541762683613 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_7
      · exact prime_thirtySevenAI_13
      · exact prime_thirtySevenAI_115079
      · exact prime_thirtySevenAI_18156227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 760541762683613) ^ 380270881341806 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 760541762683613) ^ 108648823240516 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 760541762683613) ^ 58503212514124 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 760541762683613) ^ 6608866628 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 760541762683613) ^ 41888756 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_851363092593239 : Nat.Prime 851363092593239 := by
  apply lucas_primality 851363092593239 (7 : ZMod 851363092593239)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1879, 1), (226546858061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1879, 1), (226546858061, 1)] : List FactorBlock).map factorBlockValue).prod) = 851363092593239 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_1879
      · exact prime_thirtySevenAI_226546858061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 851363092593239) ^ 425681546296619 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (7 : ZMod 851363092593239) ^ 453093716122 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (7 : ZMod 851363092593239) ^ 3758 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_944523766609441 : Nat.Prime 944523766609441 := by
  apply lucas_primality 944523766609441 (11 : ZMod 944523766609441)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 1), (59, 1), (33351827917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 1), (59, 1), (33351827917, 1)] : List FactorBlock).map factorBlockValue).prod) = 944523766609441 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_5
      · exact prime_thirtySevenAI_59
      · exact prime_thirtySevenAI_33351827917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 944523766609441) ^ 472261883304720 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (11 : ZMod 944523766609441) ^ 314841255536480 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (11 : ZMod 944523766609441) ^ 188904753321888 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (11 : ZMod 944523766609441) ^ 16008877400160 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (11 : ZMod 944523766609441) ^ 28320 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_1123820192311867 : Nat.Prime 1123820192311867 := by
  apply lucas_primality 1123820192311867 (3 : ZMod 1123820192311867)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (53, 1), (168286941047, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (53, 1), (168286941047, 1)] : List FactorBlock).map factorBlockValue).prod) = 1123820192311867 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_7
      · exact prime_thirtySevenAI_53
      · exact prime_thirtySevenAI_168286941047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1123820192311867) ^ 561910096155933 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1123820192311867) ^ 374606730770622 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1123820192311867) ^ 160545741758838 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1123820192311867) ^ 21204154571922 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1123820192311867) ^ 6678 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_1226828565754021 : Nat.Prime 1226828565754021 := by
  apply lucas_primality 1226828565754021 (7 : ZMod 1226828565754021)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (41, 1), (281, 1), (591590509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (41, 1), (281, 1), (591590509, 1)] : List FactorBlock).map factorBlockValue).prod) = 1226828565754021 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_5
      · exact prime_thirtySevenAI_41
      · exact prime_thirtySevenAI_281
      · exact prime_thirtySevenAI_591590509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1226828565754021) ^ 613414282877010 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (7 : ZMod 1226828565754021) ^ 408942855251340 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (7 : ZMod 1226828565754021) ^ 245365713150804 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (7 : ZMod 1226828565754021) ^ 29922647945220 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (7 : ZMod 1226828565754021) ^ 4365937956420 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (7 : ZMod 1226828565754021) ^ 2073780 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_1419032034363179 : Nat.Prime 1419032034363179 := by
  apply lucas_primality 1419032034363179 (2 : ZMod 1419032034363179)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (151, 1), (3931, 1), (1195314569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (151, 1), (3931, 1), (1195314569, 1)] : List FactorBlock).map factorBlockValue).prod) = 1419032034363179 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_151
      · exact prime_thirtySevenAI_3931
      · exact prime_thirtySevenAI_1195314569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1419032034363179) ^ 709516017181589 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1419032034363179) ^ 9397563141478 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1419032034363179) ^ 360984999838 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1419032034363179) ^ 1187162 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_1503176798727509 : Nat.Prime 1503176798727509 := by
  apply lucas_primality 1503176798727509 (2 : ZMod 1503176798727509)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (375794199681877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (375794199681877, 1)] : List FactorBlock).map factorBlockValue).prod) = 1503176798727509 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_375794199681877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 1503176798727509) ^ 751588399363754 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1503176798727509) ^ 4 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_1652952575203343 : Nat.Prime 1652952575203343 := by
  apply lucas_primality 1652952575203343 (5 : ZMod 1652952575203343)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 3), (17, 1), (1259, 1), (112580099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 3), (17, 1), (1259, 1), (112580099, 1)] : List FactorBlock).map factorBlockValue).prod) = 1652952575203343 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_7
      · exact prime_thirtySevenAI_17
      · exact prime_thirtySevenAI_1259
      · exact prime_thirtySevenAI_112580099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1652952575203343) ^ 826476287601671 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 1652952575203343) ^ 236136082171906 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 1652952575203343) ^ 97232504423726 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 1652952575203343) ^ 1312909114538 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 1652952575203343) ^ 14682458 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_1667237541899513 : Nat.Prime 1667237541899513 := by
  apply lucas_primality 1667237541899513 (3 : ZMod 1667237541899513)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (41, 1), (462094662389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (41, 1), (462094662389, 1)] : List FactorBlock).map factorBlockValue).prod) = 1667237541899513 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_11
      · exact prime_thirtySevenAI_41
      · exact prime_thirtySevenAI_462094662389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1667237541899513) ^ 833618770949756 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 151567049263592 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 40664330290232 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1667237541899513) ^ 3608 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_1691591597331869 : Nat.Prime 1691591597331869 := by
  apply lucas_primality 1691591597331869 (2 : ZMod 1691591597331869)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (139, 1), (363157, 1), (8377729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (139, 1), (363157, 1), (8377729, 1)] : List FactorBlock).map factorBlockValue).prod) = 1691591597331869 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_139
      · exact prime_thirtySevenAI_363157
      · exact prime_thirtySevenAI_8377729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1691591597331869) ^ 845795798665934 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1691591597331869) ^ 12169723721812 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1691591597331869) ^ 4658017324 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1691591597331869) ^ 201915292 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_1806210835639541 : Nat.Prime 1806210835639541 := by
  apply lucas_primality 1806210835639541 (2 : ZMod 1806210835639541)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (11, 1), (823, 1), (1871, 1), (5331779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (11, 1), (823, 1), (1871, 1), (5331779, 1)] : List FactorBlock).map factorBlockValue).prod) = 1806210835639541 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_5
      · exact prime_thirtySevenAI_11
      · exact prime_thirtySevenAI_823
      · exact prime_thirtySevenAI_1871
      · exact prime_thirtySevenAI_5331779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1806210835639541) ^ 903105417819770 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1806210835639541) ^ 361242167127908 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1806210835639541) ^ 164200985058140 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1806210835639541) ^ 2194666871980 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1806210835639541) ^ 965371905740 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1806210835639541) ^ 338763260 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_2045004777760537 : Nat.Prime 2045004777760537 := by
  apply lucas_primality 2045004777760537 (7 : ZMod 2045004777760537)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (57713, 1), (492139451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (57713, 1), (492139451, 1)] : List FactorBlock).map factorBlockValue).prod) = 2045004777760537 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_57713
      · exact prime_thirtySevenAI_492139451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 2045004777760537) ^ 1022502388880268 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (7 : ZMod 2045004777760537) ^ 681668259253512 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (7 : ZMod 2045004777760537) ^ 35434040472 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (7 : ZMod 2045004777760537) ^ 4155336 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_2729730586335979 : Nat.Prime 2729730586335979 := by
  apply lucas_primality 2729730586335979 (2 : ZMod 2729730586335979)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (109, 1), (2957, 1), (1411531951, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (109, 1), (2957, 1), (1411531951, 1)] : List FactorBlock).map factorBlockValue).prod) = 2729730586335979 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_109
      · exact prime_thirtySevenAI_2957
      · exact prime_thirtySevenAI_1411531951
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2729730586335979) ^ 1364865293167989 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2729730586335979) ^ 909910195445326 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2729730586335979) ^ 25043399874642 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2729730586335979) ^ 923141895954 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2729730586335979) ^ 1933878 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_3002360278296961 : Nat.Prime 3002360278296961 := by
  apply lucas_primality 3002360278296961 (29 : ZMod 3002360278296961)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 2), (5, 1), (7, 1), (239, 1), (311561927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 2), (5, 1), (7, 1), (239, 1), (311561927, 1)] : List FactorBlock).map factorBlockValue).prod) = 3002360278296961 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_5
      · exact prime_thirtySevenAI_7
      · exact prime_thirtySevenAI_239
      · exact prime_thirtySevenAI_311561927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (29 : ZMod 3002360278296961) ^ 1501180139148480 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (29 : ZMod 3002360278296961) ^ 1000786759432320 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (29 : ZMod 3002360278296961) ^ 600472055659392 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (29 : ZMod 3002360278296961) ^ 428908611185280 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (29 : ZMod 3002360278296961) ^ 12562176896640 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (29 : ZMod 3002360278296961) ^ 9636480 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_3419329630390727 : Nat.Prime 3419329630390727 := by
  apply lucas_primality 3419329630390727 (5 : ZMod 3419329630390727)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 2), (23, 1), (61, 1), (89, 1), (131, 2), (4721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 2), (23, 1), (61, 1), (89, 1), (131, 2), (4721, 1)] : List FactorBlock).map factorBlockValue).prod) = 3419329630390727 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_13
      · exact prime_thirtySevenAI_23
      · exact prime_thirtySevenAI_61
      · exact prime_thirtySevenAI_89
      · exact prime_thirtySevenAI_131
      · exact prime_thirtySevenAI_4721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 3419329630390727) ^ 1709664815195363 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 3419329630390727) ^ 263025356183902 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 3419329630390727) ^ 148666505669162 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 3419329630390727) ^ 56054584104766 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 3419329630390727) ^ 38419434049334 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 3419329630390727) ^ 26101752903746 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 3419329630390727) ^ 724280794406 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_3726091731800909 : Nat.Prime 3726091731800909 := by
  apply lucas_primality 3726091731800909 (2 : ZMod 3726091731800909)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (307, 1), (178486862033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (307, 1), (178486862033, 1)] : List FactorBlock).map factorBlockValue).prod) = 3726091731800909 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_17
      · exact prime_thirtySevenAI_307
      · exact prime_thirtySevenAI_178486862033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3726091731800909) ^ 1863045865900454 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3726091731800909) ^ 219181866576524 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3726091731800909) ^ 12137106618244 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3726091731800909) ^ 20876 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_4605990429531731 : Nat.Prime 4605990429531731 := by
  apply lucas_primality 4605990429531731 (2 : ZMod 4605990429531731)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (18479933, 1), (24924281, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (18479933, 1), (24924281, 1)] : List FactorBlock).map factorBlockValue).prod) = 4605990429531731 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_5
      · exact prime_thirtySevenAI_18479933
      · exact prime_thirtySevenAI_24924281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4605990429531731) ^ 2302995214765865 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 4605990429531731) ^ 921198085906346 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 4605990429531731) ^ 249242810 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 4605990429531731) ^ 184799330 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_5265946841622461 : Nat.Prime 5265946841622461 := by
  apply lucas_primality 5265946841622461 (3 : ZMod 5265946841622461)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (47, 1), (719, 1), (1113067973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (47, 1), (719, 1), (1113067973, 1)] : List FactorBlock).map factorBlockValue).prod) = 5265946841622461 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_5
      · exact prime_thirtySevenAI_7
      · exact prime_thirtySevenAI_47
      · exact prime_thirtySevenAI_719
      · exact prime_thirtySevenAI_1113067973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 5265946841622461) ^ 2632973420811230 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 5265946841622461) ^ 1053189368324492 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 5265946841622461) ^ 752278120231780 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 5265946841622461) ^ 112041422162180 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 5265946841622461) ^ 7323987262340 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 5265946841622461) ^ 4731020 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_6491711902208917 : Nat.Prime 6491711902208917 := by
  apply lucas_primality 6491711902208917 (2 : ZMod 6491711902208917)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (139, 1), (3891913610437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (139, 1), (3891913610437, 1)] : List FactorBlock).map factorBlockValue).prod) = 6491711902208917 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_139
      · exact prime_thirtySevenAI_3891913610437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 6491711902208917) ^ 3245855951104458 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 6491711902208917) ^ 2163903967402972 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 6491711902208917) ^ 46702963325244 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 6491711902208917) ^ 1668 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_6906908323857613 : Nat.Prime 6906908323857613 := by
  apply lucas_primality 6906908323857613 (2 : ZMod 6906908323857613)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 3), (19, 1), (71, 1), (1243931243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 3), (19, 1), (71, 1), (1243931243, 1)] : List FactorBlock).map factorBlockValue).prod) = 6906908323857613 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_7
      · exact prime_thirtySevenAI_19
      · exact prime_thirtySevenAI_71
      · exact prime_thirtySevenAI_1243931243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6906908323857613) ^ 3453454161928806 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 6906908323857613) ^ 2302302774619204 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 6906908323857613) ^ 986701189122516 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 6906908323857613) ^ 363521490729348 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 6906908323857613) ^ 97280398927572 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 6906908323857613) ^ 5552484 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_8220797460937469 : Nat.Prime 8220797460937469 := by
  apply lucas_primality 8220797460937469 (2 : ZMod 8220797460937469)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (186836305930397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (186836305930397, 1)] : List FactorBlock).map factorBlockValue).prod) = 8220797460937469 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_11
      · exact prime_thirtySevenAI_186836305930397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 8220797460937469) ^ 4110398730468734 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 8220797460937469) ^ 747345223721588 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 8220797460937469) ^ 44 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_9044387076075733 : Nat.Prime 9044387076075733 := by
  apply lucas_primality 9044387076075733 (2 : ZMod 9044387076075733)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (809, 1), (3539, 1), (29250029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (809, 1), (3539, 1), (29250029, 1)] : List FactorBlock).map factorBlockValue).prod) = 9044387076075733 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_809
      · exact prime_thirtySevenAI_3539
      · exact prime_thirtySevenAI_29250029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9044387076075733) ^ 4522193538037866 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 9044387076075733) ^ 3014795692025244 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 9044387076075733) ^ 11179712084148 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 9044387076075733) ^ 2555633533788 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 9044387076075733) ^ 309209508 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_17932013948054243 : Nat.Prime 17932013948054243 := by
  apply lucas_primality 17932013948054243 (2 : ZMod 17932013948054243)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (113, 1), (293, 1), (270802711469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (113, 1), (293, 1), (270802711469, 1)] : List FactorBlock).map factorBlockValue).prod) = 17932013948054243 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_113
      · exact prime_thirtySevenAI_293
      · exact prime_thirtySevenAI_270802711469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 17932013948054243) ^ 8966006974027121 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 17932013948054243) ^ 158690388920834 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 17932013948054243) ^ 61201412791994 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 17932013948054243) ^ 66218 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_19744026879106723 : Nat.Prime 19744026879106723 := by
  apply lucas_primality 19744026879106723 (2 : ZMod 19744026879106723)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (607, 1), (5421204524741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (607, 1), (5421204524741, 1)] : List FactorBlock).map factorBlockValue).prod) = 19744026879106723 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_607
      · exact prime_thirtySevenAI_5421204524741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 19744026879106723) ^ 9872013439553361 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 19744026879106723) ^ 6581342293035574 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 19744026879106723) ^ 32527227148446 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 19744026879106723) ^ 3642 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_44351678062715447 : Nat.Prime 44351678062715447 := by
  apply lucas_primality 44351678062715447 (5 : ZMod 44351678062715447)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 1), (4021, 1), (149491, 1), (857951, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 1), (4021, 1), (149491, 1), (857951, 1)] : List FactorBlock).map factorBlockValue).prod) = 44351678062715447 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_43
      · exact prime_thirtySevenAI_4021
      · exact prime_thirtySevenAI_149491
      · exact prime_thirtySevenAI_857951
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 44351678062715447) ^ 22175839031357723 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 44351678062715447) ^ 1031434373551522 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 44351678062715447) ^ 11030011952926 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 44351678062715447) ^ 296684603506 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 44351678062715447) ^ 51694884746 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_71200366012608817 : Nat.Prime 71200366012608817 := by
  apply lucas_primality 71200366012608817 (5 : ZMod 71200366012608817)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (31, 1), (2207, 1), (9283, 1), (2335547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (31, 1), (2207, 1), (9283, 1), (2335547, 1)] : List FactorBlock).map factorBlockValue).prod) = 71200366012608817 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_31
      · exact prime_thirtySevenAI_2207
      · exact prime_thirtySevenAI_9283
      · exact prime_thirtySevenAI_2335547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 71200366012608817) ^ 35600183006304408 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 71200366012608817) ^ 23733455337536272 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 71200366012608817) ^ 2296786000406736 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 71200366012608817) ^ 32261153607888 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 71200366012608817) ^ 7669973716752 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 71200366012608817) ^ 30485520528 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_88633326395586017 : Nat.Prime 88633326395586017 := by
  apply lucas_primality 88633326395586017 (3 : ZMod 88633326395586017)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (11, 1), (31, 1), (619, 1), (35423, 1), (370439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (11, 1), (31, 1), (619, 1), (35423, 1), (370439, 1)] : List FactorBlock).map factorBlockValue).prod) = 88633326395586017 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_11
      · exact prime_thirtySevenAI_31
      · exact prime_thirtySevenAI_619
      · exact prime_thirtySevenAI_35423
      · exact prime_thirtySevenAI_370439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 88633326395586017) ^ 44316663197793008 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 88633326395586017) ^ 8057575126871456 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 88633326395586017) ^ 2859139561147936 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 88633326395586017) ^ 143187926325664 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 88633326395586017) ^ 2502140597792 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 88633326395586017) ^ 239265645344 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_132877257646729993 : Nat.Prime 132877257646729993 := by
  apply lucas_primality 132877257646729993 (7 : ZMod 132877257646729993)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (5824043, 1), (86421571, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (5824043, 1), (86421571, 1)] : List FactorBlock).map factorBlockValue).prod) = 132877257646729993 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_11
      · exact prime_thirtySevenAI_5824043
      · exact prime_thirtySevenAI_86421571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 132877257646729993) ^ 66438628823364996 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (7 : ZMod 132877257646729993) ^ 44292419215576664 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (7 : ZMod 132877257646729993) ^ 12079750695157272 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (7 : ZMod 132877257646729993) ^ 22815294744 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (7 : ZMod 132877257646729993) ^ 1537547352 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_147669447533742787 : Nat.Prime 147669447533742787 := by
  apply lucas_primality 147669447533742787 (2 : ZMod 147669447533742787)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 2), (17623, 1), (1453236077, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 2), (17623, 1), (1453236077, 1)] : List FactorBlock).map factorBlockValue).prod) = 147669447533742787 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_31
      · exact prime_thirtySevenAI_17623
      · exact prime_thirtySevenAI_1453236077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 147669447533742787) ^ 73834723766871393 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 147669447533742787) ^ 49223149177914262 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 147669447533742787) ^ 4763530565604606 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 147669447533742787) ^ 8379359219982 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 147669447533742787) ^ 101614218 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_148560364691441459 : Nat.Prime 148560364691441459 := by
  apply lucas_primality 148560364691441459 (2 : ZMod 148560364691441459)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (29, 2), (151, 1), (83560682417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (29, 2), (151, 1), (83560682417, 1)] : List FactorBlock).map factorBlockValue).prod) = 148560364691441459 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_7
      · exact prime_thirtySevenAI_29
      · exact prime_thirtySevenAI_151
      · exact prime_thirtySevenAI_83560682417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 148560364691441459) ^ 74280182345720729 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 148560364691441459) ^ 21222909241634494 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 148560364691441459) ^ 5122771196256602 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 148560364691441459) ^ 983843474777758 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 148560364691441459) ^ 1777874 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_221169767348143363 : Nat.Prime 221169767348143363 := by
  apply lucas_primality 221169767348143363 (2 : ZMod 221169767348143363)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (5265946841622461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (5265946841622461, 1)] : List FactorBlock).map factorBlockValue).prod) = 221169767348143363 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_7
      · exact prime_thirtySevenAI_5265946841622461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 221169767348143363) ^ 110584883674071681 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 221169767348143363) ^ 73723255782714454 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 221169767348143363) ^ 31595681049734766 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 221169767348143363) ^ 42 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_483498887150858771 : Nat.Prime 483498887150858771 := by
  apply lucas_primality 483498887150858771 (2 : ZMod 483498887150858771)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (29, 1), (1667237541899513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (29, 1), (1667237541899513, 1)] : List FactorBlock).map factorBlockValue).prod) = 483498887150858771 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_5
      · exact prime_thirtySevenAI_29
      · exact prime_thirtySevenAI_1667237541899513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 483498887150858771) ^ 241749443575429385 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 96699777430171754 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 16672375418995130 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 483498887150858771) ^ 290 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_563585608037072707 : Nat.Prime 563585608037072707 := by
  apply lucas_primality 563585608037072707 (3 : ZMod 563585608037072707)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (61717, 1), (1521962095903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (61717, 1), (1521962095903, 1)] : List FactorBlock).map factorBlockValue).prod) = 563585608037072707 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_61717
      · exact prime_thirtySevenAI_1521962095903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 563585608037072707) ^ 281792804018536353 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 187861869345690902 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 9131772575418 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 563585608037072707) ^ 370302 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_687107008742993989 : Nat.Prime 687107008742993989 := by
  apply lucas_primality 687107008742993989 (6 : ZMod 687107008742993989)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (40000963, 1), (75338867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (40000963, 1), (75338867, 1)] : List FactorBlock).map factorBlockValue).prod) = 687107008742993989 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_19
      · exact prime_thirtySevenAI_40000963
      · exact prime_thirtySevenAI_75338867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 687107008742993989) ^ 343553504371496994 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (6 : ZMod 687107008742993989) ^ 229035669580997996 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (6 : ZMod 687107008742993989) ^ 36163526775947052 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (6 : ZMod 687107008742993989) ^ 17177261676 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (6 : ZMod 687107008742993989) ^ 9120219564 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_996870010236610751 : Nat.Prime 996870010236610751 := by
  apply lucas_primality 996870010236610751 (13 : ZMod 996870010236610751)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 3), (1801, 1), (675347, 1), (3278369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 3), (1801, 1), (675347, 1), (3278369, 1)] : List FactorBlock).map factorBlockValue).prod) = 996870010236610751 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_5
      · exact prime_thirtySevenAI_1801
      · exact prime_thirtySevenAI_675347
      · exact prime_thirtySevenAI_3278369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 996870010236610751) ^ 498435005118305375 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (13 : ZMod 996870010236610751) ^ 199374002047322150 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (13 : ZMod 996870010236610751) ^ 553509167260750 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (13 : ZMod 996870010236610751) ^ 1476085642250 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (13 : ZMod 996870010236610751) ^ 304074986750 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_1623927933438594241 : Nat.Prime 1623927933438594241 := by
  apply lucas_primality 1623927933438594241 (7 : ZMod 1623927933438594241)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (5, 1), (1691591597331869, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (5, 1), (1691591597331869, 1)] : List FactorBlock).map factorBlockValue).prod) = 1623927933438594241 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_5
      · exact prime_thirtySevenAI_1691591597331869
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 1623927933438594241) ^ 811963966719297120 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (7 : ZMod 1623927933438594241) ^ 541309311146198080 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (7 : ZMod 1623927933438594241) ^ 324785586687718848 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (7 : ZMod 1623927933438594241) ^ 960 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_2126036122347679889 : Nat.Prime 2126036122347679889 := by
  apply lucas_primality 2126036122347679889 (3 : ZMod 2126036122347679889)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (132877257646729993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (132877257646729993, 1)] : List FactorBlock).map factorBlockValue).prod) = 2126036122347679889 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_132877257646729993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 2126036122347679889) ^ 1063018061173839944 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 2126036122347679889) ^ 16 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_2609635767134347493 : Nat.Prime 2609635767134347493 := by
  apply lucas_primality 2609635767134347493 (2 : ZMod 2609635767134347493)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (61, 1), (4463, 1), (2396421365411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (61, 1), (4463, 1), (2396421365411, 1)] : List FactorBlock).map factorBlockValue).prod) = 2609635767134347493 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_61
      · exact prime_thirtySevenAI_4463
      · exact prime_thirtySevenAI_2396421365411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2609635767134347493) ^ 1304817883567173746 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2609635767134347493) ^ 42780914215317172 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2609635767134347493) ^ 584726813160284 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2609635767134347493) ^ 1088972 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_3203906746898167489 : Nat.Prime 3203906746898167489 := by
  apply lucas_primality 3203906746898167489 (29 : ZMod 3203906746898167489)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (3466867, 1), (1604427889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (3466867, 1), (1604427889, 1)] : List FactorBlock).map factorBlockValue).prod) = 3203906746898167489 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_3466867
      · exact prime_thirtySevenAI_1604427889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (29 : ZMod 3203906746898167489) ^ 1601953373449083744 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (29 : ZMod 3203906746898167489) ^ 1067968915632722496 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (29 : ZMod 3203906746898167489) ^ 924150464064 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (29 : ZMod 3203906746898167489) ^ 1996915392 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_3352007938325760943 : Nat.Prime 3352007938325760943 := by
  apply lucas_primality 3352007938325760943 (3 : ZMod 3352007938325760943)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (89, 1), (16608877, 1), (377940569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (89, 1), (16608877, 1), (377940569, 1)] : List FactorBlock).map factorBlockValue).prod) = 3352007938325760943 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_89
      · exact prime_thirtySevenAI_16608877
      · exact prime_thirtySevenAI_377940569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3352007938325760943) ^ 1676003969162880471 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 3352007938325760943) ^ 1117335979441920314 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 3352007938325760943) ^ 37663010542986078 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 3352007938325760943) ^ 201820263846 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 3352007938325760943) ^ 8869140318 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_7168692794733793951 : Nat.Prime 7168692794733793951 := by
  apply lucas_primality 7168692794733793951 (6 : ZMod 7168692794733793951)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (11, 2), (29, 1), (116107, 1), (117302411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (11, 2), (29, 1), (116107, 1), (117302411, 1)] : List FactorBlock).map factorBlockValue).prod) = 7168692794733793951 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_5
      · exact prime_thirtySevenAI_11
      · exact prime_thirtySevenAI_29
      · exact prime_thirtySevenAI_116107
      · exact prime_thirtySevenAI_117302411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 7168692794733793951) ^ 3584346397366896975 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (6 : ZMod 7168692794733793951) ^ 2389564264911264650 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (6 : ZMod 7168692794733793951) ^ 1433738558946758790 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (6 : ZMod 7168692794733793951) ^ 651699344975799450 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (6 : ZMod 7168692794733793951) ^ 247196303266682550 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (6 : ZMod 7168692794733793951) ^ 61742124029850 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (6 : ZMod 7168692794733793951) ^ 61112919450 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_7524747705762493343 : Nat.Prime 7524747705762493343 := by
  apply lucas_primality 7524747705762493343 (5 : ZMod 7524747705762493343)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (337, 1), (4397, 1), (2539075302139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (337, 1), (4397, 1), (2539075302139, 1)] : List FactorBlock).map factorBlockValue).prod) = 7524747705762493343 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_337
      · exact prime_thirtySevenAI_4397
      · exact prime_thirtySevenAI_2539075302139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 7524747705762493343) ^ 3762373852881246671 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 7524747705762493343) ^ 22328628207010366 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 7524747705762493343) ^ 1711336753641686 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 7524747705762493343) ^ 2963578 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_9246544974693328613 : Nat.Prime 9246544974693328613 := by
  apply lucas_primality 9246544974693328613 (2 : ZMod 9246544974693328613)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (53, 1), (28949, 1), (1506641962849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (53, 1), (28949, 1), (1506641962849, 1)] : List FactorBlock).map factorBlockValue).prod) = 9246544974693328613 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_53
      · exact prime_thirtySevenAI_28949
      · exact prime_thirtySevenAI_1506641962849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 9246544974693328613) ^ 4623272487346664306 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 9246544974693328613) ^ 174463112730062804 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 9246544974693328613) ^ 319408096123988 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 9246544974693328613) ^ 6137188 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_15657814602806084959 : Nat.Prime 15657814602806084959 := by
  apply lucas_primality 15657814602806084959 (3 : ZMod 15657814602806084959)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2609635767134347493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2609635767134347493, 1)] : List FactorBlock).map factorBlockValue).prod) = 15657814602806084959 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_2609635767134347493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 15657814602806084959) ^ 7828907301403042479 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 15657814602806084959) ^ 5219271534268694986 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 15657814602806084959) ^ 6 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_21293335073769464527 : Nat.Prime 21293335073769464527 := by
  apply lucas_primality 21293335073769464527 (5 : ZMod 21293335073769464527)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (113, 1), (1652952575203343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (113, 1), (1652952575203343, 1)] : List FactorBlock).map factorBlockValue).prod) = 21293335073769464527 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_19
      · exact prime_thirtySevenAI_113
      · exact prime_thirtySevenAI_1652952575203343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 21293335073769464527) ^ 10646667536884732263 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 21293335073769464527) ^ 7097778357923154842 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 21293335073769464527) ^ 1120701845987866554 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 21293335073769464527) ^ 188436593573181102 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 21293335073769464527) ^ 12882 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_53258081425721101711 : Nat.Prime 53258081425721101711 := by
  apply lucas_primality 53258081425721101711 (6 : ZMod 53258081425721101711)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (11, 1), (17932013948054243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (11, 1), (17932013948054243, 1)] : List FactorBlock).map factorBlockValue).prod) = 53258081425721101711 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_5
      · exact prime_thirtySevenAI_11
      · exact prime_thirtySevenAI_17932013948054243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 53258081425721101711) ^ 26629040712860550855 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (6 : ZMod 53258081425721101711) ^ 17752693808573700570 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (6 : ZMod 53258081425721101711) ^ 10651616285144220342 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (6 : ZMod 53258081425721101711) ^ 4841643765974645610 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (6 : ZMod 53258081425721101711) ^ 2970 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_78444589946058257989 : Nat.Prime 78444589946058257989 := by
  apply lucas_primality 78444589946058257989 (2 : ZMod 78444589946058257989)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (47, 1), (109, 1), (421, 1), (275538705823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (47, 1), (109, 1), (421, 1), (275538705823, 1)] : List FactorBlock).map factorBlockValue).prod) = 78444589946058257989 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_11
      · exact prime_thirtySevenAI_47
      · exact prime_thirtySevenAI_109
      · exact prime_thirtySevenAI_421
      · exact prime_thirtySevenAI_275538705823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 78444589946058257989) ^ 39222294973029128994 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 78444589946058257989) ^ 26148196648686085996 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 78444589946058257989) ^ 7131326358732568908 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 78444589946058257989) ^ 1669033828639537404 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 78444589946058257989) ^ 719675137119800532 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 78444589946058257989) ^ 186329192270922228 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 78444589946058257989) ^ 284695356 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_121673879090654553433 : Nat.Prime 121673879090654553433 := by
  apply lucas_primality 121673879090654553433 (5 : ZMod 121673879090654553433)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 5), (7, 2), (11, 1), (116121417396427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 5), (7, 2), (11, 1), (116121417396427, 1)] : List FactorBlock).map factorBlockValue).prod) = 121673879090654553433 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_7
      · exact prime_thirtySevenAI_11
      · exact prime_thirtySevenAI_116121417396427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 121673879090654553433) ^ 60836939545327276716 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 121673879090654553433) ^ 40557959696884851144 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 121673879090654553433) ^ 17381982727236364776 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 121673879090654553433) ^ 11061261735514050312 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 121673879090654553433) ^ 1047816 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_184930899493866572261 : Nat.Prime 184930899493866572261 := by
  apply lucas_primality 184930899493866572261 (2 : ZMod 184930899493866572261)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (9246544974693328613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (9246544974693328613, 1)] : List FactorBlock).map factorBlockValue).prod) = 184930899493866572261 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_5
      · exact prime_thirtySevenAI_9246544974693328613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 184930899493866572261) ^ 92465449746933286130 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 184930899493866572261) ^ 36986179898773314452 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 184930899493866572261) ^ 20 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_466900475261349035617 : Nat.Prime 466900475261349035617 := by
  apply lucas_primality 466900475261349035617 (10 : ZMod 466900475261349035617)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (17, 1), (23, 1), (101, 1), (123155823283931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (17, 1), (23, 1), (101, 1), (123155823283931, 1)] : List FactorBlock).map factorBlockValue).prod) = 466900475261349035617 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_17
      · exact prime_thirtySevenAI_23
      · exact prime_thirtySevenAI_101
      · exact prime_thirtySevenAI_123155823283931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 466900475261349035617) ^ 233450237630674517808 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (10 : ZMod 466900475261349035617) ^ 155633491753783011872 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (10 : ZMod 466900475261349035617) ^ 27464733838902884448 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (10 : ZMod 466900475261349035617) ^ 20300020663536914592 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (10 : ZMod 466900475261349035617) ^ 4622776982785634016 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (10 : ZMod 466900475261349035617) ^ 3791136 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_687874839503081087063 : Nat.Prime 687874839503081087063 := by
  apply lucas_primality 687874839503081087063 (5 : ZMod 687874839503081087063)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (54311, 1), (243433, 1), (1530253061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (54311, 1), (243433, 1), (1530253061, 1)] : List FactorBlock).map factorBlockValue).prod) = 687874839503081087063 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_17
      · exact prime_thirtySevenAI_54311
      · exact prime_thirtySevenAI_243433
      · exact prime_thirtySevenAI_1530253061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 687874839503081087063) ^ 343937419751540543531 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 687874839503081087063) ^ 40463225853122416886 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 687874839503081087063) ^ 12665479175546042 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 687874839503081087063) ^ 2825725515863014 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 687874839503081087063) ^ 449517048542 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_1328085705243625636327 : Nat.Prime 1328085705243625636327 := by
  apply lucas_primality 1328085705243625636327 (3 : ZMod 1328085705243625636327)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1268143, 1), (174544682690047, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1268143, 1), (174544682690047, 1)] : List FactorBlock).map factorBlockValue).prod) = 1328085705243625636327 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_1268143
      · exact prime_thirtySevenAI_174544682690047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1328085705243625636327) ^ 664042852621812818163 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1328085705243625636327) ^ 442695235081208545442 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1328085705243625636327) ^ 1047268096140282 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 1328085705243625636327) ^ 7608858 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_2291539082278737626663 : Nat.Prime 2291539082278737626663 := by
  apply lucas_primality 2291539082278737626663 (10 : ZMod 2291539082278737626663)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (107, 1), (563585608037072707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (107, 1), (563585608037072707, 1)] : List FactorBlock).map factorBlockValue).prod) = 2291539082278737626663 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_19
      · exact prime_thirtySevenAI_107
      · exact prime_thirtySevenAI_563585608037072707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 2291539082278737626663) ^ 1145769541139368813331 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 120607320119933559298 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 21416253105408762866 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (10 : ZMod 2291539082278737626663) ^ 4066 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_4795568856230357219369 : Nat.Prime 4795568856230357219369 := by
  apply lucas_primality 4795568856230357219369 (3 : ZMod 4795568856230357219369)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (219599, 1), (2729730586335979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (219599, 1), (2729730586335979, 1)] : List FactorBlock).map factorBlockValue).prod) = 4795568856230357219369 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_219599
      · exact prime_thirtySevenAI_2729730586335979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 4795568856230357219369) ^ 2397784428115178609684 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 4795568856230357219369) ^ 21837844690687832 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 4795568856230357219369) ^ 1756792 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_29913859757731797447577 : Nat.Prime 29913859757731797447577 := by
  apply lucas_primality 29913859757731797447577 (5 : ZMod 29913859757731797447577)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (17, 1), (859, 1), (659963, 1), (129330077641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (17, 1), (859, 1), (659963, 1), (129330077641, 1)] : List FactorBlock).map factorBlockValue).prod) = 29913859757731797447577 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_17
      · exact prime_thirtySevenAI_859
      · exact prime_thirtySevenAI_659963
      · exact prime_thirtySevenAI_129330077641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 29913859757731797447577) ^ 14956929878865898723788 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 29913859757731797447577) ^ 9971286585910599149192 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 29913859757731797447577) ^ 1759638809278341026328 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 29913859757731797447577) ^ 34824050940316411464 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 29913859757731797447577) ^ 45326570970996552 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 29913859757731797447577) ^ 231298552536 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_30480987451784118330119 : Nat.Prime 30480987451784118330119 := by
  apply lucas_primality 30480987451784118330119 (11 : ZMod 30480987451784118330119)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (149, 1), (56611, 1), (138077, 1), (13085508353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (149, 1), (56611, 1), (138077, 1), (13085508353, 1)] : List FactorBlock).map factorBlockValue).prod) = 30480987451784118330119 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_149
      · exact prime_thirtySevenAI_56611
      · exact prime_thirtySevenAI_138077
      · exact prime_thirtySevenAI_13085508353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 30480987451784118330119) ^ 15240493725892059165059 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (11 : ZMod 30480987451784118330119) ^ 204570385582443747182 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (11 : ZMod 30480987451784118330119) ^ 538428705583439938 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (11 : ZMod 30480987451784118330119) ^ 220753546584761534 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (11 : ZMod 30480987451784118330119) ^ 2329369760006 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_31500418176597294039733 : Nat.Prime 31500418176597294039733 := by
  apply lucas_primality 31500418176597294039733 (2 : ZMod 31500418176597294039733)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (31, 1), (551951, 1), (153416777006431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (31, 1), (551951, 1), (153416777006431, 1)] : List FactorBlock).map factorBlockValue).prod) = 31500418176597294039733 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_31
      · exact prime_thirtySevenAI_551951
      · exact prime_thirtySevenAI_153416777006431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 31500418176597294039733) ^ 15750209088298647019866 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 31500418176597294039733) ^ 10500139392199098013244 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 31500418176597294039733) ^ 1016142521825719162572 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 31500418176597294039733) ^ 57071041046392332 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 31500418176597294039733) ^ 205325772 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_263258816414029741265627 : Nat.Prime 263258816414029741265627 := by
  apply lucas_primality 263258816414029741265627 (2 : ZMod 263258816414029741265627)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (461, 1), (1291, 1), (221169767348143363, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (461, 1), (1291, 1), (221169767348143363, 1)] : List FactorBlock).map factorBlockValue).prod) = 263258816414029741265627 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_461
      · exact prime_thirtySevenAI_1291
      · exact prime_thirtySevenAI_221169767348143363
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 263258816414029741265627) ^ 131629408207014870632813 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 263258816414029741265627) ^ 571060339292906163266 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 263258816414029741265627) ^ 203918525494988180686 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 263258816414029741265627) ^ 1190302 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_378005018119167528476797 : Nat.Prime 378005018119167528476797 := by
  apply lucas_primality 378005018119167528476797 (5 : ZMod 378005018119167528476797)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (31500418176597294039733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (31500418176597294039733, 1)] : List FactorBlock).map factorBlockValue).prod) = 378005018119167528476797 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_31500418176597294039733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 378005018119167528476797) ^ 189002509059583764238398 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 378005018119167528476797) ^ 126001672706389176158932 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 378005018119167528476797) ^ 12 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_478503956680352052089527 : Nat.Prime 478503956680352052089527 := by
  apply lucas_primality 478503956680352052089527 (5 : ZMod 478503956680352052089527)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (59, 1), (10159, 1), (44351678062715447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (59, 1), (10159, 1), (44351678062715447, 1)] : List FactorBlock).map factorBlockValue).prod) = 478503956680352052089527 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_59
      · exact prime_thirtySevenAI_10159
      · exact prime_thirtySevenAI_44351678062715447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 478503956680352052089527) ^ 239251978340176026044763 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 478503956680352052089527) ^ 159501318893450684029842 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 478503956680352052089527) ^ 8110236553904272069314 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 478503956680352052089527) ^ 47101482102603804714 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 478503956680352052089527) ^ 10788858 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_572481379798777975656913 : Nat.Prime 572481379798777975656913 := by
  apply lucas_primality 572481379798777975656913 (5 : ZMod 572481379798777975656913)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (37, 1), (426554057, 1), (755691134491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (37, 1), (426554057, 1), (755691134491, 1)] : List FactorBlock).map factorBlockValue).prod) = 572481379798777975656913 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_37
      · exact prime_thirtySevenAI_426554057
      · exact prime_thirtySevenAI_755691134491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 572481379798777975656913) ^ 286240689899388987828456 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 572481379798777975656913) ^ 190827126599592658552304 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 572481379798777975656913) ^ 15472469724291296639376 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 572481379798777975656913) ^ 1342107454856016 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (5 : ZMod 572481379798777975656913) ^ 757560005232 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_1477035207718950023565653 : Nat.Prime 1477035207718950023565653 := by
  apply lucas_primality 1477035207718950023565653 (13 : ZMod 1477035207718950023565653)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (11, 1), (4795568856230357219369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (11, 1), (4795568856230357219369, 1)] : List FactorBlock).map factorBlockValue).prod) = 1477035207718950023565653 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_7
      · exact prime_thirtySevenAI_11
      · exact prime_thirtySevenAI_4795568856230357219369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 1477035207718950023565653) ^ 738517603859475011782826 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (13 : ZMod 1477035207718950023565653) ^ 211005029674135717652236 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (13 : ZMod 1477035207718950023565653) ^ 134275927974450002142332 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (13 : ZMod 1477035207718950023565653) ^ 308 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_2865069079892875550034083 : Nat.Prime 2865069079892875550034083 := by
  apply lucas_primality 2865069079892875550034083 (2 : ZMod 2865069079892875550034083)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5573, 1), (80251, 1), (10029797, 1), (319354811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5573, 1), (80251, 1), (10029797, 1), (319354811, 1)] : List FactorBlock).map factorBlockValue).prod) = 2865069079892875550034083 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_5573
      · exact prime_thirtySevenAI_80251
      · exact prime_thirtySevenAI_10029797
      · exact prime_thirtySevenAI_319354811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2865069079892875550034083) ^ 1432534539946437775017041 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2865069079892875550034083) ^ 514098166139041010234 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2865069079892875550034083) ^ 35701350511431328582 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2865069079892875550034083) ^ 285655739582054906 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2865069079892875550034083) ^ 8971429210417862 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_2906376633566169948702437 : Nat.Prime 2906376633566169948702437 := by
  apply lucas_primality 2906376633566169948702437 (2 : ZMod 2906376633566169948702437)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (43, 1), (1031, 1), (22109, 1), (741302869766497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (43, 1), (1031, 1), (22109, 1), (741302869766497, 1)] : List FactorBlock).map factorBlockValue).prod) = 2906376633566169948702437 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_43
      · exact prime_thirtySevenAI_1031
      · exact prime_thirtySevenAI_22109
      · exact prime_thirtySevenAI_741302869766497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2906376633566169948702437) ^ 1453188316783084974351218 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2906376633566169948702437) ^ 67590154268980696481452 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2906376633566169948702437) ^ 2818988005398806933756 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2906376633566169948702437) ^ 131456720501432446004 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 2906376633566169948702437) ^ 3920633188 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_3043263859176598295388923 : Nat.Prime 3043263859176598295388923 := by
  apply lucas_primality 3043263859176598295388923 (2 : ZMod 3043263859176598295388923)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (107, 1), (660853, 1), (5442289, 1), (3954024619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (107, 1), (660853, 1), (5442289, 1), (3954024619, 1)] : List FactorBlock).map factorBlockValue).prod) = 3043263859176598295388923 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_107
      · exact prime_thirtySevenAI_660853
      · exact prime_thirtySevenAI_5442289
      · exact prime_thirtySevenAI_3954024619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3043263859176598295388923) ^ 1521631929588299147694461 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3043263859176598295388923) ^ 28441718310061666312046 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3043263859176598295388923) ^ 4605054163598558674 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3043263859176598295388923) ^ 559188212749561498 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 3043263859176598295388923) ^ 769662344678638 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_5805424646556658778755193 : Nat.Prime 5805424646556658778755193 := by
  apply lucas_primality 5805424646556658778755193 (3 : ZMod 5805424646556658778755193)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17, 1), (2692973, 1), (121084441, 1), (130910579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17, 1), (2692973, 1), (121084441, 1), (130910579, 1)] : List FactorBlock).map factorBlockValue).prod) = 5805424646556658778755193 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_17
      · exact prime_thirtySevenAI_2692973
      · exact prime_thirtySevenAI_121084441
      · exact prime_thirtySevenAI_130910579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 5805424646556658778755193) ^ 2902712323278329389377596 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 5805424646556658778755193) ^ 341495567444509339926776 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 5805424646556658778755193) ^ 2155767861971382104 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 5805424646556658778755193) ^ 47945257033945912 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 5805424646556658778755193) ^ 44346489725300648 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_8930966662271217619011919 : Nat.Prime 8930966662271217619011919 := by
  apply lucas_primality 8930966662271217619011919 (3 : ZMod 8930966662271217619011919)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (161055133, 1), (710934016571957, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (161055133, 1), (710934016571957, 1)] : List FactorBlock).map factorBlockValue).prod) = 8930966662271217619011919 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_13
      · exact prime_thirtySevenAI_161055133
      · exact prime_thirtySevenAI_710934016571957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 8930966662271217619011919) ^ 4465483331135608809505959 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 8930966662271217619011919) ^ 2976988887423739206337306 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 8930966662271217619011919) ^ 686997435559324432231686 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 8930966662271217619011919) ^ 55452853292612646 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 8930966662271217619011919) ^ 12562300374 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_408821258988826391569349339 : Nat.Prime 408821258988826391569349339 := by
  apply lucas_primality 408821258988826391569349339 (2 : ZMod 408821258988826391569349339)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (101, 1), (5591, 1), (21293335073769464527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (101, 1), (5591, 1), (21293335073769464527, 1)] : List FactorBlock).map factorBlockValue).prod) = 408821258988826391569349339 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_17
      · exact prime_thirtySevenAI_101
      · exact prime_thirtySevenAI_5591
      · exact prime_thirtySevenAI_21293335073769464527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 408821258988826391569349339) ^ 204410629494413195784674669 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 408821258988826391569349339) ^ 24048309352283905386432314 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 408821258988826391569349339) ^ 4047735237513132589795538 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 408821258988826391569349339) ^ 73121312643324341185718 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 408821258988826391569349339) ^ 19199494 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_437438747118044238979203793 : Nat.Prime 437438747118044238979203793 := by
  apply lucas_primality 437438747118044238979203793 (10 : ZMod 437438747118044238979203793)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 2), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 2), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 437438747118044238979203793 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_7
      · exact prime_thirtySevenAI_11
      · exact prime_thirtySevenAI_13
      · exact prime_thirtySevenAI_17
      · exact prime_thirtySevenAI_19
      · exact prime_thirtySevenAI_23
      · exact prime_thirtySevenAI_29
      · exact prime_thirtySevenAI_31
      · exact prime_thirtySevenAI_37
      · exact prime_thirtySevenAI_41
      · exact prime_thirtySevenAI_43
      · exact prime_thirtySevenAI_47
      · exact prime_thirtySevenAI_53
      · exact prime_thirtySevenAI_59
      · exact prime_thirtySevenAI_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 437438747118044238979203793) ^ 218719373559022119489601896 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (10 : ZMod 437438747118044238979203793) ^ 145812915706014746326401264 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (10 : ZMod 437438747118044238979203793) ^ 62491249588292034139886256 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (10 : ZMod 437438747118044238979203793) ^ 39767158828913112634473072 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (10 : ZMod 437438747118044238979203793) ^ 33649134393695710690707984 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (10 : ZMod 437438747118044238979203793) ^ 25731691006943778763482576 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (10 : ZMod 437438747118044238979203793) ^ 23023091953581275735747568 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (10 : ZMod 437438747118044238979203793) ^ 19019075961654097346921904 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (10 : ZMod 437438747118044238979203793) ^ 15084094728208422033765648 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (10 : ZMod 437438747118044238979203793) ^ 14110927326388523838038832 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (10 : ZMod 437438747118044238979203793) ^ 11822668841028222675113616 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (10 : ZMod 437438747118044238979203793) ^ 10669237734586444853151312 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (10 : ZMod 437438747118044238979203793) ^ 10172994119024284627423344 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (10 : ZMod 437438747118044238979203793) ^ 9307207385490302957004336 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (10 : ZMod 437438747118044238979203793) ^ 8253561266378193188286864 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (10 : ZMod 437438747118044238979203793) ^ 7414216052848207440325488 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (10 : ZMod 437438747118044238979203793) ^ 7171127001935151458675472 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_446366068487800243856330401 : Nat.Prime 446366068487800243856330401 := by
  apply lucas_primality 446366068487800243856330401 (101 : ZMod 446366068487800243856330401)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 3), (5, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 2), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 3), (5, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 2), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 446366068487800243856330401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_5
      · exact prime_thirtySevenAI_11
      · exact prime_thirtySevenAI_13
      · exact prime_thirtySevenAI_17
      · exact prime_thirtySevenAI_19
      · exact prime_thirtySevenAI_23
      · exact prime_thirtySevenAI_29
      · exact prime_thirtySevenAI_31
      · exact prime_thirtySevenAI_37
      · exact prime_thirtySevenAI_41
      · exact prime_thirtySevenAI_43
      · exact prime_thirtySevenAI_47
      · exact prime_thirtySevenAI_53
      · exact prime_thirtySevenAI_59
      · exact prime_thirtySevenAI_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (101 : ZMod 446366068487800243856330401) ^ 223183034243900121928165200 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (101 : ZMod 446366068487800243856330401) ^ 148788689495933414618776800 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (101 : ZMod 446366068487800243856330401) ^ 89273213697560048771266080 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (101 : ZMod 446366068487800243856330401) ^ 40578733498890931259666400 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (101 : ZMod 446366068487800243856330401) ^ 34335851422138480296640800 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (101 : ZMod 446366068487800243856330401) ^ 26256827558105896697431200 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (101 : ZMod 446366068487800243856330401) ^ 23492950973042118097701600 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (101 : ZMod 446366068487800243856330401) ^ 19407220369034793211144800 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (101 : ZMod 446366068487800243856330401) ^ 15391933396131042891597600 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (101 : ZMod 446366068487800243856330401) ^ 14398905435090330446978400 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (101 : ZMod 446366068487800243856330401) ^ 12063947796967574158279200 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (101 : ZMod 446366068487800243856330401) ^ 10886977280190249850154400 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (101 : ZMod 446366068487800243856330401) ^ 10380606243902331252472800 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (101 : ZMod 446366068487800243856330401) ^ 9497150393357451996943200 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (101 : ZMod 446366068487800243856330401) ^ 8422001292222646110496800 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (101 : ZMod 446366068487800243856330401) ^ 7565526584538987184005600 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (101 : ZMod 446366068487800243856330401) ^ 7317476532586889243546400 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_455665361581296082270003951 : Nat.Prime 455665361581296082270003951 := by
  apply lucas_primality 455665361581296082270003951 (3 : ZMod 455665361581296082270003951)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 2), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 2), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 455665361581296082270003951 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_5
      · exact prime_thirtySevenAI_7
      · exact prime_thirtySevenAI_11
      · exact prime_thirtySevenAI_13
      · exact prime_thirtySevenAI_17
      · exact prime_thirtySevenAI_19
      · exact prime_thirtySevenAI_23
      · exact prime_thirtySevenAI_29
      · exact prime_thirtySevenAI_31
      · exact prime_thirtySevenAI_37
      · exact prime_thirtySevenAI_41
      · exact prime_thirtySevenAI_43
      · exact prime_thirtySevenAI_47
      · exact prime_thirtySevenAI_53
      · exact prime_thirtySevenAI_59
      · exact prime_thirtySevenAI_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 455665361581296082270003951) ^ 227832680790648041135001975 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 455665361581296082270003951) ^ 151888453860432027423334650 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 455665361581296082270003951) ^ 91133072316259216454000790 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 455665361581296082270003951) ^ 65095051654470868895714850 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 455665361581296082270003951) ^ 41424123780117825660909450 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 455665361581296082270003951) ^ 35051181660099698636154150 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 455665361581296082270003951) ^ 26803844798899769545294350 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 455665361581296082270003951) ^ 23982387451647162224737050 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 455665361581296082270003951) ^ 19811537460056351403043650 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 455665361581296082270003951) ^ 15712598675217106285172550 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 455665361581296082270003951) ^ 14698882631654712331290450 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 455665361581296082270003951) ^ 12315280042737731953243350 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 455665361581296082270003951) ^ 11113789306860880055365950 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 455665361581296082270003951) ^ 10596868873983629820232650 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 455665361581296082270003951) ^ 9695007693219065580212850 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 455665361581296082270003951) ^ 8597459652477284571132150 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 455665361581296082270003951) ^ 7723141721716882750339050 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (3 : ZMod 455665361581296082270003951) ^ 7469923960349116102786950 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_460461839071625514714951361 : Nat.Prime 460461839071625514714951361 := by
  apply lucas_primality 460461839071625514714951361 (95 : ZMod 460461839071625514714951361)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (5, 1), (7, 2), (11, 1), (13, 1), (17, 1), (23, 1), (29, 1), (31, 1), (37, 2), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (5, 1), (7, 2), (11, 1), (13, 1), (17, 1), (23, 1), (29, 1), (31, 1), (37, 2), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 460461839071625514714951361 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_5
      · exact prime_thirtySevenAI_7
      · exact prime_thirtySevenAI_11
      · exact prime_thirtySevenAI_13
      · exact prime_thirtySevenAI_17
      · exact prime_thirtySevenAI_23
      · exact prime_thirtySevenAI_29
      · exact prime_thirtySevenAI_31
      · exact prime_thirtySevenAI_37
      · exact prime_thirtySevenAI_41
      · exact prime_thirtySevenAI_43
      · exact prime_thirtySevenAI_47
      · exact prime_thirtySevenAI_53
      · exact prime_thirtySevenAI_59
      · exact prime_thirtySevenAI_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (95 : ZMod 460461839071625514714951361) ^ 230230919535812757357475680 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (95 : ZMod 460461839071625514714951361) ^ 153487279690541838238317120 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (95 : ZMod 460461839071625514714951361) ^ 92092367814325102942990272 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (95 : ZMod 460461839071625514714951361) ^ 65780262724517930673564480 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (95 : ZMod 460461839071625514714951361) ^ 41860167188329592246813760 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (95 : ZMod 460461839071625514714951361) ^ 35420141467048116516534720 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (95 : ZMod 460461839071625514714951361) ^ 27085990533625030277350080 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (95 : ZMod 460461839071625514714951361) ^ 20020079959635891944128320 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (95 : ZMod 460461839071625514714951361) ^ 15877994450745707403963840 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (95 : ZMod 460461839071625514714951361) ^ 14853607711987919829514560 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (95 : ZMod 460461839071625514714951361) ^ 12444914569503392289593280 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (95 : ZMod 460461839071625514714951361) ^ 11230776562722573529632960 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (95 : ZMod 460461839071625514714951361) ^ 10708414862130825923603520 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (95 : ZMod 460461839071625514714951361) ^ 9797060405779266270530880 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (95 : ZMod 460461839071625514714951361) ^ 8687959227766519145565120 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (95 : ZMod 460461839071625514714951361) ^ 7804437950366534147711040 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (95 : ZMod 460461839071625514714951361) ^ 7548554738879106798605760 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_672982687873914213814159681 : Nat.Prime 672982687873914213814159681 := by
  apply lucas_primality 672982687873914213814159681 (13 : ZMod 672982687873914213814159681)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (5, 1), (7, 2), (11, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 2), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (5, 1), (7, 2), (11, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 2), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 672982687873914213814159681 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_5
      · exact prime_thirtySevenAI_7
      · exact prime_thirtySevenAI_11
      · exact prime_thirtySevenAI_17
      · exact prime_thirtySevenAI_19
      · exact prime_thirtySevenAI_23
      · exact prime_thirtySevenAI_29
      · exact prime_thirtySevenAI_31
      · exact prime_thirtySevenAI_37
      · exact prime_thirtySevenAI_41
      · exact prime_thirtySevenAI_43
      · exact prime_thirtySevenAI_47
      · exact prime_thirtySevenAI_53
      · exact prime_thirtySevenAI_59
      · exact prime_thirtySevenAI_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 672982687873914213814159681) ^ 336491343936957106907079840 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (13 : ZMod 672982687873914213814159681) ^ 224327562624638071271386560 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (13 : ZMod 672982687873914213814159681) ^ 134596537574782842762831936 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (13 : ZMod 672982687873914213814159681) ^ 96140383981987744830594240 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (13 : ZMod 672982687873914213814159681) ^ 61180244352174019437650880 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (13 : ZMod 672982687873914213814159681) ^ 39587216933759659636127040 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (13 : ZMod 672982687873914213814159681) ^ 35420141467048116516534720 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (13 : ZMod 672982687873914213814159681) ^ 29260116864083226687572160 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (13 : ZMod 672982687873914213814159681) ^ 23206299581859110821177920 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (13 : ZMod 672982687873914213814159681) ^ 21709118963674652058521280 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (13 : ZMod 672982687873914213814159681) ^ 18188721293889573346328640 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (13 : ZMod 672982687873914213814159681) ^ 16414211899363761312540480 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (13 : ZMod 672982687873914213814159681) ^ 15650760183114284042189760 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (13 : ZMod 672982687873914213814159681) ^ 14318780593062004549237440 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (13 : ZMod 672982687873914213814159681) ^ 12697786563658758751210560 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (13 : ZMod 672982687873914213814159681) ^ 11406486235151088369731520 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (13 : ZMod 672982687873914213814159681) ^ 11032503079900233013346880 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_694347217647689268220958401 : Nat.Prime 694347217647689268220958401 := by
  apply lucas_primality 694347217647689268220958401 (97 : ZMod 694347217647689268220958401)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (5, 2), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 2), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (5, 2), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 2), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 694347217647689268220958401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_5
      · exact prime_thirtySevenAI_7
      · exact prime_thirtySevenAI_11
      · exact prime_thirtySevenAI_13
      · exact prime_thirtySevenAI_17
      · exact prime_thirtySevenAI_19
      · exact prime_thirtySevenAI_23
      · exact prime_thirtySevenAI_29
      · exact prime_thirtySevenAI_31
      · exact prime_thirtySevenAI_37
      · exact prime_thirtySevenAI_41
      · exact prime_thirtySevenAI_43
      · exact prime_thirtySevenAI_47
      · exact prime_thirtySevenAI_53
      · exact prime_thirtySevenAI_59
      · exact prime_thirtySevenAI_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (97 : ZMod 694347217647689268220958401) ^ 347173608823844634110479200 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (97 : ZMod 694347217647689268220958401) ^ 231449072549229756073652800 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (97 : ZMod 694347217647689268220958401) ^ 138869443529537853644191680 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (97 : ZMod 694347217647689268220958401) ^ 99192459663955609745851200 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (97 : ZMod 694347217647689268220958401) ^ 63122474331608115292814400 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (97 : ZMod 694347217647689268220958401) ^ 53411324434437636016996800 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (97 : ZMod 694347217647689268220958401) ^ 40843953979275839307115200 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (97 : ZMod 694347217647689268220958401) ^ 36544590402509961485313600 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (97 : ZMod 694347217647689268220958401) ^ 30189009462943011661780800 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (97 : ZMod 694347217647689268220958401) ^ 23943007505092733386929600 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (97 : ZMod 694347217647689268220958401) ^ 22398297343473847361966400 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (97 : ZMod 694347217647689268220958401) ^ 18766141017505115357323200 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (97 : ZMod 694347217647689268220958401) ^ 16935297991407055322462400 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (97 : ZMod 694347217647689268220958401) ^ 16147609712736959726068800 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (97 : ZMod 694347217647689268220958401) ^ 14773345056333814217467200 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (97 : ZMod 694347217647689268220958401) ^ 13100890899013005060772800 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (97 : ZMod 694347217647689268220958401) ^ 11768596909282868952897600 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (97 : ZMod 694347217647689268220958401) ^ 11382741272912938823294400 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_754204736410421101688282401 : Nat.Prime 754204736410421101688282401 := by
  apply lucas_primality 754204736410421101688282401 (73 : ZMod 754204736410421101688282401)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (31, 1), (37, 2), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (31, 1), (37, 2), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 754204736410421101688282401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_5
      · exact prime_thirtySevenAI_7
      · exact prime_thirtySevenAI_11
      · exact prime_thirtySevenAI_13
      · exact prime_thirtySevenAI_17
      · exact prime_thirtySevenAI_19
      · exact prime_thirtySevenAI_23
      · exact prime_thirtySevenAI_31
      · exact prime_thirtySevenAI_37
      · exact prime_thirtySevenAI_41
      · exact prime_thirtySevenAI_43
      · exact prime_thirtySevenAI_47
      · exact prime_thirtySevenAI_53
      · exact prime_thirtySevenAI_59
      · exact prime_thirtySevenAI_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (73 : ZMod 754204736410421101688282401) ^ 377102368205210550844141200 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (73 : ZMod 754204736410421101688282401) ^ 251401578803473700562760800 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (73 : ZMod 754204736410421101688282401) ^ 150840947282084220337656480 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (73 : ZMod 754204736410421101688282401) ^ 107743533772917300241183200 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (73 : ZMod 754204736410421101688282401) ^ 68564066946401918335298400 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (73 : ZMod 754204736410421101688282401) ^ 58015748954647777052944800 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (73 : ZMod 754204736410421101688282401) ^ 44364984494730653040487200 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (73 : ZMod 754204736410421101688282401) ^ 39694986126864268509909600 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (73 : ZMod 754204736410421101688282401) ^ 32791510278713960942968800 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (73 : ZMod 754204736410421101688282401) ^ 24329185045497454893170400 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (73 : ZMod 754204736410421101688282401) ^ 20383911794876245991575200 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (73 : ZMod 754204736410421101688282401) ^ 18395237473424904919226400 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (73 : ZMod 754204736410421101688282401) ^ 17539645032800490736936800 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (73 : ZMod 754204736410421101688282401) ^ 16046909285328108546559200 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (73 : ZMod 754204736410421101688282401) ^ 14230278045479643428080800 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (73 : ZMod 754204736410421101688282401) ^ 12783131125600357655733600 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (73 : ZMod 754204736410421101688282401) ^ 12364012072301985273578400 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_767436398452709191191585601 : Nat.Prime 767436398452709191191585601 := by
  apply lucas_primality 767436398452709191191585601 (38 : ZMod 767436398452709191191585601)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (23, 1), (29, 1), (31, 1), (37, 2), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (23, 1), (29, 1), (31, 1), (37, 2), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 767436398452709191191585601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_5
      · exact prime_thirtySevenAI_7
      · exact prime_thirtySevenAI_11
      · exact prime_thirtySevenAI_13
      · exact prime_thirtySevenAI_17
      · exact prime_thirtySevenAI_23
      · exact prime_thirtySevenAI_29
      · exact prime_thirtySevenAI_31
      · exact prime_thirtySevenAI_37
      · exact prime_thirtySevenAI_41
      · exact prime_thirtySevenAI_43
      · exact prime_thirtySevenAI_47
      · exact prime_thirtySevenAI_53
      · exact prime_thirtySevenAI_59
      · exact prime_thirtySevenAI_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (38 : ZMod 767436398452709191191585601) ^ 383718199226354595595792800 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (38 : ZMod 767436398452709191191585601) ^ 255812132817569730397195200 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (38 : ZMod 767436398452709191191585601) ^ 153487279690541838238317120 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (38 : ZMod 767436398452709191191585601) ^ 109633771207529884455940800 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (38 : ZMod 767436398452709191191585601) ^ 69766945313882653744689600 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (38 : ZMod 767436398452709191191585601) ^ 59033569111746860860891200 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (38 : ZMod 767436398452709191191585601) ^ 45143317556041717128916800 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (38 : ZMod 767436398452709191191585601) ^ 33366799932726486573547200 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (38 : ZMod 767436398452709191191585601) ^ 26463324084576179006606400 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (38 : ZMod 767436398452709191191585601) ^ 24756012853313199715857600 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (38 : ZMod 767436398452709191191585601) ^ 20741524282505653815988800 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (38 : ZMod 767436398452709191191585601) ^ 18717960937870955882721600 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (38 : ZMod 767436398452709191191585601) ^ 17847358103551376539339200 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (38 : ZMod 767436398452709191191585601) ^ 16328434009632110450884800 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (38 : ZMod 767436398452709191191585601) ^ 14479932046277531909275200 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (38 : ZMod 767436398452709191191585601) ^ 13007396583944223579518400 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (38 : ZMod 767436398452709191191585601) ^ 12580924564798511331009600 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_857723033564792625449419201 : Nat.Prime 857723033564792625449419201 := by
  apply lucas_primality 857723033564792625449419201 (34 : ZMod 857723033564792625449419201)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 2), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 2), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 857723033564792625449419201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_5
      · exact prime_thirtySevenAI_7
      · exact prime_thirtySevenAI_11
      · exact prime_thirtySevenAI_13
      · exact prime_thirtySevenAI_19
      · exact prime_thirtySevenAI_23
      · exact prime_thirtySevenAI_29
      · exact prime_thirtySevenAI_31
      · exact prime_thirtySevenAI_37
      · exact prime_thirtySevenAI_41
      · exact prime_thirtySevenAI_43
      · exact prime_thirtySevenAI_47
      · exact prime_thirtySevenAI_53
      · exact prime_thirtySevenAI_59
      · exact prime_thirtySevenAI_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (34 : ZMod 857723033564792625449419201) ^ 428861516782396312724709600 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (34 : ZMod 857723033564792625449419201) ^ 285907677854930875149806400 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (34 : ZMod 857723033564792625449419201) ^ 171544606712958525089883840 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (34 : ZMod 857723033564792625449419201) ^ 122531861937827517921345600 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (34 : ZMod 857723033564792625449419201) ^ 77974821233162965949947200 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (34 : ZMod 857723033564792625449419201) ^ 65978694889599432726878400 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (34 : ZMod 857723033564792625449419201) ^ 45143317556041717128916800 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (34 : ZMod 857723033564792625449419201) ^ 37292305807164896758670400 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (34 : ZMod 857723033564792625449419201) ^ 29576656329820435360324800 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (34 : ZMod 857723033564792625449419201) ^ 27668484953702987917723200 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (34 : ZMod 857723033564792625449419201) ^ 23181703609859260147281600 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (34 : ZMod 857723033564792625449419201) ^ 20920073989385185986571200 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (34 : ZMod 857723033564792625449419201) ^ 19947047292204479661614400 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (34 : ZMod 857723033564792625449419201) ^ 18249426246059417562753600 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (34 : ZMod 857723033564792625449419201) ^ 16183453463486653310366400 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (34 : ZMod 857723033564792625449419201) ^ 14537678534996485177108800 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (34 : ZMod 857723033564792625449419201) ^ 14061033337127747958187200 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_1066923773458644485315131201 : Nat.Prime 1066923773458644485315131201 := by
  apply lucas_primality 1066923773458644485315131201 (89 : ZMod 1066923773458644485315131201)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 2), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 2), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 1066923773458644485315131201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_5
      · exact prime_thirtySevenAI_7
      · exact prime_thirtySevenAI_11
      · exact prime_thirtySevenAI_13
      · exact prime_thirtySevenAI_17
      · exact prime_thirtySevenAI_19
      · exact prime_thirtySevenAI_23
      · exact prime_thirtySevenAI_29
      · exact prime_thirtySevenAI_31
      · exact prime_thirtySevenAI_37
      · exact prime_thirtySevenAI_43
      · exact prime_thirtySevenAI_47
      · exact prime_thirtySevenAI_53
      · exact prime_thirtySevenAI_59
      · exact prime_thirtySevenAI_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (89 : ZMod 1066923773458644485315131201) ^ 533461886729322242657565600 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (89 : ZMod 1066923773458644485315131201) ^ 355641257819548161771710400 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (89 : ZMod 1066923773458644485315131201) ^ 213384754691728897063026240 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (89 : ZMod 1066923773458644485315131201) ^ 152417681922663497902161600 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (89 : ZMod 1066923773458644485315131201) ^ 96993070314422225937739200 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (89 : ZMod 1066923773458644485315131201) ^ 82071059496818806562702400 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (89 : ZMod 1066923773458644485315131201) ^ 62760221968155557959713600 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (89 : ZMod 1066923773458644485315131201) ^ 56153882813612867648164800 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (89 : ZMod 1066923773458644485315131201) ^ 46387990150375847187614400 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (89 : ZMod 1066923773458644485315131201) ^ 36790474946849809838452800 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (89 : ZMod 1066923773458644485315131201) ^ 34416895918020789848875200 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (89 : ZMod 1066923773458644485315131201) ^ 28835777661044445549057600 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (89 : ZMod 1066923773458644485315131201) ^ 24812180778108011286398400 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (89 : ZMod 1066923773458644485315131201) ^ 22700505818269031602449600 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (89 : ZMod 1066923773458644485315131201) ^ 20130637235068763873870400 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (89 : ZMod 1066923773458644485315131201) ^ 18083453787434652293476800 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (89 : ZMod 1066923773458644485315131201) ^ 17490553663256466972379200 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_1151154597679063786787378401 : Nat.Prime 1151154597679063786787378401 := by
  apply lucas_primality 1151154597679063786787378401 (73 : ZMod 1151154597679063786787378401)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (23, 1), (29, 1), (31, 1), (37, 2), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (23, 1), (29, 1), (31, 1), (37, 2), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 1151154597679063786787378401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_5
      · exact prime_thirtySevenAI_7
      · exact prime_thirtySevenAI_11
      · exact prime_thirtySevenAI_13
      · exact prime_thirtySevenAI_17
      · exact prime_thirtySevenAI_23
      · exact prime_thirtySevenAI_29
      · exact prime_thirtySevenAI_31
      · exact prime_thirtySevenAI_37
      · exact prime_thirtySevenAI_41
      · exact prime_thirtySevenAI_43
      · exact prime_thirtySevenAI_47
      · exact prime_thirtySevenAI_53
      · exact prime_thirtySevenAI_59
      · exact prime_thirtySevenAI_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (73 : ZMod 1151154597679063786787378401) ^ 575577298839531893393689200 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (73 : ZMod 1151154597679063786787378401) ^ 383718199226354595595792800 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (73 : ZMod 1151154597679063786787378401) ^ 230230919535812757357475680 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (73 : ZMod 1151154597679063786787378401) ^ 164450656811294826683911200 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (73 : ZMod 1151154597679063786787378401) ^ 104650417970823980617034400 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (73 : ZMod 1151154597679063786787378401) ^ 88550353667620291291336800 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (73 : ZMod 1151154597679063786787378401) ^ 67714976334062575693375200 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (73 : ZMod 1151154597679063786787378401) ^ 50050199899089729860320800 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (73 : ZMod 1151154597679063786787378401) ^ 39694986126864268509909600 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (73 : ZMod 1151154597679063786787378401) ^ 37134019279969799573786400 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (73 : ZMod 1151154597679063786787378401) ^ 31112286423758480723983200 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (73 : ZMod 1151154597679063786787378401) ^ 28076941406806433824082400 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (73 : ZMod 1151154597679063786787378401) ^ 26771037155327064809008800 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (73 : ZMod 1151154597679063786787378401) ^ 24492651014448165676327200 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (73 : ZMod 1151154597679063786787378401) ^ 21719898069416297863912800 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (73 : ZMod 1151154597679063786787378401) ^ 19511094875916335369277600 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (73 : ZMod 1151154597679063786787378401) ^ 18871386847197766996514400 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_1366996084743888246810011851 : Nat.Prime 1366996084743888246810011851 := by
  apply lucas_primality 1366996084743888246810011851 (2 : ZMod 1366996084743888246810011851)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 2), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 2), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 1366996084743888246810011851 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_5
      · exact prime_thirtySevenAI_7
      · exact prime_thirtySevenAI_11
      · exact prime_thirtySevenAI_13
      · exact prime_thirtySevenAI_17
      · exact prime_thirtySevenAI_19
      · exact prime_thirtySevenAI_23
      · exact prime_thirtySevenAI_29
      · exact prime_thirtySevenAI_31
      · exact prime_thirtySevenAI_37
      · exact prime_thirtySevenAI_41
      · exact prime_thirtySevenAI_43
      · exact prime_thirtySevenAI_47
      · exact prime_thirtySevenAI_53
      · exact prime_thirtySevenAI_59
      · exact prime_thirtySevenAI_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1366996084743888246810011851) ^ 683498042371944123405005925 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1366996084743888246810011851) ^ 455665361581296082270003950 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1366996084743888246810011851) ^ 273399216948777649362002370 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1366996084743888246810011851) ^ 195285154963412606687144550 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1366996084743888246810011851) ^ 124272371340353476982728350 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1366996084743888246810011851) ^ 105153544980299095908462450 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1366996084743888246810011851) ^ 80411534396699308635883050 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1366996084743888246810011851) ^ 71947162354941486674211150 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1366996084743888246810011851) ^ 59434612380169054209130950 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1366996084743888246810011851) ^ 47137796025651318855517650 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1366996084743888246810011851) ^ 44096647894964136993871350 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1366996084743888246810011851) ^ 36945840128213195859730050 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1366996084743888246810011851) ^ 33341367920582640166097850 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1366996084743888246810011851) ^ 31790606621950889460697950 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1366996084743888246810011851) ^ 29085023079657196740638550 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1366996084743888246810011851) ^ 25792378957431853713396450 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1366996084743888246810011851) ^ 23169425165150648251017150 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (2 : ZMod 1366996084743888246810011851) ^ 22409771881047348308360850 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_2083041652943067804662875201 : Nat.Prime 2083041652943067804662875201 := by
  apply lucas_primality 2083041652943067804662875201 (97 : ZMod 2083041652943067804662875201)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (5, 2), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 2), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (5, 2), (7, 1), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 2), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 2083041652943067804662875201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_5
      · exact prime_thirtySevenAI_7
      · exact prime_thirtySevenAI_11
      · exact prime_thirtySevenAI_13
      · exact prime_thirtySevenAI_17
      · exact prime_thirtySevenAI_19
      · exact prime_thirtySevenAI_23
      · exact prime_thirtySevenAI_29
      · exact prime_thirtySevenAI_31
      · exact prime_thirtySevenAI_37
      · exact prime_thirtySevenAI_41
      · exact prime_thirtySevenAI_43
      · exact prime_thirtySevenAI_47
      · exact prime_thirtySevenAI_53
      · exact prime_thirtySevenAI_59
      · exact prime_thirtySevenAI_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (97 : ZMod 2083041652943067804662875201) ^ 1041520826471533902331437600 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (97 : ZMod 2083041652943067804662875201) ^ 694347217647689268220958400 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (97 : ZMod 2083041652943067804662875201) ^ 416608330588613560932575040 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (97 : ZMod 2083041652943067804662875201) ^ 297577378991866829237553600 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (97 : ZMod 2083041652943067804662875201) ^ 189367422994824345878443200 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (97 : ZMod 2083041652943067804662875201) ^ 160233973303312908050990400 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (97 : ZMod 2083041652943067804662875201) ^ 122531861937827517921345600 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (97 : ZMod 2083041652943067804662875201) ^ 109633771207529884455940800 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (97 : ZMod 2083041652943067804662875201) ^ 90567028388829034985342400 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (97 : ZMod 2083041652943067804662875201) ^ 71829022515278200160788800 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (97 : ZMod 2083041652943067804662875201) ^ 67194892030421542085899200 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (97 : ZMod 2083041652943067804662875201) ^ 56298423052515346071969600 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (97 : ZMod 2083041652943067804662875201) ^ 50805893974221165967387200 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (97 : ZMod 2083041652943067804662875201) ^ 48442829138210879178206400 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (97 : ZMod 2083041652943067804662875201) ^ 44320035169001442652401600 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (97 : ZMod 2083041652943067804662875201) ^ 39302672697039015182318400 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (97 : ZMod 2083041652943067804662875201) ^ 35305790727848606858692800 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (97 : ZMod 2083041652943067804662875201) ^ 34148223818738816469883200 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_2916258314120294926528025281 : Nat.Prime 2916258314120294926528025281 := by
  apply lucas_primality 2916258314120294926528025281 (71 : ZMod 2916258314120294926528025281)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (5, 1), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 2), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (5, 1), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 2), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 2916258314120294926528025281 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_5
      · exact prime_thirtySevenAI_7
      · exact prime_thirtySevenAI_11
      · exact prime_thirtySevenAI_13
      · exact prime_thirtySevenAI_17
      · exact prime_thirtySevenAI_19
      · exact prime_thirtySevenAI_23
      · exact prime_thirtySevenAI_29
      · exact prime_thirtySevenAI_31
      · exact prime_thirtySevenAI_37
      · exact prime_thirtySevenAI_41
      · exact prime_thirtySevenAI_43
      · exact prime_thirtySevenAI_47
      · exact prime_thirtySevenAI_53
      · exact prime_thirtySevenAI_59
      · exact prime_thirtySevenAI_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (71 : ZMod 2916258314120294926528025281) ^ 1458129157060147463264012640 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (71 : ZMod 2916258314120294926528025281) ^ 972086104706764975509341760 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (71 : ZMod 2916258314120294926528025281) ^ 583251662824058985305605056 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (71 : ZMod 2916258314120294926528025281) ^ 416608330588613560932575040 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (71 : ZMod 2916258314120294926528025281) ^ 265114392192754084229820480 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (71 : ZMod 2916258314120294926528025281) ^ 224327562624638071271386560 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (71 : ZMod 2916258314120294926528025281) ^ 171544606712958525089883840 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (71 : ZMod 2916258314120294926528025281) ^ 153487279690541838238317120 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (71 : ZMod 2916258314120294926528025281) ^ 126793839744360648979479360 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (71 : ZMod 2916258314120294926528025281) ^ 100560631521389480225104320 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (71 : ZMod 2916258314120294926528025281) ^ 94072848842590158920258880 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (71 : ZMod 2916258314120294926528025281) ^ 78817792273521484500757440 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (71 : ZMod 2916258314120294926528025281) ^ 71128251563909632354342080 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (71 : ZMod 2916258314120294926528025281) ^ 67819960793495230849488960 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (71 : ZMod 2916258314120294926528025281) ^ 62048049236602019713362240 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (71 : ZMod 2916258314120294926528025281) ^ 55023741775854621255245760 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (71 : ZMod 2916258314120294926528025281) ^ 49428107018988049602169920 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (71 : ZMod 2916258314120294926528025281) ^ 47807513346234343057836480 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_3645322892650368658160031601 : Nat.Prime 3645322892650368658160031601 := by
  apply lucas_primality 3645322892650368658160031601 (107 : ZMod 3645322892650368658160031601)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 2), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 2), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 3645322892650368658160031601 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_5
      · exact prime_thirtySevenAI_7
      · exact prime_thirtySevenAI_11
      · exact prime_thirtySevenAI_13
      · exact prime_thirtySevenAI_17
      · exact prime_thirtySevenAI_19
      · exact prime_thirtySevenAI_23
      · exact prime_thirtySevenAI_29
      · exact prime_thirtySevenAI_31
      · exact prime_thirtySevenAI_37
      · exact prime_thirtySevenAI_41
      · exact prime_thirtySevenAI_43
      · exact prime_thirtySevenAI_47
      · exact prime_thirtySevenAI_53
      · exact prime_thirtySevenAI_59
      · exact prime_thirtySevenAI_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (107 : ZMod 3645322892650368658160031601) ^ 1822661446325184329080015800 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (107 : ZMod 3645322892650368658160031601) ^ 1215107630883456219386677200 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (107 : ZMod 3645322892650368658160031601) ^ 729064578530073731632006320 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (107 : ZMod 3645322892650368658160031601) ^ 520760413235766951165718800 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (107 : ZMod 3645322892650368658160031601) ^ 331392990240942605287275600 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (107 : ZMod 3645322892650368658160031601) ^ 280409453280797589089233200 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (107 : ZMod 3645322892650368658160031601) ^ 214430758391198156362354800 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (107 : ZMod 3645322892650368658160031601) ^ 191859099613177297797896400 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (107 : ZMod 3645322892650368658160031601) ^ 158492299680450811224349200 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (107 : ZMod 3645322892650368658160031601) ^ 125700789401736850281380400 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (107 : ZMod 3645322892650368658160031601) ^ 117591061053237698650323600 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (107 : ZMod 3645322892650368658160031601) ^ 98522240341901855625946800 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (107 : ZMod 3645322892650368658160031601) ^ 88910314454887040442927600 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (107 : ZMod 3645322892650368658160031601) ^ 84774950991869038561861200 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (107 : ZMod 3645322892650368658160031601) ^ 77560061545752524641702800 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (107 : ZMod 3645322892650368658160031601) ^ 68779677219818276569057200 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (107 : ZMod 3645322892650368658160031601) ^ 61785133773735062002712400 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (107 : ZMod 3645322892650368658160031601) ^ 59759391682792928822295600 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem prime_thirtySevenAI_4860430523533824877546708801 : Nat.Prime 4860430523533824877546708801 := by
  apply lucas_primality 4860430523533824877546708801 (107 : ZMod 4860430523533824877546708801)
  · rw [← thirtySevenAIFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 2), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 2), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 4860430523533824877546708801 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_thirtySevenAI_2
      · exact prime_thirtySevenAI_3
      · exact prime_thirtySevenAI_5
      · exact prime_thirtySevenAI_7
      · exact prime_thirtySevenAI_11
      · exact prime_thirtySevenAI_13
      · exact prime_thirtySevenAI_17
      · exact prime_thirtySevenAI_19
      · exact prime_thirtySevenAI_23
      · exact prime_thirtySevenAI_29
      · exact prime_thirtySevenAI_31
      · exact prime_thirtySevenAI_37
      · exact prime_thirtySevenAI_41
      · exact prime_thirtySevenAI_43
      · exact prime_thirtySevenAI_47
      · exact prime_thirtySevenAI_53
      · exact prime_thirtySevenAI_59
      · exact prime_thirtySevenAI_61
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (107 : ZMod 4860430523533824877546708801) ^ 2430215261766912438773354400 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (107 : ZMod 4860430523533824877546708801) ^ 1620143507844608292515569600 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (107 : ZMod 4860430523533824877546708801) ^ 972086104706764975509341760 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (107 : ZMod 4860430523533824877546708801) ^ 694347217647689268220958400 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (107 : ZMod 4860430523533824877546708801) ^ 441857320321256807049700800 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (107 : ZMod 4860430523533824877546708801) ^ 373879271041063452118977600 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (107 : ZMod 4860430523533824877546708801) ^ 285907677854930875149806400 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (107 : ZMod 4860430523533824877546708801) ^ 255812132817569730397195200 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (107 : ZMod 4860430523533824877546708801) ^ 211323066240601081632465600 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (107 : ZMod 4860430523533824877546708801) ^ 167601052535649133708507200 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (107 : ZMod 4860430523533824877546708801) ^ 156788081404316931533764800 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (107 : ZMod 4860430523533824877546708801) ^ 131362987122535807501262400 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (107 : ZMod 4860430523533824877546708801) ^ 118547085939849387257236800 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (107 : ZMod 4860430523533824877546708801) ^ 113033267989158718082481600 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (107 : ZMod 4860430523533824877546708801) ^ 103413415394336699522270400 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (107 : ZMod 4860430523533824877546708801) ^ 91706236293091035425409600 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (107 : ZMod 4860430523533824877546708801) ^ 82380178364980082670283200 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide
    · change (107 : ZMod 4860430523533824877546708801) ^ 79679188910390571763060800 ≠ 1
      rw [← thirtySevenAIFastPow_eq_pow]
      decide

private theorem phi_thirtySevenAI_43743874711804423897920379200 : Nat.totient 43743874711804423897920379200 = 5756140632996343657267200000 := by
  rw [← show ((([(2, 6), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 2), (41, 1), (43, 1), (47, 1), (53, 1), (59, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379200 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_2, prime_thirtySevenAI_3, prime_thirtySevenAI_5, prime_thirtySevenAI_7, prime_thirtySevenAI_11, prime_thirtySevenAI_13, prime_thirtySevenAI_17, prime_thirtySevenAI_19, prime_thirtySevenAI_23, prime_thirtySevenAI_29, prime_thirtySevenAI_31, prime_thirtySevenAI_37, prime_thirtySevenAI_41, prime_thirtySevenAI_43, prime_thirtySevenAI_47, prime_thirtySevenAI_53, prime_thirtySevenAI_59, prime_thirtySevenAI_61]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379201 : Nat.totient 43743874711804423897920379201 = 43229203725714995753745914208 := by
  rw [← show ((([(89, 1), (1867, 1), (263258816414029741265627, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379201 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_89, prime_thirtySevenAI_1867, prime_thirtySevenAI_263258816414029741265627]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379202 : Nat.totient 43743874711804423897920379202 = 21868894092043035350664793492 := by
  rw [← show ((([(2, 1), (7187, 1), (3043263859176598295388923, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379202 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_2, prime_thirtySevenAI_7187, prime_thirtySevenAI_3043263859176598295388923]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379203 : Nat.totient 43743874711804423897920379203 = 28969453451297907922314813600 := by
  rw [← show ((([(3, 1), (151, 1), (126968497427, 1), (760541762683613, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379203 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_3, prime_thirtySevenAI_151, prime_thirtySevenAI_126968497427, prime_thirtySevenAI_760541762683613]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379204 : Nat.totient 43743874711804423897920379204 = 21871920985653535911353292480 := by
  rw [← show ((([(2, 2), (1345471, 1), (191393383, 1), (42467431724857, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379204 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_2, prime_thirtySevenAI_1345471, prime_thirtySevenAI_191393383, prime_thirtySevenAI_42467431724857]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379205 : Nat.totient 43743874711804423897920379205 = 34983249073026698614939619328 := by
  rw [← show ((([(5, 1), (2953, 1), (15306898513, 1), (193551523862569, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379205 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_5, prime_thirtySevenAI_2953, prime_thirtySevenAI_15306898513, prime_thirtySevenAI_193551523862569]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379206 : Nat.totient 43743874711804423897920379206 = 14581158808975347112580565600 := by
  rw [← show ((([(2, 1), (3, 1), (190901, 1), (258623, 1), (147669447533742787, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379206 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_2, prime_thirtySevenAI_3, prime_thirtySevenAI_190901, prime_thirtySevenAI_258623, prime_thirtySevenAI_147669447533742787]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379207 : Nat.totient 43743874711804423897920379207 = 37494749732863172842791429912 := by
  rw [← show ((([(7, 1), (1864293007, 1), (3352007938325760943, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379207 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_7, prime_thirtySevenAI_1864293007, prime_thirtySevenAI_3352007938325760943]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379208 : Nat.totient 43743874711804423897920379208 = 21834676812627579433924726272 := by
  rw [← show ((([(2, 3), (587, 1), (8288812769, 1), (1123820192311867, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379208 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_2, prime_thirtySevenAI_587, prime_thirtySevenAI_8288812769, prime_thirtySevenAI_1123820192311867]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379209 : Nat.totient 43743874711804423897920379209 = 29162583141202949265280252800 := by
  rw [← show ((([(3, 2), (4860430523533824877546708801, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379209 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_3, prime_thirtySevenAI_4860430523533824877546708801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379210 : Nat.totient 43743874711804423897920379210 = 17497549884721210512627562000 := by
  rw [← show ((([(2, 1), (5, 1), (47321092540151, 1), (92440542607271, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379210 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_2, prime_thirtySevenAI_5, prime_thirtySevenAI_47321092540151, prime_thirtySevenAI_92440542607271]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379211 : Nat.totient 43743874711804423897920379211 = 39761386217475961632740326400 := by
  rw [← show ((([(11, 2), (6971, 1), (585113, 1), (88633326395586017, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379211 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_11, prime_thirtySevenAI_6971, prime_thirtySevenAI_585113, prime_thirtySevenAI_88633326395586017]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379212 : Nat.totient 43743874711804423897920379212 = 14581291570601474632640126400 := by
  rw [← show ((([(2, 2), (3, 1), (3645322892650368658160031601, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379212 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_2, prime_thirtySevenAI_3, prime_thirtySevenAI_3645322892650368658160031601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379213 : Nat.totient 43743874711804423897920379213 = 40339332311457352174147151616 := by
  rw [← show ((([(13, 1), (1019, 1), (18780269, 1), (54928733, 1), (3201093227, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379213 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_13, prime_thirtySevenAI_1019, prime_thirtySevenAI_18780269, prime_thirtySevenAI_54928733, prime_thirtySevenAI_3201093227]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379214 : Nat.totient 43743874711804423897920379214 = 18625975607823714863551861728 := by
  rw [← show ((([(2, 1), (7, 1), (167, 1), (2039, 1), (93866963, 1), (97755848490779, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379214 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_2, prime_thirtySevenAI_7, prime_thirtySevenAI_167, prime_thirtySevenAI_2039, prime_thirtySevenAI_93866963, prime_thirtySevenAI_97755848490779]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379215 : Nat.totient 43743874711804423897920379215 = 23330066512962359412224202240 := by
  rw [← show ((([(3, 1), (5, 1), (2916258314120294926528025281, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379215 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_3, prime_thirtySevenAI_5, prime_thirtySevenAI_2916258314120294926528025281]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379216 : Nat.totient 43743874711804423897920379216 = 21871937355895375353726696032 := by
  rw [← show ((([(2, 4), (3211311593459, 1), (851363092593239, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379216 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_2, prime_thirtySevenAI_3211311593459, prime_thirtySevenAI_851363092593239]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379217 : Nat.totient 43743874711804423897920379217 = 41010508310122393582219051008 := by
  rw [← show ((([(17, 1), (257, 1), (14191028167, 1), (705539515057079, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379217 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_17, prime_thirtySevenAI_257, prime_thirtySevenAI_14191028167, prime_thirtySevenAI_705539515057079]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379218 : Nat.totient 43743874711804423897920379218 = 14581291570552148074166824224 := by
  rw [← show ((([(2, 1), (3, 2), (295617946229, 1), (8220797460937469, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379218 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_2, prime_thirtySevenAI_3, prime_thirtySevenAI_295617946229, prime_thirtySevenAI_8220797460937469]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379219 : Nat.totient 43743874711804423897920379219 = 41378017178910024291134723328 := by
  rw [← show ((([(19, 1), (653, 1), (702503, 1), (1585993, 1), (3164470252123, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379219 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_19, prime_thirtySevenAI_653, prime_thirtySevenAI_702503, prime_thirtySevenAI_1585993, prime_thirtySevenAI_3164470252123]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379220 : Nat.totient 43743874711804423897920379220 = 17497433442885376942474266624 := by
  rw [← show ((([(2, 2), (5, 1), (161969, 1), (2080157, 1), (6491711902208917, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379220 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_2, prime_thirtySevenAI_5, prime_thirtySevenAI_161969, prime_thirtySevenAI_2080157, prime_thirtySevenAI_6491711902208917]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379221 : Nat.totient 43743874711804423897920379221 = 24996499835316813655954502400 := by
  rw [← show ((([(3, 1), (7, 1), (2083041652943067804662875201, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379221 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_3, prime_thirtySevenAI_7, prime_thirtySevenAI_2083041652943067804662875201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379222 : Nat.totient 43743874711804423897920379222 = 19882646743152998824983897120 := by
  rw [← show ((([(2, 1), (11, 1), (21319, 1), (10581611773, 1), (8814058220323, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379222 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_2, prime_thirtySevenAI_11, prime_thirtySevenAI_21319, prime_thirtySevenAI_10581611773, prime_thirtySevenAI_8814058220323]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379223 : Nat.totient 43743874711804423897920379223 = 41837397030009102205816388256 := by
  rw [← show ((([(23, 1), (9157, 1), (60742859, 1), (3419329630390727, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379223 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_23, prime_thirtySevenAI_9157, prime_thirtySevenAI_60742859, prime_thirtySevenAI_3419329630390727]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379224 : Nat.totient 43743874711804423897920379224 = 14581063097997668268865503360 := by
  rw [← show ((([(2, 3), (3, 1), (63823, 1), (1805730461, 1), (15815242981667, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379224 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_2, prime_thirtySevenAI_3, prime_thirtySevenAI_63823, prime_thirtySevenAI_1805730461, prime_thirtySevenAI_15815242981667]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379225 : Nat.totient 43743874711804423897920379225 = 34995099769424611592480870400 := by
  rw [← show ((([(5, 2), (1852526162209, 1), (944523766609441, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379225 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_5, prime_thirtySevenAI_1852526162209, prime_thirtySevenAI_944523766609441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379226 : Nat.totient 43743874711804423897920379226 = 19793961045509444370147916800 := by
  rw [← show ((([(2, 1), (13, 1), (83, 1), (131, 1), (2689163, 1), (4773739, 1), (12053653841, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379226 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_2, prime_thirtySevenAI_13, prime_thirtySevenAI_83, prime_thirtySevenAI_131, prime_thirtySevenAI_2689163, prime_thirtySevenAI_4773739, prime_thirtySevenAI_12053653841]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379227 : Nat.totient 43743874711804423897920379227 = 29162583141148897067051827200 := by
  rw [← show ((([(3, 3), (539623282241, 1), (3002360278296961, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379227 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_3, prime_thirtySevenAI_539623282241, prime_thirtySevenAI_3002360278296961]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379228 : Nat.totient 43743874711804423897920379228 = 18747331155566431701952932864 := by
  rw [← show ((([(2, 2), (7, 1), (446933, 1), (10566653, 1), (330810548380849, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379228 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_2, prime_thirtySevenAI_7, prime_thirtySevenAI_446933, prime_thirtySevenAI_10566653, prime_thirtySevenAI_330810548380849]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379229 : Nat.totient 43743874711804423897920379229 = 42216113724912708992603424960 := by
  rw [← show ((([(29, 1), (2237, 1), (89611, 1), (7524747705762493343, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379229 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_29, prime_thirtySevenAI_2237, prime_thirtySevenAI_89611, prime_thirtySevenAI_7524747705762493343]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379230 : Nat.totient 43743874711804423897920379230 = 11664841273356997062998357760 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (60761, 1), (13383906967, 1), (1793032544543, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379230 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_2, prime_thirtySevenAI_3, prime_thirtySevenAI_5, prime_thirtySevenAI_60761, prime_thirtySevenAI_13383906967, prime_thirtySevenAI_1793032544543]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379231 : Nat.totient 43743874711804423897920379231 = 42321441828621996488262080160 := by
  rw [← show ((([(31, 1), (3733, 1), (378005018119167528476797, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379231 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_31, prime_thirtySevenAI_3733, prime_thirtySevenAI_378005018119167528476797]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379232 : Nat.totient 43743874711804423897920379232 = 21871937355902211948960189600 := by
  rw [← show ((([(2, 5), (1366996084743888246810011851, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379232 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_2, prime_thirtySevenAI_1366996084743888246810011851]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379233 : Nat.totient 43743874711804423897920379233 = 26488405368795043068345816000 := by
  rw [← show ((([(3, 1), (11, 1), (1151, 1), (58330037, 1), (19744026879106723, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379233 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_3, prime_thirtySevenAI_11, prime_thirtySevenAI_1151, prime_thirtySevenAI_58330037, prime_thirtySevenAI_19744026879106723]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379234 : Nat.totient 43743874711804423897920379234 = 20585352805532303991620256064 := by
  rw [← show ((([(2, 1), (17, 1), (906663499619, 1), (1419032034363179, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379234 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_2, prime_thirtySevenAI_17, prime_thirtySevenAI_906663499619, prime_thirtySevenAI_1419032034363179]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379235 : Nat.totient 43743874711804423897920379235 = 29827447706312814395755008000 := by
  rw [← show ((([(5, 1), (7, 1), (179, 1), (38351, 1), (1141205281, 1), (159534901429, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379235 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_5, prime_thirtySevenAI_7, prime_thirtySevenAI_179, prime_thirtySevenAI_38351, prime_thirtySevenAI_1141205281, prime_thirtySevenAI_159534901429]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379236 : Nat.totient 43743874711804423897920379236 = 14581251378738325803179683584 := by
  rw [← show ((([(2, 2), (3, 2), (362863, 1), (1859406863, 1), (1800933314129, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379236 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_2, prime_thirtySevenAI_3, prime_thirtySevenAI_362863, prime_thirtySevenAI_1859406863, prime_thirtySevenAI_1800933314129]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379237 : Nat.totient 43743874711804423897920379237 = 42139973802718643022035142912 := by
  rw [← show ((([(37, 1), (103, 1), (5009, 1), (2291539082278737626663, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379237 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_37, prime_thirtySevenAI_103, prime_thirtySevenAI_5009, prime_thirtySevenAI_2291539082278737626663]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379238 : Nat.totient 43743874711804423897920379238 = 20720782758223148162172811200 := by
  rw [← show ((([(2, 1), (19, 1), (1151154597679063786787378401, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379238 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_2, prime_thirtySevenAI_19, prime_thirtySevenAI_1151154597679063786787378401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379239 : Nat.totient 43743874711804423897920379239 = 26608937914814980123607040000 := by
  rw [← show ((([(3, 1), (13, 1), (97, 1), (863, 1), (13441, 1), (996870010236610751, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379239 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_3, prime_thirtySevenAI_13, prime_thirtySevenAI_97, prime_thirtySevenAI_863, prime_thirtySevenAI_13441, prime_thirtySevenAI_996870010236610751]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379240 : Nat.totient 43743874711804423897920379240 = 17497549884720706077646080000 := by
  rw [← show ((([(2, 3), (5, 1), (29934035031001, 1), (36533560098481, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379240 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_2, prime_thirtySevenAI_5, prime_thirtySevenAI_29934035031001, prime_thirtySevenAI_36533560098481]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379241 : Nat.totient 43743874711804423897920379241 = 42676950938345779412605248000 := by
  rw [← show ((([(41, 1), (1066923773458644485315131201, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379241 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_41, prime_thirtySevenAI_1066923773458644485315131201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379242 : Nat.totient 43743874711804423897920379242 = 12375575703617679665402019840 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (199, 1), (241, 1), (1759, 1), (13009, 1), (44533, 1), (21311113093, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379242 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_2, prime_thirtySevenAI_3, prime_thirtySevenAI_7, prime_thirtySevenAI_199, prime_thirtySevenAI_241, prime_thirtySevenAI_1759, prime_thirtySevenAI_13009, prime_thirtySevenAI_44533, prime_thirtySevenAI_21311113093]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379243 : Nat.totient 43743874711804423897920379243 = 42702531081950446760200379904 := by
  rw [← show ((([(43, 1), (1777, 1), (572481379798777975656913, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379243 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_43, prime_thirtySevenAI_1777, prime_thirtySevenAI_572481379798777975656913]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379244 : Nat.totient 43743874711804423897920379244 = 19826278032858698806235847440 := by
  rw [← show ((([(2, 2), (11, 1), (347, 1), (2865069079892875550034083, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379244 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_2, prime_thirtySevenAI_11, prime_thirtySevenAI_347, prime_thirtySevenAI_2865069079892875550034083]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379245 : Nat.totient 43743874711804423897920379245 = 23313740364000723228776432640 := by
  rw [← show ((([(3, 2), (5, 1), (1429, 1), (95586933049, 1), (7116623315941, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379245 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_3, prime_thirtySevenAI_5, prime_thirtySevenAI_1429, prime_thirtySevenAI_95586933049, prime_thirtySevenAI_7116623315941]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379246 : Nat.totient 43743874711804423897920379246 = 20866001320919896634853043200 := by
  rw [← show ((([(2, 1), (23, 1), (383, 1), (58711, 1), (7319017, 1), (5778144651281, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379246 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_2, prime_thirtySevenAI_23, prime_thirtySevenAI_383, prime_thirtySevenAI_58711, prime_thirtySevenAI_7319017, prime_thirtySevenAI_5778144651281]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379247 : Nat.totient 43743874711804423897920379247 = 42770711478879114114425932800 := by
  rw [← show ((([(47, 1), (1009, 1), (6459151, 1), (9303353, 1), (15350173463, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379247 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_47, prime_thirtySevenAI_1009, prime_thirtySevenAI_6459151, prime_thirtySevenAI_9303353, prime_thirtySevenAI_15350173463]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379248 : Nat.totient 43743874711804423897920379248 = 14557659007277971432263066112 := by
  rw [← show ((([(2, 4), (3, 1), (617, 1), (1477035207718950023565653, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379248 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_2, prime_thirtySevenAI_3, prime_thirtySevenAI_617, prime_thirtySevenAI_1477035207718950023565653]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379249 : Nat.totient 43743874711804423897920379249 = 37485077282019190799879480640 := by
  rw [← show ((([(7, 3), (3877, 1), (26812879, 1), (1226828565754021, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379249 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_7, prime_thirtySevenAI_3877, prime_thirtySevenAI_26812879, prime_thirtySevenAI_1226828565754021]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379250 : Nat.totient 43743874711804423897920379250 = 17497548318940309277442159600 := by
  rw [← show ((([(2, 1), (5, 3), (11174963, 1), (15657814602806084959, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379250 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_2, prime_thirtySevenAI_5, prime_thirtySevenAI_11174963, prime_thirtySevenAI_15657814602806084959]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379251 : Nat.totient 43743874711804423897920379251 = 27447137074073364014381414400 := by
  rw [← show ((([(3, 1), (17, 1), (857723033564792625449419201, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379251 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_3, prime_thirtySevenAI_17, prime_thirtySevenAI_857723033564792625449419201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379252 : Nat.totient 43743874711804423897920379252 = 20186382830589025371246678912 := by
  rw [← show ((([(2, 2), (13, 1), (6659, 1), (319399, 1), (7490023, 1), (52806597707, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379252 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_2, prime_thirtySevenAI_13, prime_thirtySevenAI_6659, prime_thirtySevenAI_319399, prime_thirtySevenAI_7490023, prime_thirtySevenAI_52806597707]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379253 : Nat.totient 43743874711804423897920379253 = 42309198175943650111615553280 := by
  rw [← show ((([(53, 1), (71, 1), (8753, 1), (1328085705243625636327, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379253 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_53, prime_thirtySevenAI_71, prime_thirtySevenAI_8753, prime_thirtySevenAI_1328085705243625636327]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379254 : Nat.totient 43743874711804423897920379254 = 14581291533497696139297169104 := by
  rw [← show ((([(2, 1), (3, 4), (392986703, 1), (687107008742993989, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379254 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_2, prime_thirtySevenAI_3, prime_thirtySevenAI_392986703, prime_thirtySevenAI_687107008742993989]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379255 : Nat.totient 43743874711804423897920379255 = 31581510077268223756428244480 := by
  rw [← show ((([(5, 1), (11, 1), (137, 1), (5805424646556658778755193, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379255 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_5, prime_thirtySevenAI_11, prime_thirtySevenAI_137, prime_thirtySevenAI_5805424646556658778755193]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379256 : Nat.totient 43743874711804423897920379256 = 18746656943853424678826508288 := by
  rw [← show ((([(2, 3), (7, 1), (26113, 1), (29913859757731797447577, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379256 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_2, prime_thirtySevenAI_7, prime_thirtySevenAI_26113, prime_thirtySevenAI_29913859757731797447577]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379257 : Nat.totient 43743874711804423897920379257 = 27627710344297530882897081600 := by
  rw [← show ((([(3, 1), (19, 1), (767436398452709191191585601, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379257 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_3, prime_thirtySevenAI_19, prime_thirtySevenAI_767436398452709191191585601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379258 : Nat.totient 43743874711804423897920379258 = 21117732619491790847271907200 := by
  rw [← show ((([(2, 1), (29, 1), (754204736410421101688282401, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379258 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_2, prime_thirtySevenAI_29, prime_thirtySevenAI_754204736410421101688282401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379259 : Nat.totient 43743874711804423897920379259 = 42988369823811139473927820800 := by
  rw [← show ((([(59, 1), (3067, 1), (695441, 1), (97482823, 1), (3565850021, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379259 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_59, prime_thirtySevenAI_3067, prime_thirtySevenAI_695441, prime_thirtySevenAI_97482823, prime_thirtySevenAI_3565850021]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379260 : Nat.totient 43743874711804423897920379260 = 11639838800165296261918460160 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (463, 1), (323364945581, 1), (4869586326107, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379260 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_2, prime_thirtySevenAI_3, prime_thirtySevenAI_5, prime_thirtySevenAI_463, prime_thirtySevenAI_323364945581, prime_thirtySevenAI_4869586326107]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379261 : Nat.totient 43743874711804423897920379261 = 43026762011387331700720530240 := by
  rw [← show ((([(61, 1), (192457070789, 1), (3726091731800909, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379261 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_61, prime_thirtySevenAI_192457070789, prime_thirtySevenAI_3726091731800909]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379262 : Nat.totient 43743874711804423897920379262 = 20898461989714649228487888120 := by
  rw [← show ((([(2, 1), (31, 1), (79, 1), (8930966662271217619011919, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379262 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_2, prime_thirtySevenAI_31, prime_thirtySevenAI_79, prime_thirtySevenAI_8930966662271217619011919]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379263 : Nat.totient 43743874711804423897920379263 = 24996499835316813655954502400 := by
  rw [← show ((([(3, 2), (7, 1), (694347217647689268220958401, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379263 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_3, prime_thirtySevenAI_7, prime_thirtySevenAI_694347217647689268220958401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379264 : Nat.totient 43743874711804423897920379264 = 21871599967751233068570572800 := by
  rw [← show ((([(2, 7), (64901, 1), (57028157, 1), (92335042689059, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379264 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_2, prime_thirtySevenAI_64901, prime_thirtySevenAI_57028157, prime_thirtySevenAI_92335042689059]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379265 : Nat.totient 43743874711804423897920379265 = 32303169017947882263079664640 := by
  rw [← show ((([(5, 1), (13, 1), (672982687873914213814159681, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379265 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_5, prime_thirtySevenAI_13, prime_thirtySevenAI_672982687873914213814159681]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379266 : Nat.totient 43743874711804423897920379266 = 12813622450289073996817006080 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (67, 1), (73, 1), (197, 1), (687874839503081087063, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379266 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_2, prime_thirtySevenAI_3, prime_thirtySevenAI_11, prime_thirtySevenAI_67, prime_thirtySevenAI_73, prime_thirtySevenAI_197, prime_thirtySevenAI_687874839503081087063]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379267 : Nat.totient 43743874711804423897920379267 = 42844920887938507097760000000 := by
  rw [← show ((([(101, 1), (109, 1), (701, 1), (5903, 1), (1875901, 1), (511880589221, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379267 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_101, prime_thirtySevenAI_109, prime_thirtySevenAI_701, prime_thirtySevenAI_5903, prime_thirtySevenAI_1875901, prime_thirtySevenAI_511880589221]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379268 : Nat.totient 43743874711804423897920379268 = 20575146582381854274562437120 := by
  rw [← show ((([(2, 2), (17, 1), (2017, 1), (69243563, 1), (4605990429531731, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379268 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_2, prime_thirtySevenAI_17, prime_thirtySevenAI_2017, prime_thirtySevenAI_69243563, prime_thirtySevenAI_4605990429531731]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379269 : Nat.totient 43743874711804423897920379269 = 27894636606799765045205441600 := by
  rw [← show ((([(3, 1), (23, 1), (3428141, 1), (184930899493866572261, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379269 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_3, prime_thirtySevenAI_23, prime_thirtySevenAI_3428141, prime_thirtySevenAI_184930899493866572261]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379270 : Nat.totient 43743874711804423897920379270 = 14931745314882895791190720512 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (227, 1), (176713, 1), (333754049, 1), (46676502739, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379270 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_2, prime_thirtySevenAI_5, prime_thirtySevenAI_7, prime_thirtySevenAI_227, prime_thirtySevenAI_176713, prime_thirtySevenAI_333754049, prime_thirtySevenAI_46676502739]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379271 : Nat.totient 43743874711804423897920379271 = 43737298719361265893218300000 := by
  rw [← show ((([(6701, 1), (910621, 1), (7168692794733793951, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379271 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_6701, prime_thirtySevenAI_910621, prime_thirtySevenAI_7168692794733793951]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379272 : Nat.totient 43743874711804423897920379272 = 14475987208508160380088814848 := by
  rw [← show ((([(2, 3), (3, 2), (139, 1), (35923, 1), (121673879090654553433, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379272 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_2, prime_thirtySevenAI_3, prime_thirtySevenAI_139, prime_thirtySevenAI_35923, prime_thirtySevenAI_121673879090654553433]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379273 : Nat.totient 43743874711804423897920379273 = 43335053452815597506351029828 := by
  rw [← show ((([(107, 1), (408821258988826391569349339, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379273 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_107, prime_thirtySevenAI_408821258988826391569349339]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379274 : Nat.totient 43743874711804423897920379274 = 21280803896444840833759419600 := by
  rw [← show ((([(2, 1), (37, 1), (1222615931, 1), (483498887150858771, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379274 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_2, prime_thirtySevenAI_37, prime_thirtySevenAI_1222615931, prime_thirtySevenAI_483498887150858771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379275 : Nat.totient 43743874711804423897920379275 = 23251071934333632163156462080 := by
  rw [← show ((([(3, 1), (5, 2), (547, 1), (643, 1), (183349, 1), (9044387076075733, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379275 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_3, prime_thirtySevenAI_5, prime_thirtySevenAI_547, prime_thirtySevenAI_643, prime_thirtySevenAI_183349, prime_thirtySevenAI_9044387076075733]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379276 : Nat.totient 43743874711804423897920379276 = 20574288698492435108394528000 := by
  rw [← show ((([(2, 2), (19, 1), (211, 1), (431, 1), (46447, 1), (330541181, 1), (412250023, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379276 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_2, prime_thirtySevenAI_19, prime_thirtySevenAI_211, prime_thirtySevenAI_431, prime_thirtySevenAI_46447, prime_thirtySevenAI_330541181, prime_thirtySevenAI_412250023]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379277 : Nat.totient 43743874711804423897920379277 = 34071627605696494439096889600 := by
  rw [← show ((([(7, 1), (11, 1), (2423, 1), (79181, 1), (3249143, 1), (911346020789, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379277 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_7, prime_thirtySevenAI_11, prime_thirtySevenAI_2423, prime_thirtySevenAI_79181, prime_thirtySevenAI_3249143, prime_thirtySevenAI_911346020789]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379278 : Nat.totient 43743874711804423897920379278 = 13459642551866878003877511168 := by
  rw [← show ((([(2, 1), (3, 1), (13, 1), (1201153, 1), (466900475261349035617, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379278 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_2, prime_thirtySevenAI_3, prime_thirtySevenAI_13, prime_thirtySevenAI_1201153, prime_thirtySevenAI_466900475261349035617]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379279 : Nat.totient 43743874711804423897920379279 = 43742967650561402797171392000 := by
  rw [← show ((([(61651, 1), (221461, 1), (3203906746898167489, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379279 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_61651, prime_thirtySevenAI_221461, prime_thirtySevenAI_3203906746898167489]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379280 : Nat.totient 43743874711804423897920379280 = 17496574493123312467381013888 := by
  rw [← show ((([(2, 4), (5, 1), (17939, 1), (30480987451784118330119, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379280 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_2, prime_thirtySevenAI_5, prime_thirtySevenAI_17939, prime_thirtySevenAI_30480987451784118330119]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379281 : Nat.totient 43743874711804423897920379281 = 29162583141175872682269003504 := by
  rw [← show ((([(3, 3), (1077813008567, 1), (1503176798727509, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379281 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_3, prime_thirtySevenAI_1077813008567, prime_thirtySevenAI_1503176798727509]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379282 : Nat.totient 43743874711804423897920379282 = 21335394098397748629364070400 := by
  rw [← show ((([(2, 1), (41, 1), (8419, 1), (39019, 1), (1623927933438594241, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379282 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_2, prime_thirtySevenAI_41, prime_thirtySevenAI_8419, prime_thirtySevenAI_39019, prime_thirtySevenAI_1623927933438594241]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379283 : Nat.totient 43743874711804423897920379283 = 43743874709678387754997378848 := by
  rw [← show ((([(20575320547, 1), (2126036122347679889, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379283 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_20575320547, prime_thirtySevenAI_2126036122347679889]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379284 : Nat.totient 43743874711804423897920379284 = 12459140039303841361645094400 := by
  rw [← show ((([(2, 2), (3, 1), (7, 1), (523, 1), (821, 1), (671467, 1), (1806210835639541, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379284 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_2, prime_thirtySevenAI_3, prime_thirtySevenAI_7, prime_thirtySevenAI_523, prime_thirtySevenAI_821, prime_thirtySevenAI_671467, prime_thirtySevenAI_1806210835639541]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379285 : Nat.totient 43743874711804423897920379285 = 32860498329129322553445531648 := by
  rw [← show ((([(5, 1), (17, 1), (433, 1), (172078549, 1), (6906908323857613, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379285 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_5, prime_thirtySevenAI_17, prime_thirtySevenAI_433, prime_thirtySevenAI_172078549, prime_thirtySevenAI_6906908323857613]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379286 : Nat.totient 43743874711804423897920379286 = 21343190483770422931401217704 := by
  rw [← show ((([(2, 1), (43, 1), (1063, 1), (478503956680352052089527, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379286 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_2, prime_thirtySevenAI_43, prime_thirtySevenAI_1063, prime_thirtySevenAI_478503956680352052089527]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379287 : Nat.totient 43743874711804423897920379287 = 27994219734509348945901863552 := by
  rw [← show ((([(3, 1), (29, 1), (173, 1), (2906376633566169948702437, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379287 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_3, prime_thirtySevenAI_29, prime_thirtySevenAI_173, prime_thirtySevenAI_2906376633566169948702437]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379288 : Nat.totient 43743874711804423897920379288 = 19883380380229044202828032000 := by
  rw [← show ((([(2, 3), (11, 1), (99901, 1), (14936747537, 1), (333126130973, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379288 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_2, prime_thirtySevenAI_11, prime_thirtySevenAI_99901, prime_thirtySevenAI_14936747537, prime_thirtySevenAI_333126130973]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379289 : Nat.totient 43743874711804423897920379289 = 43738195885887372437232745056 := by
  rw [← show ((([(7703, 1), (2776917799, 1), (2045004777760537, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379289 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_7703, prime_thirtySevenAI_2776917799, prime_thirtySevenAI_2045004777760537]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379290 : Nat.totient 43743874711804423897920379290 = 11443107307661686748315169792 := by
  rw [← show ((([(2, 1), (3, 2), (5, 1), (89, 1), (127, 1), (289453, 1), (148560364691441459, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379290 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_2, prime_thirtySevenAI_3, prime_thirtySevenAI_5, prime_thirtySevenAI_89, prime_thirtySevenAI_127, prime_thirtySevenAI_289453, prime_thirtySevenAI_148560364691441459]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379291 : Nat.totient 43743874711804423897920379291 = 34610538228389161300005525504 := by
  rw [← show ((([(7, 1), (13, 1), (6751396753, 1), (71200366012608817, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379291 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_7, prime_thirtySevenAI_13, prime_thirtySevenAI_6751396753, prime_thirtySevenAI_71200366012608817]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379292 : Nat.totient 43743874711804423897920379292 = 20920980106257549454784045376 := by
  rw [← show ((([(2, 2), (23, 1), (6061309, 1), (78444589946058257989, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379292 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_2, prime_thirtySevenAI_23, prime_thirtySevenAI_6061309, prime_thirtySevenAI_78444589946058257989]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379293 : Nat.totient 43743874711804423897920379293 = 28221851457292162132281654000 := by
  rw [← show ((([(3, 1), (31, 1), (8831791, 1), (53258081425721101711, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379293 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_3, prime_thirtySevenAI_31, prime_thirtySevenAI_8831791, prime_thirtySevenAI_53258081425721101711]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379294 : Nat.totient 43743874711804423897920379294 = 21395147952165013757718599040 := by
  rw [← show ((([(2, 1), (47, 1), (1873, 1), (8786883271, 1), (28275921087847, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379294 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_2, prime_thirtySevenAI_47, prime_thirtySevenAI_1873, prime_thirtySevenAI_8786883271, prime_thirtySevenAI_28275921087847]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379295 : Nat.totient 43743874711804423897920379295 = 33153252413157037059476497920 := by
  rw [← show ((([(5, 1), (19, 1), (460461839071625514714951361, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379295 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_5, prime_thirtySevenAI_19, prime_thirtySevenAI_460461839071625514714951361]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379296 : Nat.totient 43743874711804423897920379296 = 14581291570601474632640126400 := by
  rw [← show ((([(2, 5), (3, 1), (455665361581296082270003951, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379296 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_2, prime_thirtySevenAI_3, prime_thirtySevenAI_455665361581296082270003951]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379297 : Nat.totient 43743874711804423897920379297 = 43356760776264932551839260928 := by
  rw [← show ((([(113, 1), (1182514485653, 1), (327365068419373, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379297 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_113, prime_thirtySevenAI_1182514485653, prime_thirtySevenAI_327365068419373]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379298 : Nat.totient 43743874711804423897920379298 = 18747374876487610241965876800 := by
  rw [← show ((([(2, 1), (7, 2), (446366068487800243856330401, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379298 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_2, prime_thirtySevenAI_7, prime_thirtySevenAI_446366068487800243856330401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379299 : Nat.totient 43743874711804423897920379299 = 26444167908439831963691765760 := by
  rw [← show ((([(3, 2), (11, 1), (593, 1), (1327, 1), (10159, 1), (1661117, 1), (33274018597, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379299 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_3, prime_thirtySevenAI_11, prime_thirtySevenAI_593, prime_thirtySevenAI_1327, prime_thirtySevenAI_10159, prime_thirtySevenAI_1661117, prime_thirtySevenAI_33274018597]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_thirtySevenAI_43743874711804423897920379300 : Nat.totient 43743874711804423897920379300 = 17497549884721769559168151680 := by
  rw [← show ((([(2, 2), (5, 2), (437438747118044238979203793, 1)] : List FactorBlock).map factorBlockValue).prod) = 43743874711804423897920379300 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_thirtySevenAI_2, prime_thirtySevenAI_5, prime_thirtySevenAI_437438747118044238979203793]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64ThirtySevenAI : certifiedKill 2 43743874711804423897920379199 99 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_thirtySevenAI_43743874711804423897920379200, phi_thirtySevenAI_43743874711804423897920379201, phi_thirtySevenAI_43743874711804423897920379202,
    phi_thirtySevenAI_43743874711804423897920379203, phi_thirtySevenAI_43743874711804423897920379204, phi_thirtySevenAI_43743874711804423897920379205,
    phi_thirtySevenAI_43743874711804423897920379206, phi_thirtySevenAI_43743874711804423897920379207, phi_thirtySevenAI_43743874711804423897920379208,
    phi_thirtySevenAI_43743874711804423897920379209, phi_thirtySevenAI_43743874711804423897920379210, phi_thirtySevenAI_43743874711804423897920379211,
    phi_thirtySevenAI_43743874711804423897920379212, phi_thirtySevenAI_43743874711804423897920379213, phi_thirtySevenAI_43743874711804423897920379214,
    phi_thirtySevenAI_43743874711804423897920379215, phi_thirtySevenAI_43743874711804423897920379216, phi_thirtySevenAI_43743874711804423897920379217,
    phi_thirtySevenAI_43743874711804423897920379218, phi_thirtySevenAI_43743874711804423897920379219, phi_thirtySevenAI_43743874711804423897920379220,
    phi_thirtySevenAI_43743874711804423897920379221, phi_thirtySevenAI_43743874711804423897920379222, phi_thirtySevenAI_43743874711804423897920379223,
    phi_thirtySevenAI_43743874711804423897920379224, phi_thirtySevenAI_43743874711804423897920379225, phi_thirtySevenAI_43743874711804423897920379226,
    phi_thirtySevenAI_43743874711804423897920379227, phi_thirtySevenAI_43743874711804423897920379228, phi_thirtySevenAI_43743874711804423897920379229,
    phi_thirtySevenAI_43743874711804423897920379230, phi_thirtySevenAI_43743874711804423897920379231, phi_thirtySevenAI_43743874711804423897920379232,
    phi_thirtySevenAI_43743874711804423897920379233, phi_thirtySevenAI_43743874711804423897920379234, phi_thirtySevenAI_43743874711804423897920379235,
    phi_thirtySevenAI_43743874711804423897920379236, phi_thirtySevenAI_43743874711804423897920379237, phi_thirtySevenAI_43743874711804423897920379238,
    phi_thirtySevenAI_43743874711804423897920379239, phi_thirtySevenAI_43743874711804423897920379240, phi_thirtySevenAI_43743874711804423897920379241,
    phi_thirtySevenAI_43743874711804423897920379242, phi_thirtySevenAI_43743874711804423897920379243, phi_thirtySevenAI_43743874711804423897920379244,
    phi_thirtySevenAI_43743874711804423897920379245, phi_thirtySevenAI_43743874711804423897920379246, phi_thirtySevenAI_43743874711804423897920379247,
    phi_thirtySevenAI_43743874711804423897920379248, phi_thirtySevenAI_43743874711804423897920379249, phi_thirtySevenAI_43743874711804423897920379250,
    phi_thirtySevenAI_43743874711804423897920379251, phi_thirtySevenAI_43743874711804423897920379252, phi_thirtySevenAI_43743874711804423897920379253,
    phi_thirtySevenAI_43743874711804423897920379254, phi_thirtySevenAI_43743874711804423897920379255, phi_thirtySevenAI_43743874711804423897920379256,
    phi_thirtySevenAI_43743874711804423897920379257, phi_thirtySevenAI_43743874711804423897920379258, phi_thirtySevenAI_43743874711804423897920379259,
    phi_thirtySevenAI_43743874711804423897920379260, phi_thirtySevenAI_43743874711804423897920379261, phi_thirtySevenAI_43743874711804423897920379262,
    phi_thirtySevenAI_43743874711804423897920379263, phi_thirtySevenAI_43743874711804423897920379264, phi_thirtySevenAI_43743874711804423897920379265,
    phi_thirtySevenAI_43743874711804423897920379266, phi_thirtySevenAI_43743874711804423897920379267, phi_thirtySevenAI_43743874711804423897920379268,
    phi_thirtySevenAI_43743874711804423897920379269, phi_thirtySevenAI_43743874711804423897920379270, phi_thirtySevenAI_43743874711804423897920379271,
    phi_thirtySevenAI_43743874711804423897920379272, phi_thirtySevenAI_43743874711804423897920379273, phi_thirtySevenAI_43743874711804423897920379274,
    phi_thirtySevenAI_43743874711804423897920379275, phi_thirtySevenAI_43743874711804423897920379276, phi_thirtySevenAI_43743874711804423897920379277,
    phi_thirtySevenAI_43743874711804423897920379278, phi_thirtySevenAI_43743874711804423897920379279, phi_thirtySevenAI_43743874711804423897920379280,
    phi_thirtySevenAI_43743874711804423897920379281, phi_thirtySevenAI_43743874711804423897920379282, phi_thirtySevenAI_43743874711804423897920379283,
    phi_thirtySevenAI_43743874711804423897920379284, phi_thirtySevenAI_43743874711804423897920379285, phi_thirtySevenAI_43743874711804423897920379286,
    phi_thirtySevenAI_43743874711804423897920379287, phi_thirtySevenAI_43743874711804423897920379288, phi_thirtySevenAI_43743874711804423897920379289,
    phi_thirtySevenAI_43743874711804423897920379290, phi_thirtySevenAI_43743874711804423897920379291, phi_thirtySevenAI_43743874711804423897920379292,
    phi_thirtySevenAI_43743874711804423897920379293, phi_thirtySevenAI_43743874711804423897920379294, phi_thirtySevenAI_43743874711804423897920379295,
    phi_thirtySevenAI_43743874711804423897920379296, phi_thirtySevenAI_43743874711804423897920379297, phi_thirtySevenAI_43743874711804423897920379298,
    phi_thirtySevenAI_43743874711804423897920379299, phi_thirtySevenAI_43743874711804423897920379300]

end TotientTailPeriodKiller
end Erdos249257
