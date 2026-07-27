import Erdos249257.DiagonalPincerCertificatesT64

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def seventySevenBWFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem seventySevenBWFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : seventySevenBWFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [seventySevenBWFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [seventySevenBWFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then seventySevenBWFastPow a n * seventySevenBWFastPow a n * a else seventySevenBWFastPow a n * seventySevenBWFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_seventySevenBW_2 : Nat.Prime 2 := by norm_num
private theorem prime_seventySevenBW_3 : Nat.Prime 3 := by norm_num
private theorem prime_seventySevenBW_5 : Nat.Prime 5 := by norm_num
private theorem prime_seventySevenBW_7 : Nat.Prime 7 := by norm_num
private theorem prime_seventySevenBW_11 : Nat.Prime 11 := by norm_num
private theorem prime_seventySevenBW_13 : Nat.Prime 13 := by norm_num
private theorem prime_seventySevenBW_17 : Nat.Prime 17 := by norm_num
private theorem prime_seventySevenBW_19 : Nat.Prime 19 := by norm_num
private theorem prime_seventySevenBW_23 : Nat.Prime 23 := by norm_num
private theorem prime_seventySevenBW_29 : Nat.Prime 29 := by norm_num
private theorem prime_seventySevenBW_31 : Nat.Prime 31 := by norm_num
private theorem prime_seventySevenBW_37 : Nat.Prime 37 := by norm_num
private theorem prime_seventySevenBW_41 : Nat.Prime 41 := by norm_num
private theorem prime_seventySevenBW_43 : Nat.Prime 43 := by norm_num
private theorem prime_seventySevenBW_47 : Nat.Prime 47 := by norm_num
private theorem prime_seventySevenBW_53 : Nat.Prime 53 := by norm_num
private theorem prime_seventySevenBW_59 : Nat.Prime 59 := by norm_num
private theorem prime_seventySevenBW_61 : Nat.Prime 61 := by norm_num
private theorem prime_seventySevenBW_67 : Nat.Prime 67 := by norm_num
private theorem prime_seventySevenBW_71 : Nat.Prime 71 := by norm_num
private theorem prime_seventySevenBW_73 : Nat.Prime 73 := by norm_num
private theorem prime_seventySevenBW_79 : Nat.Prime 79 := by norm_num
private theorem prime_seventySevenBW_83 : Nat.Prime 83 := by norm_num
private theorem prime_seventySevenBW_89 : Nat.Prime 89 := by norm_num
private theorem prime_seventySevenBW_97 : Nat.Prime 97 := by norm_num
private theorem prime_seventySevenBW_101 : Nat.Prime 101 := by norm_num
private theorem prime_seventySevenBW_103 : Nat.Prime 103 := by norm_num
private theorem prime_seventySevenBW_107 : Nat.Prime 107 := by norm_num
private theorem prime_seventySevenBW_109 : Nat.Prime 109 := by norm_num
private theorem prime_seventySevenBW_113 : Nat.Prime 113 := by norm_num
private theorem prime_seventySevenBW_127 : Nat.Prime 127 := by norm_num
private theorem prime_seventySevenBW_131 : Nat.Prime 131 := by norm_num
private theorem prime_seventySevenBW_139 : Nat.Prime 139 := by norm_num
private theorem prime_seventySevenBW_151 : Nat.Prime 151 := by norm_num
private theorem prime_seventySevenBW_157 : Nat.Prime 157 := by norm_num
private theorem prime_seventySevenBW_163 : Nat.Prime 163 := by norm_num
private theorem prime_seventySevenBW_167 : Nat.Prime 167 := by norm_num
private theorem prime_seventySevenBW_173 : Nat.Prime 173 := by norm_num
private theorem prime_seventySevenBW_179 : Nat.Prime 179 := by norm_num
private theorem prime_seventySevenBW_181 : Nat.Prime 181 := by norm_num
private theorem prime_seventySevenBW_191 : Nat.Prime 191 := by norm_num
private theorem prime_seventySevenBW_193 : Nat.Prime 193 := by norm_num
private theorem prime_seventySevenBW_197 : Nat.Prime 197 := by norm_num
private theorem prime_seventySevenBW_199 : Nat.Prime 199 := by norm_num
private theorem prime_seventySevenBW_211 : Nat.Prime 211 := by norm_num
private theorem prime_seventySevenBW_227 : Nat.Prime 227 := by norm_num
private theorem prime_seventySevenBW_229 : Nat.Prime 229 := by norm_num
private theorem prime_seventySevenBW_233 : Nat.Prime 233 := by norm_num
private theorem prime_seventySevenBW_239 : Nat.Prime 239 := by norm_num
private theorem prime_seventySevenBW_241 : Nat.Prime 241 := by norm_num
private theorem prime_seventySevenBW_251 : Nat.Prime 251 := by norm_num
private theorem prime_seventySevenBW_257 : Nat.Prime 257 := by norm_num
private theorem prime_seventySevenBW_263 : Nat.Prime 263 := by norm_num
private theorem prime_seventySevenBW_269 : Nat.Prime 269 := by norm_num
private theorem prime_seventySevenBW_271 : Nat.Prime 271 := by norm_num
private theorem prime_seventySevenBW_277 : Nat.Prime 277 := by norm_num
private theorem prime_seventySevenBW_283 : Nat.Prime 283 := by norm_num
private theorem prime_seventySevenBW_307 : Nat.Prime 307 := by norm_num
private theorem prime_seventySevenBW_311 : Nat.Prime 311 := by norm_num
private theorem prime_seventySevenBW_313 : Nat.Prime 313 := by norm_num
private theorem prime_seventySevenBW_317 : Nat.Prime 317 := by norm_num
private theorem prime_seventySevenBW_331 : Nat.Prime 331 := by norm_num
private theorem prime_seventySevenBW_347 : Nat.Prime 347 := by norm_num
private theorem prime_seventySevenBW_349 : Nat.Prime 349 := by norm_num
private theorem prime_seventySevenBW_367 : Nat.Prime 367 := by norm_num
private theorem prime_seventySevenBW_379 : Nat.Prime 379 := by norm_num
private theorem prime_seventySevenBW_383 : Nat.Prime 383 := by norm_num
private theorem prime_seventySevenBW_389 : Nat.Prime 389 := by norm_num
private theorem prime_seventySevenBW_409 : Nat.Prime 409 := by norm_num
private theorem prime_seventySevenBW_433 : Nat.Prime 433 := by norm_num
private theorem prime_seventySevenBW_449 : Nat.Prime 449 := by norm_num
private theorem prime_seventySevenBW_457 : Nat.Prime 457 := by norm_num
private theorem prime_seventySevenBW_463 : Nat.Prime 463 := by norm_num
private theorem prime_seventySevenBW_487 : Nat.Prime 487 := by norm_num
private theorem prime_seventySevenBW_491 : Nat.Prime 491 := by norm_num
private theorem prime_seventySevenBW_503 : Nat.Prime 503 := by norm_num
private theorem prime_seventySevenBW_547 : Nat.Prime 547 := by norm_num
private theorem prime_seventySevenBW_557 : Nat.Prime 557 := by norm_num
private theorem prime_seventySevenBW_569 : Nat.Prime 569 := by norm_num
private theorem prime_seventySevenBW_577 : Nat.Prime 577 := by norm_num
private theorem prime_seventySevenBW_587 : Nat.Prime 587 := by norm_num
private theorem prime_seventySevenBW_601 : Nat.Prime 601 := by norm_num
private theorem prime_seventySevenBW_607 : Nat.Prime 607 := by norm_num
private theorem prime_seventySevenBW_613 : Nat.Prime 613 := by norm_num
private theorem prime_seventySevenBW_619 : Nat.Prime 619 := by norm_num
private theorem prime_seventySevenBW_641 : Nat.Prime 641 := by norm_num
private theorem prime_seventySevenBW_643 : Nat.Prime 643 := by norm_num
private theorem prime_seventySevenBW_653 : Nat.Prime 653 := by norm_num
private theorem prime_seventySevenBW_677 : Nat.Prime 677 := by norm_num
private theorem prime_seventySevenBW_683 : Nat.Prime 683 := by norm_num
private theorem prime_seventySevenBW_719 : Nat.Prime 719 := by norm_num
private theorem prime_seventySevenBW_727 : Nat.Prime 727 := by norm_num
private theorem prime_seventySevenBW_733 : Nat.Prime 733 := by norm_num
private theorem prime_seventySevenBW_743 : Nat.Prime 743 := by norm_num
private theorem prime_seventySevenBW_761 : Nat.Prime 761 := by norm_num
private theorem prime_seventySevenBW_773 : Nat.Prime 773 := by norm_num
private theorem prime_seventySevenBW_797 : Nat.Prime 797 := by norm_num
private theorem prime_seventySevenBW_809 : Nat.Prime 809 := by norm_num
private theorem prime_seventySevenBW_811 : Nat.Prime 811 := by norm_num
private theorem prime_seventySevenBW_821 : Nat.Prime 821 := by norm_num
private theorem prime_seventySevenBW_857 : Nat.Prime 857 := by norm_num
private theorem prime_seventySevenBW_877 : Nat.Prime 877 := by norm_num
private theorem prime_seventySevenBW_881 : Nat.Prime 881 := by norm_num
private theorem prime_seventySevenBW_883 : Nat.Prime 883 := by norm_num
private theorem prime_seventySevenBW_941 : Nat.Prime 941 := by norm_num
private theorem prime_seventySevenBW_953 : Nat.Prime 953 := by norm_num
private theorem prime_seventySevenBW_977 : Nat.Prime 977 := by norm_num
private theorem prime_seventySevenBW_1031 : Nat.Prime 1031 := by norm_num
private theorem prime_seventySevenBW_1051 : Nat.Prime 1051 := by norm_num
private theorem prime_seventySevenBW_1103 : Nat.Prime 1103 := by norm_num
private theorem prime_seventySevenBW_1123 : Nat.Prime 1123 := by norm_num
private theorem prime_seventySevenBW_1181 : Nat.Prime 1181 := by norm_num
private theorem prime_seventySevenBW_1187 : Nat.Prime 1187 := by norm_num
private theorem prime_seventySevenBW_1193 : Nat.Prime 1193 := by norm_num
private theorem prime_seventySevenBW_1259 : Nat.Prime 1259 := by norm_num
private theorem prime_seventySevenBW_1279 : Nat.Prime 1279 := by norm_num
private theorem prime_seventySevenBW_1367 : Nat.Prime 1367 := by norm_num
private theorem prime_seventySevenBW_1439 : Nat.Prime 1439 := by norm_num
private theorem prime_seventySevenBW_1471 : Nat.Prime 1471 := by norm_num
private theorem prime_seventySevenBW_1481 : Nat.Prime 1481 := by norm_num
private theorem prime_seventySevenBW_1487 : Nat.Prime 1487 := by norm_num
private theorem prime_seventySevenBW_1531 : Nat.Prime 1531 := by norm_num
private theorem prime_seventySevenBW_1553 : Nat.Prime 1553 := by norm_num
private theorem prime_seventySevenBW_1567 : Nat.Prime 1567 := by norm_num
private theorem prime_seventySevenBW_1811 : Nat.Prime 1811 := by norm_num
private theorem prime_seventySevenBW_1831 : Nat.Prime 1831 := by norm_num
private theorem prime_seventySevenBW_1861 : Nat.Prime 1861 := by norm_num
private theorem prime_seventySevenBW_1871 : Nat.Prime 1871 := by norm_num
private theorem prime_seventySevenBW_1933 : Nat.Prime 1933 := by norm_num
private theorem prime_seventySevenBW_1993 : Nat.Prime 1993 := by norm_num
private theorem prime_seventySevenBW_1999 : Nat.Prime 1999 := by norm_num
private theorem prime_seventySevenBW_2027 : Nat.Prime 2027 := by norm_num
private theorem prime_seventySevenBW_2029 : Nat.Prime 2029 := by norm_num
private theorem prime_seventySevenBW_2053 : Nat.Prime 2053 := by norm_num
private theorem prime_seventySevenBW_2063 : Nat.Prime 2063 := by norm_num
private theorem prime_seventySevenBW_2099 : Nat.Prime 2099 := by norm_num
private theorem prime_seventySevenBW_2141 : Nat.Prime 2141 := by norm_num
private theorem prime_seventySevenBW_2179 : Nat.Prime 2179 := by norm_num
private theorem prime_seventySevenBW_2239 : Nat.Prime 2239 := by norm_num
private theorem prime_seventySevenBW_2311 : Nat.Prime 2311 := by norm_num
private theorem prime_seventySevenBW_2441 : Nat.Prime 2441 := by norm_num
private theorem prime_seventySevenBW_2543 : Nat.Prime 2543 := by norm_num
private theorem prime_seventySevenBW_2593 : Nat.Prime 2593 := by norm_num
private theorem prime_seventySevenBW_2647 : Nat.Prime 2647 := by norm_num
private theorem prime_seventySevenBW_2683 : Nat.Prime 2683 := by norm_num
private theorem prime_seventySevenBW_2693 : Nat.Prime 2693 := by norm_num
private theorem prime_seventySevenBW_2713 : Nat.Prime 2713 := by norm_num
private theorem prime_seventySevenBW_2791 : Nat.Prime 2791 := by norm_num
private theorem prime_seventySevenBW_2797 : Nat.Prime 2797 := by norm_num
private theorem prime_seventySevenBW_2801 : Nat.Prime 2801 := by norm_num
private theorem prime_seventySevenBW_2857 : Nat.Prime 2857 := by norm_num
private theorem prime_seventySevenBW_2903 : Nat.Prime 2903 := by norm_num
private theorem prime_seventySevenBW_2971 : Nat.Prime 2971 := by norm_num
private theorem prime_seventySevenBW_3079 : Nat.Prime 3079 := by norm_num
private theorem prime_seventySevenBW_3089 : Nat.Prime 3089 := by norm_num
private theorem prime_seventySevenBW_3109 : Nat.Prime 3109 := by norm_num
private theorem prime_seventySevenBW_3229 : Nat.Prime 3229 := by norm_num
private theorem prime_seventySevenBW_3323 : Nat.Prime 3323 := by norm_num
private theorem prime_seventySevenBW_3491 : Nat.Prime 3491 := by norm_num
private theorem prime_seventySevenBW_3499 : Nat.Prime 3499 := by norm_num
private theorem prime_seventySevenBW_3643 : Nat.Prime 3643 := by norm_num
private theorem prime_seventySevenBW_3803 : Nat.Prime 3803 := by norm_num
private theorem prime_seventySevenBW_4003 : Nat.Prime 4003 := by norm_num
private theorem prime_seventySevenBW_4211 : Nat.Prime 4211 := by norm_num
private theorem prime_seventySevenBW_4231 : Nat.Prime 4231 := by norm_num
private theorem prime_seventySevenBW_4409 : Nat.Prime 4409 := by norm_num
private theorem prime_seventySevenBW_4457 : Nat.Prime 4457 := by norm_num
private theorem prime_seventySevenBW_4481 : Nat.Prime 4481 := by norm_num
private theorem prime_seventySevenBW_4483 : Nat.Prime 4483 := by norm_num
private theorem prime_seventySevenBW_4801 : Nat.Prime 4801 := by norm_num
private theorem prime_seventySevenBW_4861 : Nat.Prime 4861 := by norm_num
private theorem prime_seventySevenBW_4937 : Nat.Prime 4937 := by norm_num
private theorem prime_seventySevenBW_5021 : Nat.Prime 5021 := by norm_num
private theorem prime_seventySevenBW_5087 : Nat.Prime 5087 := by norm_num
private theorem prime_seventySevenBW_5189 : Nat.Prime 5189 := by norm_num
private theorem prime_seventySevenBW_5387 : Nat.Prime 5387 := by norm_num
private theorem prime_seventySevenBW_5711 : Nat.Prime 5711 := by norm_num
private theorem prime_seventySevenBW_5843 : Nat.Prime 5843 := by norm_num
private theorem prime_seventySevenBW_5881 : Nat.Prime 5881 := by norm_num
private theorem prime_seventySevenBW_5923 : Nat.Prime 5923 := by norm_num
private theorem prime_seventySevenBW_6011 : Nat.Prime 6011 := by norm_num
private theorem prime_seventySevenBW_6337 : Nat.Prime 6337 := by norm_num
private theorem prime_seventySevenBW_6449 : Nat.Prime 6449 := by norm_num
private theorem prime_seventySevenBW_6451 : Nat.Prime 6451 := by norm_num
private theorem prime_seventySevenBW_6841 : Nat.Prime 6841 := by norm_num
private theorem prime_seventySevenBW_6869 : Nat.Prime 6869 := by norm_num
private theorem prime_seventySevenBW_7297 : Nat.Prime 7297 := by norm_num
private theorem prime_seventySevenBW_7331 : Nat.Prime 7331 := by norm_num
private theorem prime_seventySevenBW_7643 : Nat.Prime 7643 := by norm_num
private theorem prime_seventySevenBW_7687 : Nat.Prime 7687 := by norm_num
private theorem prime_seventySevenBW_7951 : Nat.Prime 7951 := by norm_num
private theorem prime_seventySevenBW_8089 : Nat.Prime 8089 := by norm_num
private theorem prime_seventySevenBW_8191 : Nat.Prime 8191 := by norm_num
private theorem prime_seventySevenBW_8467 : Nat.Prime 8467 := by norm_num
private theorem prime_seventySevenBW_8663 : Nat.Prime 8663 := by norm_num
private theorem prime_seventySevenBW_8839 : Nat.Prime 8839 := by norm_num
private theorem prime_seventySevenBW_8999 : Nat.Prime 8999 := by norm_num
private theorem prime_seventySevenBW_9337 : Nat.Prime 9337 := by norm_num
private theorem prime_seventySevenBW_9497 : Nat.Prime 9497 := by norm_num
private theorem prime_seventySevenBW_10273 : Nat.Prime 10273 := by norm_num
private theorem prime_seventySevenBW_10513 : Nat.Prime 10513 := by norm_num
private theorem prime_seventySevenBW_12239 : Nat.Prime 12239 := by norm_num
private theorem prime_seventySevenBW_13217 : Nat.Prime 13217 := by norm_num
private theorem prime_seventySevenBW_13421 : Nat.Prime 13421 := by norm_num
private theorem prime_seventySevenBW_13619 : Nat.Prime 13619 := by norm_num
private theorem prime_seventySevenBW_14303 : Nat.Prime 14303 := by norm_num
private theorem prime_seventySevenBW_15731 : Nat.Prime 15731 := by norm_num
private theorem prime_seventySevenBW_16333 : Nat.Prime 16333 := by norm_num
private theorem prime_seventySevenBW_16369 : Nat.Prime 16369 := by norm_num
private theorem prime_seventySevenBW_16603 : Nat.Prime 16603 := by norm_num
private theorem prime_seventySevenBW_16649 : Nat.Prime 16649 := by norm_num
private theorem prime_seventySevenBW_17191 : Nat.Prime 17191 := by norm_num
private theorem prime_seventySevenBW_17231 : Nat.Prime 17231 := by norm_num
private theorem prime_seventySevenBW_18691 : Nat.Prime 18691 := by norm_num
private theorem prime_seventySevenBW_19037 : Nat.Prime 19037 := by norm_num
private theorem prime_seventySevenBW_19301 : Nat.Prime 19301 := by norm_num
private theorem prime_seventySevenBW_19937 : Nat.Prime 19937 := by norm_num
private theorem prime_seventySevenBW_21031 : Nat.Prime 21031 := by norm_num
private theorem prime_seventySevenBW_21191 : Nat.Prime 21191 := by norm_num
private theorem prime_seventySevenBW_21737 : Nat.Prime 21737 := by norm_num
private theorem prime_seventySevenBW_22133 : Nat.Prime 22133 := by norm_num
private theorem prime_seventySevenBW_23557 : Nat.Prime 23557 := by norm_num
private theorem prime_seventySevenBW_23719 : Nat.Prime 23719 := by norm_num
private theorem prime_seventySevenBW_24071 : Nat.Prime 24071 := by norm_num
private theorem prime_seventySevenBW_24547 : Nat.Prime 24547 := by norm_num
private theorem prime_seventySevenBW_26683 : Nat.Prime 26683 := by norm_num
private theorem prime_seventySevenBW_27893 : Nat.Prime 27893 := by norm_num
private theorem prime_seventySevenBW_27943 : Nat.Prime 27943 := by norm_num
private theorem prime_seventySevenBW_28603 : Nat.Prime 28603 := by norm_num
private theorem prime_seventySevenBW_29671 : Nat.Prime 29671 := by norm_num
private theorem prime_seventySevenBW_31247 : Nat.Prime 31247 := by norm_num
private theorem prime_seventySevenBW_32611 : Nat.Prime 32611 := by norm_num
private theorem prime_seventySevenBW_32717 : Nat.Prime 32717 := by norm_num
private theorem prime_seventySevenBW_33289 : Nat.Prime 33289 := by norm_num
private theorem prime_seventySevenBW_34721 : Nat.Prime 34721 := by norm_num
private theorem prime_seventySevenBW_34739 : Nat.Prime 34739 := by norm_num
private theorem prime_seventySevenBW_35281 : Nat.Prime 35281 := by norm_num
private theorem prime_seventySevenBW_36187 : Nat.Prime 36187 := by norm_num
private theorem prime_seventySevenBW_37003 : Nat.Prime 37003 := by norm_num
private theorem prime_seventySevenBW_41017 : Nat.Prime 41017 := by norm_num
private theorem prime_seventySevenBW_42767 : Nat.Prime 42767 := by norm_num
private theorem prime_seventySevenBW_43237 : Nat.Prime 43237 := by norm_num
private theorem prime_seventySevenBW_44987 : Nat.Prime 44987 := by norm_num
private theorem prime_seventySevenBW_45083 : Nat.Prime 45083 := by norm_num
private theorem prime_seventySevenBW_45191 : Nat.Prime 45191 := by norm_num
private theorem prime_seventySevenBW_45959 : Nat.Prime 45959 := by norm_num
private theorem prime_seventySevenBW_47051 : Nat.Prime 47051 := by norm_num
private theorem prime_seventySevenBW_48757 : Nat.Prime 48757 := by norm_num
private theorem prime_seventySevenBW_50291 : Nat.Prime 50291 := by norm_num
private theorem prime_seventySevenBW_59263 : Nat.Prime 59263 := by norm_num
private theorem prime_seventySevenBW_61099 : Nat.Prime 61099 := by norm_num
private theorem prime_seventySevenBW_61253 : Nat.Prime 61253 := by norm_num
private theorem prime_seventySevenBW_63649 : Nat.Prime 63649 := by norm_num
private theorem prime_seventySevenBW_64063 : Nat.Prime 64063 := by norm_num
private theorem prime_seventySevenBW_66029 : Nat.Prime 66029 := by norm_num
private theorem prime_seventySevenBW_66697 : Nat.Prime 66697 := by norm_num
private theorem prime_seventySevenBW_67049 : Nat.Prime 67049 := by norm_num
private theorem prime_seventySevenBW_69457 : Nat.Prime 69457 := by norm_num
private theorem prime_seventySevenBW_72503 : Nat.Prime 72503 := by norm_num
private theorem prime_seventySevenBW_72859 : Nat.Prime 72859 := by norm_num
private theorem prime_seventySevenBW_84467 : Nat.Prime 84467 := by norm_num
private theorem prime_seventySevenBW_92557 : Nat.Prime 92557 := by norm_num
private theorem prime_seventySevenBW_96323 : Nat.Prime 96323 := by norm_num
private theorem prime_seventySevenBW_97613 : Nat.Prime 97613 := by norm_num
private theorem prime_seventySevenBW_97729 : Nat.Prime 97729 := by norm_num
private theorem prime_seventySevenBW_117721 : Nat.Prime 117721 := by norm_num
private theorem prime_seventySevenBW_122173 : Nat.Prime 122173 := by norm_num
private theorem prime_seventySevenBW_125471 : Nat.Prime 125471 := by norm_num
private theorem prime_seventySevenBW_130841 : Nat.Prime 130841 := by norm_num
private theorem prime_seventySevenBW_139291 : Nat.Prime 139291 := by norm_num
private theorem prime_seventySevenBW_143687 : Nat.Prime 143687 := by norm_num
private theorem prime_seventySevenBW_145753 : Nat.Prime 145753 := by norm_num
private theorem prime_seventySevenBW_159571 : Nat.Prime 159571 := by norm_num
private theorem prime_seventySevenBW_172987 : Nat.Prime 172987 := by norm_num
private theorem prime_seventySevenBW_178207 : Nat.Prime 178207 := by norm_num
private theorem prime_seventySevenBW_179281 : Nat.Prime 179281 := by norm_num
private theorem prime_seventySevenBW_179527 : Nat.Prime 179527 := by norm_num
private theorem prime_seventySevenBW_182041 : Nat.Prime 182041 := by norm_num
private theorem prime_seventySevenBW_194309 : Nat.Prime 194309 := by norm_num
private theorem prime_seventySevenBW_197381 : Nat.Prime 197381 := by norm_num
private theorem prime_seventySevenBW_203023 : Nat.Prime 203023 := by norm_num
private theorem prime_seventySevenBW_220123 : Nat.Prime 220123 := by norm_num
private theorem prime_seventySevenBW_222193 : Nat.Prime 222193 := by norm_num
private theorem prime_seventySevenBW_231479 : Nat.Prime 231479 := by norm_num
private theorem prime_seventySevenBW_238481 : Nat.Prime 238481 := by norm_num
private theorem prime_seventySevenBW_245783 : Nat.Prime 245783 := by norm_num
private theorem prime_seventySevenBW_256057 : Nat.Prime 256057 := by norm_num
private theorem prime_seventySevenBW_261721 : Nat.Prime 261721 := by norm_num
private theorem prime_seventySevenBW_265241 : Nat.Prime 265241 := by norm_num
private theorem prime_seventySevenBW_268759 : Nat.Prime 268759 := by norm_num
private theorem prime_seventySevenBW_280069 : Nat.Prime 280069 := by norm_num
private theorem prime_seventySevenBW_284707 : Nat.Prime 284707 := by norm_num
private theorem prime_seventySevenBW_300739 : Nat.Prime 300739 := by norm_num
private theorem prime_seventySevenBW_340103 : Nat.Prime 340103 := by norm_num
private theorem prime_seventySevenBW_344263 : Nat.Prime 344263 := by norm_num
private theorem prime_seventySevenBW_355093 : Nat.Prime 355093 := by norm_num
private theorem prime_seventySevenBW_396713 : Nat.Prime 396713 := by norm_num
private theorem prime_seventySevenBW_420323 : Nat.Prime 420323 := by norm_num
private theorem prime_seventySevenBW_435349 : Nat.Prime 435349 := by norm_num
private theorem prime_seventySevenBW_464351 : Nat.Prime 464351 := by norm_num
private theorem prime_seventySevenBW_476929 : Nat.Prime 476929 := by norm_num
private theorem prime_seventySevenBW_477941 : Nat.Prime 477941 := by norm_num
private theorem prime_seventySevenBW_484597 : Nat.Prime 484597 := by norm_num
private theorem prime_seventySevenBW_488417 : Nat.Prime 488417 := by norm_num
private theorem prime_seventySevenBW_498493 : Nat.Prime 498493 := by norm_num
private theorem prime_seventySevenBW_500009 : Nat.Prime 500009 := by norm_num
private theorem prime_seventySevenBW_504797 : Nat.Prime 504797 := by norm_num
private theorem prime_seventySevenBW_510319 : Nat.Prime 510319 := by norm_num
private theorem prime_seventySevenBW_521603 : Nat.Prime 521603 := by norm_num
private theorem prime_seventySevenBW_577939 : Nat.Prime 577939 := by norm_num
private theorem prime_seventySevenBW_578029 : Nat.Prime 578029 := by norm_num
private theorem prime_seventySevenBW_613967 : Nat.Prime 613967 := by norm_num
private theorem prime_seventySevenBW_720619 : Nat.Prime 720619 := by norm_num
private theorem prime_seventySevenBW_721547 : Nat.Prime 721547 := by norm_num
private theorem prime_seventySevenBW_729649 : Nat.Prime 729649 := by norm_num
private theorem prime_seventySevenBW_740659 : Nat.Prime 740659 := by norm_num
private theorem prime_seventySevenBW_741467 : Nat.Prime 741467 := by norm_num
private theorem prime_seventySevenBW_742037 : Nat.Prime 742037 := by norm_num
private theorem prime_seventySevenBW_748039 : Nat.Prime 748039 := by norm_num
private theorem prime_seventySevenBW_750797 : Nat.Prime 750797 := by norm_num
private theorem prime_seventySevenBW_815809 : Nat.Prime 815809 := by norm_num
private theorem prime_seventySevenBW_834341 : Nat.Prime 834341 := by norm_num
private theorem prime_seventySevenBW_837079 : Nat.Prime 837079 := by norm_num
private theorem prime_seventySevenBW_845237 : Nat.Prime 845237 := by norm_num
private theorem prime_seventySevenBW_853637 : Nat.Prime 853637 := by norm_num
private theorem prime_seventySevenBW_931237 : Nat.Prime 931237 := by norm_num
private theorem prime_seventySevenBW_964097 : Nat.Prime 964097 := by norm_num
private theorem prime_seventySevenBW_1128557 : Nat.Prime 1128557 := by norm_num
private theorem prime_seventySevenBW_1180381 : Nat.Prime 1180381 := by norm_num
private theorem prime_seventySevenBW_1249519 : Nat.Prime 1249519 := by norm_num
private theorem prime_seventySevenBW_1279309 : Nat.Prime 1279309 := by norm_num
private theorem prime_seventySevenBW_1358647 : Nat.Prime 1358647 := by norm_num
private theorem prime_seventySevenBW_1370459 : Nat.Prime 1370459 := by norm_num
private theorem prime_seventySevenBW_1409587 : Nat.Prime 1409587 := by norm_num
private theorem prime_seventySevenBW_1534411 : Nat.Prime 1534411 := by norm_num
private theorem prime_seventySevenBW_1540481 : Nat.Prime 1540481 := by norm_num
private theorem prime_seventySevenBW_1646357 : Nat.Prime 1646357 := by norm_num
private theorem prime_seventySevenBW_1652687 : Nat.Prime 1652687 := by norm_num
private theorem prime_seventySevenBW_1782709 : Nat.Prime 1782709 := by norm_num
private theorem prime_seventySevenBW_1790671 : Nat.Prime 1790671 := by norm_num
private theorem prime_seventySevenBW_1977329 : Nat.Prime 1977329 := by norm_num
private theorem prime_seventySevenBW_2229769 : Nat.Prime 2229769 := by norm_num
private theorem prime_seventySevenBW_2280433 : Nat.Prime 2280433 := by norm_num
private theorem prime_seventySevenBW_2290213 : Nat.Prime 2290213 := by norm_num
private theorem prime_seventySevenBW_2442943 : Nat.Prime 2442943 := by norm_num
private theorem prime_seventySevenBW_2447581 : Nat.Prime 2447581 := by norm_num
private theorem prime_seventySevenBW_2623141 : Nat.Prime 2623141 := by norm_num
private theorem prime_seventySevenBW_2635163 : Nat.Prime 2635163 := by norm_num
private theorem prime_seventySevenBW_2711327 : Nat.Prime 2711327 := by norm_num
private theorem prime_seventySevenBW_2723393 : Nat.Prime 2723393 := by norm_num
private theorem prime_seventySevenBW_3008569 : Nat.Prime 3008569 := by norm_num
private theorem prime_seventySevenBW_3065929 : Nat.Prime 3065929 := by norm_num
private theorem prime_seventySevenBW_3089557 : Nat.Prime 3089557 := by norm_num
private theorem prime_seventySevenBW_3118307 : Nat.Prime 3118307 := by norm_num
private theorem prime_seventySevenBW_3372907 : Nat.Prime 3372907 := by norm_num
private theorem prime_seventySevenBW_3557773 : Nat.Prime 3557773 := by norm_num
private theorem prime_seventySevenBW_3674947 : Nat.Prime 3674947 := by norm_num
private theorem prime_seventySevenBW_4017649 : Nat.Prime 4017649 := by norm_num
private theorem prime_seventySevenBW_4350673 : Nat.Prime 4350673 := by norm_num
private theorem prime_seventySevenBW_4932619 : Nat.Prime 4932619 := by norm_num
private theorem prime_seventySevenBW_5009327 : Nat.Prime 5009327 := by norm_num
private theorem prime_seventySevenBW_5049721 : Nat.Prime 5049721 := by norm_num
private theorem prime_seventySevenBW_5088887 : Nat.Prime 5088887 := by norm_num
private theorem prime_seventySevenBW_5543903 : Nat.Prime 5543903 := by norm_num
private theorem prime_seventySevenBW_5870549 : Nat.Prime 5870549 := by norm_num
private theorem prime_seventySevenBW_5938379 : Nat.Prime 5938379 := by norm_num
private theorem prime_seventySevenBW_5942971 : Nat.Prime 5942971 := by norm_num
private theorem prime_seventySevenBW_6116989 : Nat.Prime 6116989 := by norm_num
private theorem prime_seventySevenBW_7322779 : Nat.Prime 7322779 := by norm_num
private theorem prime_seventySevenBW_7391101 : Nat.Prime 7391101 := by norm_num
private theorem prime_seventySevenBW_8033791 : Nat.Prime 8033791 := by norm_num
private theorem prime_seventySevenBW_8678933 : Nat.Prime 8678933 := by norm_num
private theorem prime_seventySevenBW_8821243 : Nat.Prime 8821243 := by norm_num
private theorem prime_seventySevenBW_8908223 : Nat.Prime 8908223 := by norm_num
private theorem prime_seventySevenBW_8941553 : Nat.Prime 8941553 := by norm_num
private theorem prime_seventySevenBW_9004319 : Nat.Prime 9004319 := by norm_num
private theorem prime_seventySevenBW_9245491 : Nat.Prime 9245491 := by norm_num
private theorem prime_seventySevenBW_9621869 : Nat.Prime 9621869 := by norm_num
private theorem prime_seventySevenBW_9802867 : Nat.Prime 9802867 := by norm_num
private theorem prime_seventySevenBW_10099861 : Nat.Prime 10099861 := by norm_num
private theorem prime_seventySevenBW_10304353 : Nat.Prime 10304353 := by norm_num
private theorem prime_seventySevenBW_11321389 : Nat.Prime 11321389 := by norm_num
private theorem prime_seventySevenBW_12271219 : Nat.Prime 12271219 := by norm_num
private theorem prime_seventySevenBW_13448563 : Nat.Prime 13448563 := by norm_num
private theorem prime_seventySevenBW_14562271 : Nat.Prime 14562271 := by norm_num
private theorem prime_seventySevenBW_15397537 : Nat.Prime 15397537 := by norm_num
private theorem prime_seventySevenBW_16629889 : Nat.Prime 16629889 := by norm_num
private theorem prime_seventySevenBW_16828271 : Nat.Prime 16828271 := by norm_num
private theorem prime_seventySevenBW_17664359 : Nat.Prime 17664359 := by norm_num
private theorem prime_seventySevenBW_18597889 : Nat.Prime 18597889 := by norm_num
private theorem prime_seventySevenBW_18855517 : Nat.Prime 18855517 := by norm_num
private theorem prime_seventySevenBW_19124197 : Nat.Prime 19124197 := by norm_num
private theorem prime_seventySevenBW_19561459 : Nat.Prime 19561459 := by norm_num
private theorem prime_seventySevenBW_21670633 : Nat.Prime 21670633 := by norm_num
private theorem prime_seventySevenBW_24146963 : Nat.Prime 24146963 := by norm_num
private theorem prime_seventySevenBW_24308633 : Nat.Prime 24308633 := by norm_num
private theorem prime_seventySevenBW_27149501 : Nat.Prime 27149501 := by norm_num
private theorem prime_seventySevenBW_27952931 : Nat.Prime 27952931 := by norm_num
private theorem prime_seventySevenBW_30113113 : Nat.Prime 30113113 := by
  apply lucas_primality 30113113 (5 : ZMod 30113113)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (619, 1), (2027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (619, 1), (2027, 1)] : List FactorBlock).map factorBlockValue).prod) = 30113113 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_619
      · exact prime_seventySevenBW_2027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 30113113) ^ 15056556 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 30113113) ^ 10037704 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 30113113) ^ 48648 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 30113113) ^ 14856 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_31951291 : Nat.Prime 31951291 := by
  apply lucas_primality 31951291 (2 : ZMod 31951291)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (233, 1), (653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (233, 1), (653, 1)] : List FactorBlock).map factorBlockValue).prod) = 31951291 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_5
      · exact prime_seventySevenBW_7
      · exact prime_seventySevenBW_233
      · exact prime_seventySevenBW_653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 31951291) ^ 15975645 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 31951291) ^ 10650430 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 31951291) ^ 6390258 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 31951291) ^ 4564470 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 31951291) ^ 137130 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 31951291) ^ 48930 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_41610857 : Nat.Prime 41610857 := by
  apply lucas_primality 41610857 (3 : ZMod 41610857)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (239, 1), (3109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (239, 1), (3109, 1)] : List FactorBlock).map factorBlockValue).prod) = 41610857 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_7
      · exact prime_seventySevenBW_239
      · exact prime_seventySevenBW_3109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 41610857) ^ 20805428 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 41610857) ^ 5944408 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 41610857) ^ 174104 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 41610857) ^ 13384 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_43709251 : Nat.Prime 43709251 := by
  apply lucas_primality 43709251 (2 : ZMod 43709251)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 3), (13, 1), (4483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 3), (13, 1), (4483, 1)] : List FactorBlock).map factorBlockValue).prod) = 43709251 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_5
      · exact prime_seventySevenBW_13
      · exact prime_seventySevenBW_4483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 43709251) ^ 21854625 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 43709251) ^ 14569750 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 43709251) ^ 8741850 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 43709251) ^ 3362250 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 43709251) ^ 9750 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_45225283 : Nat.Prime 45225283 := by
  apply lucas_primality 45225283 (3 : ZMod 45225283)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (396713, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (396713, 1)] : List FactorBlock).map factorBlockValue).prod) = 45225283 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_19
      · exact prime_seventySevenBW_396713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 45225283) ^ 22612641 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 45225283) ^ 15075094 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 45225283) ^ 2380278 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 45225283) ^ 114 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_48757469 : Nat.Prime 48757469 := by
  apply lucas_primality 48757469 (2 : ZMod 48757469)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 1), (420323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 1), (420323, 1)] : List FactorBlock).map factorBlockValue).prod) = 48757469 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_29
      · exact prime_seventySevenBW_420323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 48757469) ^ 24378734 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 48757469) ^ 1681292 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 48757469) ^ 116 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_49576003 : Nat.Prime 49576003 := by
  apply lucas_primality 49576003 (3 : ZMod 49576003)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (1180381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (1180381, 1)] : List FactorBlock).map factorBlockValue).prod) = 49576003 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_7
      · exact prime_seventySevenBW_1180381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 49576003) ^ 24788001 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 49576003) ^ 16525334 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 49576003) ^ 7082286 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 49576003) ^ 42 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_50419757 : Nat.Prime 50419757 := by
  apply lucas_primality 50419757 (3 : ZMod 50419757)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (741467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (741467, 1)] : List FactorBlock).map factorBlockValue).prod) = 50419757 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_17
      · exact prime_seventySevenBW_741467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 50419757) ^ 25209878 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 50419757) ^ 2965868 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 50419757) ^ 68 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_54208039 : Nat.Prime 54208039 := by
  apply lucas_primality 54208039 (6 : ZMod 54208039)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1103, 1), (8191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1103, 1), (8191, 1)] : List FactorBlock).map factorBlockValue).prod) = 54208039 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_1103
      · exact prime_seventySevenBW_8191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 54208039) ^ 27104019 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (6 : ZMod 54208039) ^ 18069346 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (6 : ZMod 54208039) ^ 49146 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (6 : ZMod 54208039) ^ 6618 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_56924369 : Nat.Prime 56924369 := by
  apply lucas_primality 56924369 (3 : ZMod 56924369)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3557773, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3557773, 1)] : List FactorBlock).map factorBlockValue).prod) = 56924369 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3557773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 56924369) ^ 28462184 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 56924369) ^ 16 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_58630633 : Nat.Prime 58630633 := by
  apply lucas_primality 58630633 (5 : ZMod 58630633)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (2442943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (2442943, 1)] : List FactorBlock).map factorBlockValue).prod) = 58630633 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_2442943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 58630633) ^ 29315316 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 58630633) ^ 19543544 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 58630633) ^ 24 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_63858611 : Nat.Prime 63858611 := by
  apply lucas_primality 63858611 (2 : ZMod 63858611)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (181, 1), (35281, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (181, 1), (35281, 1)] : List FactorBlock).map factorBlockValue).prod) = 63858611 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_5
      · exact prime_seventySevenBW_181
      · exact prime_seventySevenBW_35281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 63858611) ^ 31929305 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 63858611) ^ 12771722 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 63858611) ^ 352810 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 63858611) ^ 1810 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_82128707 : Nat.Prime 82128707 := by
  apply lucas_primality 82128707 (2 : ZMod 82128707)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (107, 1), (139, 1), (251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (107, 1), (139, 1), (251, 1)] : List FactorBlock).map factorBlockValue).prod) = 82128707 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_11
      · exact prime_seventySevenBW_107
      · exact prime_seventySevenBW_139
      · exact prime_seventySevenBW_251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 82128707) ^ 41064353 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 82128707) ^ 7466246 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 82128707) ^ 767558 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 82128707) ^ 590854 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 82128707) ^ 327206 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_83222753 : Nat.Prime 83222753 := by
  apply lucas_primality 83222753 (3 : ZMod 83222753)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (17, 2), (8999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (17, 2), (8999, 1)] : List FactorBlock).map factorBlockValue).prod) = 83222753 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_17
      · exact prime_seventySevenBW_8999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 83222753) ^ 41611376 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 83222753) ^ 4895456 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 83222753) ^ 9248 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_87349037 : Nat.Prime 87349037 := by
  apply lucas_primality 87349037 (2 : ZMod 87349037)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (79, 2), (3499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (79, 2), (3499, 1)] : List FactorBlock).map factorBlockValue).prod) = 87349037 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_79
      · exact prime_seventySevenBW_3499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 87349037) ^ 43674518 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 87349037) ^ 1105684 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 87349037) ^ 24964 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_87498001 : Nat.Prime 87498001 := by
  apply lucas_primality 87498001 (13 : ZMod 87498001)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5, 3), (4861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5, 3), (4861, 1)] : List FactorBlock).map factorBlockValue).prod) = 87498001 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_5
      · exact prime_seventySevenBW_4861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 87498001) ^ 43749000 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (13 : ZMod 87498001) ^ 29166000 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (13 : ZMod 87498001) ^ 17499600 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (13 : ZMod 87498001) ^ 18000 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_101544217 : Nat.Prime 101544217 := by
  apply lucas_primality 101544217 (7 : ZMod 101544217)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (857, 1), (4937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (857, 1), (4937, 1)] : List FactorBlock).map factorBlockValue).prod) = 101544217 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_857
      · exact prime_seventySevenBW_4937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 101544217) ^ 50772108 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (7 : ZMod 101544217) ^ 33848072 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (7 : ZMod 101544217) ^ 118488 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (7 : ZMod 101544217) ^ 20568 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_117476497 : Nat.Prime 117476497 := by
  apply lucas_primality 117476497 (5 : ZMod 117476497)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (815809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (815809, 1)] : List FactorBlock).map factorBlockValue).prod) = 117476497 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_815809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 117476497) ^ 58738248 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 117476497) ^ 39158832 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 117476497) ^ 144 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_121064557 : Nat.Prime 121064557 := by
  apply lucas_primality 121064557 (22 : ZMod 121064557)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (109, 1), (92557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (109, 1), (92557, 1)] : List FactorBlock).map factorBlockValue).prod) = 121064557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_109
      · exact prime_seventySevenBW_92557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (22 : ZMod 121064557) ^ 60532278 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (22 : ZMod 121064557) ^ 40354852 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (22 : ZMod 121064557) ^ 1110684 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (22 : ZMod 121064557) ^ 1308 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_147648317 : Nat.Prime 147648317 := by
  apply lucas_primality 147648317 (3 : ZMod 147648317)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (23, 1), (84467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (23, 1), (84467, 1)] : List FactorBlock).map factorBlockValue).prod) = 147648317 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_19
      · exact prime_seventySevenBW_23
      · exact prime_seventySevenBW_84467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 147648317) ^ 73824158 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 147648317) ^ 7770964 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 147648317) ^ 6419492 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 147648317) ^ 1748 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_159621013 : Nat.Prime 159621013 := by
  apply lucas_primality 159621013 (2 : ZMod 159621013)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (23, 1), (263, 1), (733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (23, 1), (263, 1), (733, 1)] : List FactorBlock).map factorBlockValue).prod) = 159621013 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_23
      · exact prime_seventySevenBW_263
      · exact prime_seventySevenBW_733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 159621013) ^ 79810506 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 159621013) ^ 53207004 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 159621013) ^ 6940044 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 159621013) ^ 606924 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 159621013) ^ 217764 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_178141801 : Nat.Prime 178141801 := by
  apply lucas_primality 178141801 (7 : ZMod 178141801)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 2), (367, 1), (809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 2), (367, 1), (809, 1)] : List FactorBlock).map factorBlockValue).prod) = 178141801 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_5
      · exact prime_seventySevenBW_367
      · exact prime_seventySevenBW_809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 178141801) ^ 89070900 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (7 : ZMod 178141801) ^ 59380600 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (7 : ZMod 178141801) ^ 35628360 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (7 : ZMod 178141801) ^ 485400 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (7 : ZMod 178141801) ^ 220200 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_178831061 : Nat.Prime 178831061 := by
  apply lucas_primality 178831061 (2 : ZMod 178831061)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (8941553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (8941553, 1)] : List FactorBlock).map factorBlockValue).prod) = 178831061 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_5
      · exact prime_seventySevenBW_8941553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 178831061) ^ 89415530 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 178831061) ^ 35766212 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 178831061) ^ 20 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_187857569 : Nat.Prime 187857569 := by
  apply lucas_primality 187857569 (3 : ZMod 187857569)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5870549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5870549, 1)] : List FactorBlock).map factorBlockValue).prod) = 187857569 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_5870549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 187857569) ^ 93928784 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 187857569) ^ 32 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_198304013 : Nat.Prime 198304013 := by
  apply lucas_primality 198304013 (2 : ZMod 198304013)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (49576003, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (49576003, 1)] : List FactorBlock).map factorBlockValue).prod) = 198304013 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_49576003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 198304013) ^ 99152006 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 198304013) ^ 4 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_227741851 : Nat.Prime 227741851 := by
  apply lucas_primality 227741851 (2 : ZMod 227741851)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (7, 1), (197, 1), (367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (7, 1), (197, 1), (367, 1)] : List FactorBlock).map factorBlockValue).prod) = 227741851 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_5
      · exact prime_seventySevenBW_7
      · exact prime_seventySevenBW_197
      · exact prime_seventySevenBW_367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 227741851) ^ 113870925 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 227741851) ^ 75913950 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 227741851) ^ 45548370 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 227741851) ^ 32534550 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 227741851) ^ 1156050 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 227741851) ^ 620550 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_245817641 : Nat.Prime 245817641 := by
  apply lucas_primality 245817641 (3 : ZMod 245817641)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (37, 2), (67, 2)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (37, 2), (67, 2)] : List FactorBlock).map factorBlockValue).prod) = 245817641 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_5
      · exact prime_seventySevenBW_37
      · exact prime_seventySevenBW_67
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 245817641) ^ 122908820 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 245817641) ^ 49163528 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 245817641) ^ 6643720 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 245817641) ^ 3668920 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_261007429 : Nat.Prime 261007429 := by
  apply lucas_primality 261007429 (6 : ZMod 261007429)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (1977329, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (1977329, 1)] : List FactorBlock).map factorBlockValue).prod) = 261007429 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_11
      · exact prime_seventySevenBW_1977329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 261007429) ^ 130503714 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (6 : ZMod 261007429) ^ 87002476 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (6 : ZMod 261007429) ^ 23727948 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (6 : ZMod 261007429) ^ 132 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_262255507 : Nat.Prime 262255507 := by
  apply lucas_primality 262255507 (2 : ZMod 262255507)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (43709251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (43709251, 1)] : List FactorBlock).map factorBlockValue).prod) = 262255507 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_43709251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 262255507) ^ 131127753 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 262255507) ^ 87418502 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 262255507) ^ 6 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_277827019 : Nat.Prime 277827019 := by
  apply lucas_primality 277827019 (2 : ZMod 277827019)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (29, 1), (307, 1), (743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (29, 1), (307, 1), (743, 1)] : List FactorBlock).map factorBlockValue).prod) = 277827019 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_7
      · exact prime_seventySevenBW_29
      · exact prime_seventySevenBW_307
      · exact prime_seventySevenBW_743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 277827019) ^ 138913509 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 277827019) ^ 92609006 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 277827019) ^ 39689574 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 277827019) ^ 9580242 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 277827019) ^ 904974 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 277827019) ^ 373926 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_295494191 : Nat.Prime 295494191 := by
  apply lucas_primality 295494191 (13 : ZMod 295494191)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (71, 1), (191, 1), (2179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (71, 1), (191, 1), (2179, 1)] : List FactorBlock).map factorBlockValue).prod) = 295494191 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_5
      · exact prime_seventySevenBW_71
      · exact prime_seventySevenBW_191
      · exact prime_seventySevenBW_2179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 295494191) ^ 147747095 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (13 : ZMod 295494191) ^ 59098838 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (13 : ZMod 295494191) ^ 4161890 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (13 : ZMod 295494191) ^ 1547090 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (13 : ZMod 295494191) ^ 135610 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_309539023 : Nat.Prime 309539023 := by
  apply lucas_primality 309539023 (5 : ZMod 309539023)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (1933, 1), (2053, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (1933, 1), (2053, 1)] : List FactorBlock).map factorBlockValue).prod) = 309539023 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_13
      · exact prime_seventySevenBW_1933
      · exact prime_seventySevenBW_2053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 309539023) ^ 154769511 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 309539023) ^ 103179674 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 309539023) ^ 23810694 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 309539023) ^ 160134 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 309539023) ^ 150774 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_340634237 : Nat.Prime 340634237 := by
  apply lucas_primality 340634237 (2 : ZMod 340634237)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (5009327, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (5009327, 1)] : List FactorBlock).map factorBlockValue).prod) = 340634237 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_17
      · exact prime_seventySevenBW_5009327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 340634237) ^ 170317118 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 340634237) ^ 20037308 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 340634237) ^ 68 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_380066353 : Nat.Prime 380066353 := by
  apply lucas_primality 380066353 (10 : ZMod 380066353)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (23, 1), (344263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (23, 1), (344263, 1)] : List FactorBlock).map factorBlockValue).prod) = 380066353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_23
      · exact prime_seventySevenBW_344263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 380066353) ^ 190033176 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (10 : ZMod 380066353) ^ 126688784 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (10 : ZMod 380066353) ^ 16524624 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (10 : ZMod 380066353) ^ 1104 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_527954477 : Nat.Prime 527954477 := by
  apply lucas_primality 527954477 (2 : ZMod 527954477)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (18855517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (18855517, 1)] : List FactorBlock).map factorBlockValue).prod) = 527954477 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_7
      · exact prime_seventySevenBW_18855517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 527954477) ^ 263977238 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 527954477) ^ 75422068 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 527954477) ^ 28 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_528997561 : Nat.Prime 528997561 := by
  apply lucas_primality 528997561 (46 : ZMod 528997561)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (7, 1), (13, 1), (193, 1), (251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (7, 1), (13, 1), (193, 1), (251, 1)] : List FactorBlock).map factorBlockValue).prod) = 528997561 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_5
      · exact prime_seventySevenBW_7
      · exact prime_seventySevenBW_13
      · exact prime_seventySevenBW_193
      · exact prime_seventySevenBW_251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (46 : ZMod 528997561) ^ 264498780 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (46 : ZMod 528997561) ^ 176332520 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (46 : ZMod 528997561) ^ 105799512 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (46 : ZMod 528997561) ^ 75571080 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (46 : ZMod 528997561) ^ 40692120 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (46 : ZMod 528997561) ^ 2740920 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (46 : ZMod 528997561) ^ 2107560 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_575012969 : Nat.Prime 575012969 := by
  apply lucas_primality 575012969 (3 : ZMod 575012969)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (239, 1), (300739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (239, 1), (300739, 1)] : List FactorBlock).map factorBlockValue).prod) = 575012969 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_239
      · exact prime_seventySevenBW_300739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 575012969) ^ 287506484 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 575012969) ^ 2405912 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 575012969) ^ 1912 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_631554379 : Nat.Prime 631554379 := by
  apply lucas_primality 631554379 (7 : ZMod 631554379)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (13, 1), (23, 1), (50291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (13, 1), (23, 1), (50291, 1)] : List FactorBlock).map factorBlockValue).prod) = 631554379 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_7
      · exact prime_seventySevenBW_13
      · exact prime_seventySevenBW_23
      · exact prime_seventySevenBW_50291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 631554379) ^ 315777189 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (7 : ZMod 631554379) ^ 210518126 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (7 : ZMod 631554379) ^ 90222054 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (7 : ZMod 631554379) ^ 48581106 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (7 : ZMod 631554379) ^ 27458886 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (7 : ZMod 631554379) ^ 12558 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_721148299 : Nat.Prime 721148299 := by
  apply lucas_primality 721148299 (2 : ZMod 721148299)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (9245491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (9245491, 1)] : List FactorBlock).map factorBlockValue).prod) = 721148299 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_13
      · exact prime_seventySevenBW_9245491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 721148299) ^ 360574149 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 721148299) ^ 240382766 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 721148299) ^ 55472946 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 721148299) ^ 78 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_741017113 : Nat.Prime 741017113 := by
  apply lucas_primality 741017113 (5 : ZMod 741017113)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (347, 1), (8089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (347, 1), (8089, 1)] : List FactorBlock).map factorBlockValue).prod) = 741017113 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_11
      · exact prime_seventySevenBW_347
      · exact prime_seventySevenBW_8089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 741017113) ^ 370508556 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 741017113) ^ 247005704 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 741017113) ^ 67365192 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 741017113) ^ 2135496 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 741017113) ^ 91608 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_774071927 : Nat.Prime 774071927 := by
  apply lucas_primality 774071927 (5 : ZMod 774071927)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (131, 1), (811, 1), (3643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (131, 1), (811, 1), (3643, 1)] : List FactorBlock).map factorBlockValue).prod) = 774071927 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_131
      · exact prime_seventySevenBW_811
      · exact prime_seventySevenBW_3643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 774071927) ^ 387035963 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 774071927) ^ 5908946 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 774071927) ^ 954466 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 774071927) ^ 212482 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_877577531 : Nat.Prime 877577531 := by
  apply lucas_primality 877577531 (6 : ZMod 877577531)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (41, 1), (73, 1), (109, 1), (269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (41, 1), (73, 1), (109, 1), (269, 1)] : List FactorBlock).map factorBlockValue).prod) = 877577531 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_5
      · exact prime_seventySevenBW_41
      · exact prime_seventySevenBW_73
      · exact prime_seventySevenBW_109
      · exact prime_seventySevenBW_269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 877577531) ^ 438788765 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (6 : ZMod 877577531) ^ 175515506 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (6 : ZMod 877577531) ^ 21404330 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (6 : ZMod 877577531) ^ 12021610 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (6 : ZMod 877577531) ^ 8051170 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (6 : ZMod 877577531) ^ 3262370 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_915499391 : Nat.Prime 915499391 := by
  apply lucas_primality 915499391 (11 : ZMod 915499391)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (67, 1), (89, 1), (1181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (67, 1), (89, 1), (1181, 1)] : List FactorBlock).map factorBlockValue).prod) = 915499391 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_5
      · exact prime_seventySevenBW_13
      · exact prime_seventySevenBW_67
      · exact prime_seventySevenBW_89
      · exact prime_seventySevenBW_1181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 915499391) ^ 457749695 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (11 : ZMod 915499391) ^ 183099878 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (11 : ZMod 915499391) ^ 70423030 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (11 : ZMod 915499391) ^ 13664170 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (11 : ZMod 915499391) ^ 10286510 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (11 : ZMod 915499391) ^ 775190 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_925533121 : Nat.Prime 925533121 := by
  apply lucas_primality 925533121 (13 : ZMod 925533121)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (5, 1), (964097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (5, 1), (964097, 1)] : List FactorBlock).map factorBlockValue).prod) = 925533121 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_5
      · exact prime_seventySevenBW_964097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 925533121) ^ 462766560 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (13 : ZMod 925533121) ^ 308511040 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (13 : ZMod 925533121) ^ 185106624 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (13 : ZMod 925533121) ^ 960 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_994268789 : Nat.Prime 994268789 := by
  apply lucas_primality 994268789 (2 : ZMod 994268789)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (109, 1), (2280433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (109, 1), (2280433, 1)] : List FactorBlock).map factorBlockValue).prod) = 994268789 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_109
      · exact prime_seventySevenBW_2280433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 994268789) ^ 497134394 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 994268789) ^ 9121732 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 994268789) ^ 436 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_1033971221 : Nat.Prime 1033971221 := by
  apply lucas_primality 1033971221 (2 : ZMod 1033971221)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (29, 1), (1782709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (29, 1), (1782709, 1)] : List FactorBlock).map factorBlockValue).prod) = 1033971221 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_5
      · exact prime_seventySevenBW_29
      · exact prime_seventySevenBW_1782709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1033971221) ^ 516985610 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1033971221) ^ 206794244 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1033971221) ^ 35654180 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1033971221) ^ 580 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_1071522341 : Nat.Prime 1071522341 := by
  apply lucas_primality 1071522341 (10 : ZMod 1071522341)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (61, 1), (125471, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (61, 1), (125471, 1)] : List FactorBlock).map factorBlockValue).prod) = 1071522341 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_5
      · exact prime_seventySevenBW_7
      · exact prime_seventySevenBW_61
      · exact prime_seventySevenBW_125471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 1071522341) ^ 535761170 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (10 : ZMod 1071522341) ^ 214304468 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (10 : ZMod 1071522341) ^ 153074620 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (10 : ZMod 1071522341) ^ 17565940 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (10 : ZMod 1071522341) ^ 8540 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_1072986367 : Nat.Prime 1072986367 := by
  apply lucas_primality 1072986367 (3 : ZMod 1072986367)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (178831061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (178831061, 1)] : List FactorBlock).map factorBlockValue).prod) = 1072986367 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_178831061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1072986367) ^ 536493183 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 1072986367) ^ 357662122 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 1072986367) ^ 6 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_1179865987 : Nat.Prime 1179865987 := by
  apply lucas_primality 1179865987 (2 : ZMod 1179865987)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (29, 1), (521603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (29, 1), (521603, 1)] : List FactorBlock).map factorBlockValue).prod) = 1179865987 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_13
      · exact prime_seventySevenBW_29
      · exact prime_seventySevenBW_521603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1179865987) ^ 589932993 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1179865987) ^ 393288662 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1179865987) ^ 90758922 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1179865987) ^ 40685034 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1179865987) ^ 2262 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_1201007887 : Nat.Prime 1201007887 := by
  apply lucas_primality 1201007887 (5 : ZMod 1201007887)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (15397537, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (15397537, 1)] : List FactorBlock).map factorBlockValue).prod) = 1201007887 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_13
      · exact prime_seventySevenBW_15397537
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1201007887) ^ 600503943 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 1201007887) ^ 400335962 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 1201007887) ^ 92385222 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 1201007887) ^ 78 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_1300992937 : Nat.Prime 1300992937 := by
  apply lucas_primality 1300992937 (7 : ZMod 1300992937)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (54208039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (54208039, 1)] : List FactorBlock).map factorBlockValue).prod) = 1300992937 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_54208039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 1300992937) ^ 650496468 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (7 : ZMod 1300992937) ^ 433664312 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (7 : ZMod 1300992937) ^ 24 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_1617899033 : Nat.Prime 1617899033 := by
  apply lucas_primality 1617899033 (3 : ZMod 1617899033)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (41, 1), (4932619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (41, 1), (4932619, 1)] : List FactorBlock).map factorBlockValue).prod) = 1617899033 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_41
      · exact prime_seventySevenBW_4932619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1617899033) ^ 808949516 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 1617899033) ^ 39460952 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 1617899033) ^ 328 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_1899672937 : Nat.Prime 1899672937 := by
  apply lucas_primality 1899672937 (5 : ZMod 1899672937)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (1471, 1), (7687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (1471, 1), (7687, 1)] : List FactorBlock).map factorBlockValue).prod) = 1899672937 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_7
      · exact prime_seventySevenBW_1471
      · exact prime_seventySevenBW_7687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1899672937) ^ 949836468 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 1899672937) ^ 633224312 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 1899672937) ^ 271381848 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 1899672937) ^ 1291416 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 1899672937) ^ 247128 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_2007593389 : Nat.Prime 2007593389 := by
  apply lucas_primality 2007593389 (2 : ZMod 2007593389)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (941, 1), (59263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (941, 1), (59263, 1)] : List FactorBlock).map factorBlockValue).prod) = 2007593389 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_941
      · exact prime_seventySevenBW_59263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2007593389) ^ 1003796694 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2007593389) ^ 669197796 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2007593389) ^ 2133468 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2007593389) ^ 33876 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_2033761157 : Nat.Prime 2033761157 := by
  apply lucas_primality 2033761157 (3 : ZMod 2033761157)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (53, 1), (1370459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (53, 1), (1370459, 1)] : List FactorBlock).map factorBlockValue).prod) = 2033761157 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_7
      · exact prime_seventySevenBW_53
      · exact prime_seventySevenBW_1370459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2033761157) ^ 1016880578 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 2033761157) ^ 290537308 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 2033761157) ^ 38372852 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 2033761157) ^ 1484 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_2524098509 : Nat.Prime 2524098509 := by
  apply lucas_primality 2524098509 (2 : ZMod 2524098509)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (283, 1), (2229769, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (283, 1), (2229769, 1)] : List FactorBlock).map factorBlockValue).prod) = 2524098509 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_283
      · exact prime_seventySevenBW_2229769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2524098509) ^ 1262049254 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2524098509) ^ 8919076 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2524098509) ^ 1132 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_2996320267 : Nat.Prime 2996320267 := by
  apply lucas_primality 2996320267 (37 : ZMod 2996320267)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (67, 1), (977, 1), (2543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (67, 1), (977, 1), (2543, 1)] : List FactorBlock).map factorBlockValue).prod) = 2996320267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_67
      · exact prime_seventySevenBW_977
      · exact prime_seventySevenBW_2543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (37 : ZMod 2996320267) ^ 1498160133 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (37 : ZMod 2996320267) ^ 998773422 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (37 : ZMod 2996320267) ^ 44721198 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (37 : ZMod 2996320267) ^ 3066858 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (37 : ZMod 2996320267) ^ 1178262 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_3083926231 : Nat.Prime 3083926231 := by
  apply lucas_primality 3083926231 (3 : ZMod 3083926231)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (7, 2), (11, 1), (21191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (7, 2), (11, 1), (21191, 1)] : List FactorBlock).map factorBlockValue).prod) = 3083926231 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_5
      · exact prime_seventySevenBW_7
      · exact prime_seventySevenBW_11
      · exact prime_seventySevenBW_21191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3083926231) ^ 1541963115 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 3083926231) ^ 1027975410 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 3083926231) ^ 616785246 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 3083926231) ^ 440560890 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 3083926231) ^ 280356930 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 3083926231) ^ 145530 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_3515451557 : Nat.Prime 3515451557 := by
  apply lucas_primality 3515451557 (2 : ZMod 3515451557)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (1553, 1), (33289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (1553, 1), (33289, 1)] : List FactorBlock).map factorBlockValue).prod) = 3515451557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_17
      · exact prime_seventySevenBW_1553
      · exact prime_seventySevenBW_33289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3515451557) ^ 1757725778 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 3515451557) ^ 206791268 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 3515451557) ^ 2263652 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 3515451557) ^ 105604 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_3633710693 : Nat.Prime 3633710693 := by
  apply lucas_primality 3633710693 (2 : ZMod 3633710693)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1259, 1), (721547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1259, 1), (721547, 1)] : List FactorBlock).map factorBlockValue).prod) = 3633710693 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_1259
      · exact prime_seventySevenBW_721547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3633710693) ^ 1816855346 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 3633710693) ^ 2886188 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 3633710693) ^ 5036 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_3926552057 : Nat.Prime 3926552057 := by
  apply lucas_primality 3926552057 (3 : ZMod 3926552057)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (151, 1), (464351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (151, 1), (464351, 1)] : List FactorBlock).map factorBlockValue).prod) = 3926552057 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_7
      · exact prime_seventySevenBW_151
      · exact prime_seventySevenBW_464351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3926552057) ^ 1963276028 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 3926552057) ^ 560936008 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 3926552057) ^ 26003656 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 3926552057) ^ 8456 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_4302177917 : Nat.Prime 4302177917 := by
  apply lucas_primality 4302177917 (2 : ZMod 4302177917)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1861, 1), (577939, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1861, 1), (577939, 1)] : List FactorBlock).map factorBlockValue).prod) = 4302177917 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_1861
      · exact prime_seventySevenBW_577939
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4302177917) ^ 2151088958 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 4302177917) ^ 2311756 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 4302177917) ^ 7444 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_4314710249 : Nat.Prime 4314710249 := by
  apply lucas_primality 4314710249 (3 : ZMod 4314710249)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (29, 1), (18597889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (29, 1), (18597889, 1)] : List FactorBlock).map factorBlockValue).prod) = 4314710249 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_29
      · exact prime_seventySevenBW_18597889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 4314710249) ^ 2157355124 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 4314710249) ^ 148783112 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 4314710249) ^ 232 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_4521410119 : Nat.Prime 4521410119 := by
  apply lucas_primality 4521410119 (3 : ZMod 4521410119)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 5), (379, 1), (24547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 5), (379, 1), (24547, 1)] : List FactorBlock).map factorBlockValue).prod) = 4521410119 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_379
      · exact prime_seventySevenBW_24547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4521410119) ^ 2260705059 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 4521410119) ^ 1507136706 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 4521410119) ^ 11929842 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 4521410119) ^ 184194 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_4974463961 : Nat.Prime 4974463961 := by
  apply lucas_primality 4974463961 (3 : ZMod 4974463961)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (29, 1), (1531, 1), (2801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (29, 1), (1531, 1), (2801, 1)] : List FactorBlock).map factorBlockValue).prod) = 4974463961 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_5
      · exact prime_seventySevenBW_29
      · exact prime_seventySevenBW_1531
      · exact prime_seventySevenBW_2801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4974463961) ^ 2487231980 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 4974463961) ^ 994892792 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 4974463961) ^ 171533240 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 4974463961) ^ 3249160 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 4974463961) ^ 1775960 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_5159810687 : Nat.Prime 5159810687 := by
  apply lucas_primality 5159810687 (5 : ZMod 5159810687)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (83222753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (83222753, 1)] : List FactorBlock).map factorBlockValue).prod) = 5159810687 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_31
      · exact prime_seventySevenBW_83222753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 5159810687) ^ 2579905343 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 5159810687) ^ 166445506 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 5159810687) ^ 62 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_5540648219 : Nat.Prime 5540648219 := by
  apply lucas_primality 5540648219 (2 : ZMod 5540648219)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (179, 1), (821, 1), (2693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (179, 1), (821, 1), (2693, 1)] : List FactorBlock).map factorBlockValue).prod) = 5540648219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_7
      · exact prime_seventySevenBW_179
      · exact prime_seventySevenBW_821
      · exact prime_seventySevenBW_2693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5540648219) ^ 2770324109 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 5540648219) ^ 791521174 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 5540648219) ^ 30953342 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 5540648219) ^ 6748658 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 5540648219) ^ 2057426 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_6463828739 : Nat.Prime 6463828739 := by
  apply lucas_primality 6463828739 (2 : ZMod 6463828739)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (87349037, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (87349037, 1)] : List FactorBlock).map factorBlockValue).prod) = 6463828739 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_37
      · exact prime_seventySevenBW_87349037
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 6463828739) ^ 3231914369 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 6463828739) ^ 174698074 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 6463828739) ^ 74 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_6640001971 : Nat.Prime 6640001971 := by
  apply lucas_primality 6640001971 (3 : ZMod 6640001971)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (227, 1), (139291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (227, 1), (139291, 1)] : List FactorBlock).map factorBlockValue).prod) = 6640001971 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_5
      · exact prime_seventySevenBW_7
      · exact prime_seventySevenBW_227
      · exact prime_seventySevenBW_139291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 6640001971) ^ 3320000985 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 6640001971) ^ 2213333990 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 6640001971) ^ 1328000394 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 6640001971) ^ 948571710 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 6640001971) ^ 29251110 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 6640001971) ^ 47670 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_7381410293 : Nat.Prime 7381410293 := by
  apply lucas_primality 7381410293 (2 : ZMod 7381410293)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (9497, 1), (194309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (9497, 1), (194309, 1)] : List FactorBlock).map factorBlockValue).prod) = 7381410293 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_9497
      · exact prime_seventySevenBW_194309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 7381410293) ^ 3690705146 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 7381410293) ^ 777236 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 7381410293) ^ 37988 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_7531919957 : Nat.Prime 7531919957 := by
  apply lucas_primality 7531919957 (2 : ZMod 7531919957)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (193, 1), (199, 1), (4457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (193, 1), (199, 1), (4457, 1)] : List FactorBlock).map factorBlockValue).prod) = 7531919957 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_11
      · exact prime_seventySevenBW_193
      · exact prime_seventySevenBW_199
      · exact prime_seventySevenBW_4457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7531919957) ^ 3765959978 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 7531919957) ^ 684719996 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 7531919957) ^ 39025492 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 7531919957) ^ 37848844 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 7531919957) ^ 1689908 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_8422374953 : Nat.Prime 8422374953 := by
  apply lucas_primality 8422374953 (3 : ZMod 8422374953)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17231, 1), (61099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17231, 1), (61099, 1)] : List FactorBlock).map factorBlockValue).prod) = 8422374953 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_17231
      · exact prime_seventySevenBW_61099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 8422374953) ^ 4211187476 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 8422374953) ^ 488792 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 8422374953) ^ 137848 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_10369458277 : Nat.Prime 10369458277 := by
  apply lucas_primality 10369458277 (2 : ZMod 10369458277)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (23, 1), (569, 1), (66029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (23, 1), (569, 1), (66029, 1)] : List FactorBlock).map factorBlockValue).prod) = 10369458277 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_23
      · exact prime_seventySevenBW_569
      · exact prime_seventySevenBW_66029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 10369458277) ^ 5184729138 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 10369458277) ^ 3456486092 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 10369458277) ^ 450846012 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 10369458277) ^ 18224004 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 10369458277) ^ 157044 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_10555699087 : Nat.Prime 10555699087 := by
  apply lucas_primality 10555699087 (3 : ZMod 10555699087)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (59, 1), (199, 1), (16649, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (59, 1), (199, 1), (16649, 1)] : List FactorBlock).map factorBlockValue).prod) = 10555699087 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_59
      · exact prime_seventySevenBW_199
      · exact prime_seventySevenBW_16649
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 10555699087) ^ 5277849543 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 10555699087) ^ 3518566362 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 10555699087) ^ 178910154 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 10555699087) ^ 53043714 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 10555699087) ^ 634014 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_12027188227 : Nat.Prime 12027188227 := by
  apply lucas_primality 12027188227 (2 : ZMod 12027188227)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (139, 1), (881, 1), (16369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (139, 1), (881, 1), (16369, 1)] : List FactorBlock).map factorBlockValue).prod) = 12027188227 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_139
      · exact prime_seventySevenBW_881
      · exact prime_seventySevenBW_16369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 12027188227) ^ 6013594113 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 12027188227) ^ 4009062742 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 12027188227) ^ 86526534 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 12027188227) ^ 13651746 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 12027188227) ^ 734754 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_13040167291 : Nat.Prime 13040167291 := by
  apply lucas_primality 13040167291 (2 : ZMod 13040167291)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (2141, 1), (203023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (2141, 1), (203023, 1)] : List FactorBlock).map factorBlockValue).prod) = 13040167291 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_5
      · exact prime_seventySevenBW_2141
      · exact prime_seventySevenBW_203023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 13040167291) ^ 6520083645 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 13040167291) ^ 4346722430 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 13040167291) ^ 2608033458 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 13040167291) ^ 6090690 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 13040167291) ^ 64230 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_14719197137 : Nat.Prime 14719197137 := by
  apply lucas_primality 14719197137 (3 : ZMod 14719197137)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (157, 1), (837079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (157, 1), (837079, 1)] : List FactorBlock).map factorBlockValue).prod) = 14719197137 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_7
      · exact prime_seventySevenBW_157
      · exact prime_seventySevenBW_837079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 14719197137) ^ 7359598568 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 14719197137) ^ 2102742448 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 14719197137) ^ 93752848 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 14719197137) ^ 17584 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_15309637813 : Nat.Prime 15309637813 := by
  apply lucas_primality 15309637813 (5 : ZMod 15309637813)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 2), (8678933, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 2), (8678933, 1)] : List FactorBlock).map factorBlockValue).prod) = 15309637813 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_7
      · exact prime_seventySevenBW_8678933
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 15309637813) ^ 7654818906 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 15309637813) ^ 5103212604 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 15309637813) ^ 2187091116 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 15309637813) ^ 1764 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_15360165901 : Nat.Prime 15360165901 := by
  apply lucas_primality 15360165901 (6 : ZMod 15360165901)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 2), (23, 1), (742037, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 2), (23, 1), (742037, 1)] : List FactorBlock).map factorBlockValue).prod) = 15360165901 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_5
      · exact prime_seventySevenBW_23
      · exact prime_seventySevenBW_742037
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 15360165901) ^ 7680082950 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (6 : ZMod 15360165901) ^ 5120055300 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (6 : ZMod 15360165901) ^ 3072033180 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (6 : ZMod 15360165901) ^ 667833300 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (6 : ZMod 15360165901) ^ 20700 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_22625114321 : Nat.Prime 22625114321 := by
  apply lucas_primality 22625114321 (3 : ZMod 22625114321)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (7643, 1), (37003, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (7643, 1), (37003, 1)] : List FactorBlock).map factorBlockValue).prod) = 22625114321 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_5
      · exact prime_seventySevenBW_7643
      · exact prime_seventySevenBW_37003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 22625114321) ^ 11312557160 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 22625114321) ^ 4525022864 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 22625114321) ^ 2960240 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 22625114321) ^ 611440 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_28509089699 : Nat.Prime 28509089699 := by
  apply lucas_primality 28509089699 (2 : ZMod 28509089699)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 1), (173, 1), (241, 1), (7951, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 1), (173, 1), (241, 1), (7951, 1)] : List FactorBlock).map factorBlockValue).prod) = 28509089699 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_43
      · exact prime_seventySevenBW_173
      · exact prime_seventySevenBW_241
      · exact prime_seventySevenBW_7951
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 28509089699) ^ 14254544849 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 28509089699) ^ 663002086 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 28509089699) ^ 164792426 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 28509089699) ^ 118294978 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 28509089699) ^ 3585598 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_30665110087 : Nat.Prime 30665110087 := by
  apply lucas_primality 30665110087 (6 : ZMod 30665110087)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (13, 1), (877, 1), (16603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (13, 1), (877, 1), (16603, 1)] : List FactorBlock).map factorBlockValue).prod) = 30665110087 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_13
      · exact prime_seventySevenBW_877
      · exact prime_seventySevenBW_16603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 30665110087) ^ 15332555043 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (6 : ZMod 30665110087) ^ 10221703362 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (6 : ZMod 30665110087) ^ 2358854622 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (6 : ZMod 30665110087) ^ 34965918 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (6 : ZMod 30665110087) ^ 1846962 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_31267755317 : Nat.Prime 31267755317 := by
  apply lucas_primality 31267755317 (2 : ZMod 31267755317)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (37, 1), (5021, 1), (6011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (37, 1), (5021, 1), (6011, 1)] : List FactorBlock).map factorBlockValue).prod) = 31267755317 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_7
      · exact prime_seventySevenBW_37
      · exact prime_seventySevenBW_5021
      · exact prime_seventySevenBW_6011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 31267755317) ^ 15633877658 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 31267755317) ^ 4466822188 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 31267755317) ^ 845074468 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 31267755317) ^ 6227396 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 31267755317) ^ 5201756 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_33467690719 : Nat.Prime 33467690719 := by
  apply lucas_primality 33467690719 (7 : ZMod 33467690719)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (11, 1), (24146963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (11, 1), (24146963, 1)] : List FactorBlock).map factorBlockValue).prod) = 33467690719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_7
      · exact prime_seventySevenBW_11
      · exact prime_seventySevenBW_24146963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 33467690719) ^ 16733845359 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (7 : ZMod 33467690719) ^ 11155896906 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (7 : ZMod 33467690719) ^ 4781098674 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (7 : ZMod 33467690719) ^ 3042517338 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (7 : ZMod 33467690719) ^ 1386 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_37084505573 : Nat.Prime 37084505573 := by
  apply lucas_primality 37084505573 (2 : ZMod 37084505573)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1051, 1), (8821243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1051, 1), (8821243, 1)] : List FactorBlock).map factorBlockValue).prod) = 37084505573 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_1051
      · exact prime_seventySevenBW_8821243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 37084505573) ^ 18542252786 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 37084505573) ^ 35284972 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 37084505573) ^ 4204 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_41519583631 : Nat.Prime 41519583631 := by
  apply lucas_primality 41519583631 (3 : ZMod 41519583631)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 1), (151, 1), (241, 1), (1811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 1), (151, 1), (241, 1), (1811, 1)] : List FactorBlock).map factorBlockValue).prod) = 41519583631 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_5
      · exact prime_seventySevenBW_7
      · exact prime_seventySevenBW_151
      · exact prime_seventySevenBW_241
      · exact prime_seventySevenBW_1811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 41519583631) ^ 20759791815 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 41519583631) ^ 13839861210 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 41519583631) ^ 8303916726 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 41519583631) ^ 5931369090 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 41519583631) ^ 274964130 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 41519583631) ^ 172280430 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 41519583631) ^ 22926330 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_42945522289 : Nat.Prime 42945522289 := by
  apply lucas_primality 42945522289 (7 : ZMod 42945522289)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (139, 1), (487, 1), (13217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (139, 1), (487, 1), (13217, 1)] : List FactorBlock).map factorBlockValue).prod) = 42945522289 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_139
      · exact prime_seventySevenBW_487
      · exact prime_seventySevenBW_13217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 42945522289) ^ 21472761144 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (7 : ZMod 42945522289) ^ 14315174096 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (7 : ZMod 42945522289) ^ 308960592 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (7 : ZMod 42945522289) ^ 88183824 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (7 : ZMod 42945522289) ^ 3249264 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_45250228643 : Nat.Prime 45250228643 := by
  apply lucas_primality 45250228643 (2 : ZMod 45250228643)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (22625114321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (22625114321, 1)] : List FactorBlock).map factorBlockValue).prod) = 45250228643 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_22625114321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 45250228643) ^ 22625114321 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 45250228643) ^ 2 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_46656186019 : Nat.Prime 46656186019 := by
  apply lucas_primality 46656186019 (3 : ZMod 46656186019)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (9337, 1), (64063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (9337, 1), (64063, 1)] : List FactorBlock).map factorBlockValue).prod) = 46656186019 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_13
      · exact prime_seventySevenBW_9337
      · exact prime_seventySevenBW_64063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 46656186019) ^ 23328093009 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 46656186019) ^ 15552062006 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 46656186019) ^ 3588937386 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 46656186019) ^ 4996914 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 46656186019) ^ 728286 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_48694005803 : Nat.Prime 48694005803 := by
  apply lucas_primality 48694005803 (2 : ZMod 48694005803)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (67, 1), (27952931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (67, 1), (27952931, 1)] : List FactorBlock).map factorBlockValue).prod) = 48694005803 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_13
      · exact prime_seventySevenBW_67
      · exact prime_seventySevenBW_27952931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 48694005803) ^ 24347002901 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 48694005803) ^ 3745692754 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 48694005803) ^ 726776206 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 48694005803) ^ 1742 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_51627207371 : Nat.Prime 51627207371 := by
  apply lucas_primality 51627207371 (2 : ZMod 51627207371)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (23, 1), (29, 1), (277, 1), (27943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (23, 1), (29, 1), (277, 1), (27943, 1)] : List FactorBlock).map factorBlockValue).prod) = 51627207371 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_5
      · exact prime_seventySevenBW_23
      · exact prime_seventySevenBW_29
      · exact prime_seventySevenBW_277
      · exact prime_seventySevenBW_27943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 51627207371) ^ 25813603685 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 51627207371) ^ 10325441474 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 51627207371) ^ 2244661190 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 51627207371) ^ 1780248530 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 51627207371) ^ 186379810 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 51627207371) ^ 1847590 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_59491203901 : Nat.Prime 59491203901 := by
  apply lucas_primality 59491203901 (2 : ZMod 59491203901)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (198304013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (198304013, 1)] : List FactorBlock).map factorBlockValue).prod) = 59491203901 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_5
      · exact prime_seventySevenBW_198304013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 59491203901) ^ 29745601950 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 59491203901) ^ 19830401300 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 59491203901) ^ 11898240780 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 59491203901) ^ 300 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_59742650453 : Nat.Prime 59742650453 := by
  apply lucas_primality 59742650453 (2 : ZMod 59742650453)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (43, 1), (157, 1), (181, 1), (719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (43, 1), (157, 1), (181, 1), (719, 1)] : List FactorBlock).map factorBlockValue).prod) = 59742650453 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_17
      · exact prime_seventySevenBW_43
      · exact prime_seventySevenBW_157
      · exact prime_seventySevenBW_181
      · exact prime_seventySevenBW_719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 59742650453) ^ 29871325226 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 59742650453) ^ 3514273556 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 59742650453) ^ 1389363964 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 59742650453) ^ 380526436 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 59742650453) ^ 330069892 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 59742650453) ^ 83091308 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_63700809043 : Nat.Prime 63700809043 := by
  apply lucas_primality 63700809043 (2 : ZMod 63700809043)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (3079, 1), (265241, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (3079, 1), (265241, 1)] : List FactorBlock).map factorBlockValue).prod) = 63700809043 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_13
      · exact prime_seventySevenBW_3079
      · exact prime_seventySevenBW_265241
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 63700809043) ^ 31850404521 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 63700809043) ^ 21233603014 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 63700809043) ^ 4900062234 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 63700809043) ^ 20688798 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 63700809043) ^ 240162 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_74977564789 : Nat.Prime 74977564789 := by
  apply lucas_primality 74977564789 (2 : ZMod 74977564789)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (7, 1), (773, 1), (42767, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (7, 1), (773, 1), (42767, 1)] : List FactorBlock).map factorBlockValue).prod) = 74977564789 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_7
      · exact prime_seventySevenBW_773
      · exact prime_seventySevenBW_42767
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 74977564789) ^ 37488782394 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 74977564789) ^ 24992521596 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 74977564789) ^ 10711080684 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 74977564789) ^ 96995556 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 74977564789) ^ 1753164 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_101004430661 : Nat.Prime 101004430661 := by
  apply lucas_primality 101004430661 (2 : ZMod 101004430661)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (19937, 1), (36187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (19937, 1), (36187, 1)] : List FactorBlock).map factorBlockValue).prod) = 101004430661 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_5
      · exact prime_seventySevenBW_7
      · exact prime_seventySevenBW_19937
      · exact prime_seventySevenBW_36187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 101004430661) ^ 50502215330 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 101004430661) ^ 20200886132 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 101004430661) ^ 14429204380 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 101004430661) ^ 5066180 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 101004430661) ^ 2791180 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_102761786009 : Nat.Prime 102761786009 := by
  apply lucas_primality 102761786009 (3 : ZMod 102761786009)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (331, 1), (5543903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (331, 1), (5543903, 1)] : List FactorBlock).map factorBlockValue).prod) = 102761786009 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_7
      · exact prime_seventySevenBW_331
      · exact prime_seventySevenBW_5543903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 102761786009) ^ 51380893004 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 102761786009) ^ 14680255144 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 102761786009) ^ 310458568 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 102761786009) ^ 18536 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_109526822261 : Nat.Prime 109526822261 := by
  apply lucas_primality 109526822261 (2 : ZMod 109526822261)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (191, 1), (2791, 1), (10273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (191, 1), (2791, 1), (10273, 1)] : List FactorBlock).map factorBlockValue).prod) = 109526822261 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_5
      · exact prime_seventySevenBW_191
      · exact prime_seventySevenBW_2791
      · exact prime_seventySevenBW_10273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 109526822261) ^ 54763411130 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 109526822261) ^ 21905364452 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 109526822261) ^ 573438860 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 109526822261) ^ 39242860 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 109526822261) ^ 10661620 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_117757172053 : Nat.Prime 117757172053 := by
  apply lucas_primality 117757172053 (2 : ZMod 117757172053)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (13, 1), (109, 1), (607, 1), (3803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (13, 1), (109, 1), (607, 1), (3803, 1)] : List FactorBlock).map factorBlockValue).prod) = 117757172053 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_13
      · exact prime_seventySevenBW_109
      · exact prime_seventySevenBW_607
      · exact prime_seventySevenBW_3803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 117757172053) ^ 58878586026 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 117757172053) ^ 39252390684 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 117757172053) ^ 9058244004 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 117757172053) ^ 1080341028 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 117757172053) ^ 193998636 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 117757172053) ^ 30964284 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_124076546521 : Nat.Prime 124076546521 := by
  apply lucas_primality 124076546521 (17 : ZMod 124076546521)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (1033971221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (1033971221, 1)] : List FactorBlock).map factorBlockValue).prod) = 124076546521 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_5
      · exact prime_seventySevenBW_1033971221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 124076546521) ^ 62038273260 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (17 : ZMod 124076546521) ^ 41358848840 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (17 : ZMod 124076546521) ^ 24815309304 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (17 : ZMod 124076546521) ^ 120 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_168249868697 : Nat.Prime 168249868697 := by
  apply lucas_primality 168249868697 (3 : ZMod 168249868697)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (13, 1), (277, 1), (834341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (13, 1), (277, 1), (834341, 1)] : List FactorBlock).map factorBlockValue).prod) = 168249868697 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_7
      · exact prime_seventySevenBW_13
      · exact prime_seventySevenBW_277
      · exact prime_seventySevenBW_834341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 168249868697) ^ 84124934348 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 168249868697) ^ 24035695528 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 168249868697) ^ 12942297592 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 168249868697) ^ 607400248 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 168249868697) ^ 201656 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_184050804733 : Nat.Prime 184050804733 := by
  apply lucas_primality 184050804733 (5 : ZMod 184050804733)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (173, 1), (383, 1), (231479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (173, 1), (383, 1), (231479, 1)] : List FactorBlock).map factorBlockValue).prod) = 184050804733 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_173
      · exact prime_seventySevenBW_383
      · exact prime_seventySevenBW_231479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 184050804733) ^ 92025402366 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 184050804733) ^ 61350268244 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 184050804733) ^ 1063877484 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 184050804733) ^ 480550404 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 184050804733) ^ 795108 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_205523572019 : Nat.Prime 205523572019 := by
  apply lucas_primality 205523572019 (2 : ZMod 205523572019)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (102761786009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (102761786009, 1)] : List FactorBlock).map factorBlockValue).prod) = 205523572019 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_102761786009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 205523572019) ^ 102761786009 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 205523572019) ^ 2 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_305378691931 : Nat.Prime 305378691931 := by
  apply lucas_primality 305378691931 (2 : ZMod 305378691931)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (13, 1), (261007429, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (13, 1), (261007429, 1)] : List FactorBlock).map factorBlockValue).prod) = 305378691931 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_5
      · exact prime_seventySevenBW_13
      · exact prime_seventySevenBW_261007429
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 305378691931) ^ 152689345965 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 305378691931) ^ 101792897310 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 305378691931) ^ 61075738386 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 305378691931) ^ 23490668610 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 305378691931) ^ 1170 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_327757392331 : Nat.Prime 327757392331 := by
  apply lucas_primality 327757392331 (2 : ZMod 327757392331)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (19, 1), (575012969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (19, 1), (575012969, 1)] : List FactorBlock).map factorBlockValue).prod) = 327757392331 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_5
      · exact prime_seventySevenBW_19
      · exact prime_seventySevenBW_575012969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 327757392331) ^ 163878696165 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 327757392331) ^ 109252464110 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 327757392331) ^ 65551478466 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 327757392331) ^ 17250389070 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 327757392331) ^ 570 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_384023655937 : Nat.Prime 384023655937 := by
  apply lucas_primality 384023655937 (5 : ZMod 384023655937)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 9), (3, 3), (37, 1), (750797, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 9), (3, 3), (37, 1), (750797, 1)] : List FactorBlock).map factorBlockValue).prod) = 384023655937 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_37
      · exact prime_seventySevenBW_750797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 384023655937) ^ 192011827968 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 384023655937) ^ 128007885312 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 384023655937) ^ 10379017728 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 384023655937) ^ 511488 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_391205018731 : Nat.Prime 391205018731 := by
  apply lucas_primality 391205018731 (2 : ZMod 391205018731)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (13040167291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (13040167291, 1)] : List FactorBlock).map factorBlockValue).prod) = 391205018731 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_5
      · exact prime_seventySevenBW_13040167291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 391205018731) ^ 195602509365 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 391205018731) ^ 130401672910 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 391205018731) ^ 78241003746 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 391205018731) ^ 30 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_482490973049 : Nat.Prime 482490973049 := by
  apply lucas_primality 482490973049 (3 : ZMod 482490973049)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 2), (17, 1), (47, 1), (1540481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 2), (17, 1), (47, 1), (1540481, 1)] : List FactorBlock).map factorBlockValue).prod) = 482490973049 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_7
      · exact prime_seventySevenBW_17
      · exact prime_seventySevenBW_47
      · exact prime_seventySevenBW_1540481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 482490973049) ^ 241245486524 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 482490973049) ^ 68927281864 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 482490973049) ^ 28381821944 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 482490973049) ^ 10265765384 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 482490973049) ^ 313208 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_686325341101 : Nat.Prime 686325341101 := by
  apply lucas_primality 686325341101 (2 : ZMod 686325341101)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (7, 1), (59, 1), (61, 1), (71, 1), (1279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (7, 1), (59, 1), (61, 1), (71, 1), (1279, 1)] : List FactorBlock).map factorBlockValue).prod) = 686325341101 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_5
      · exact prime_seventySevenBW_7
      · exact prime_seventySevenBW_59
      · exact prime_seventySevenBW_61
      · exact prime_seventySevenBW_71
      · exact prime_seventySevenBW_1279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 686325341101) ^ 343162670550 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 686325341101) ^ 228775113700 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 686325341101) ^ 137265068220 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 686325341101) ^ 98046477300 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 686325341101) ^ 11632632900 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 686325341101) ^ 11251235100 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 686325341101) ^ 9666554100 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 686325341101) ^ 536610900 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_1018715778649 : Nat.Prime 1018715778649 := by
  apply lucas_primality 1018715778649 (11 : ZMod 1018715778649)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 4), (23, 2), (619, 1), (4801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 4), (23, 2), (619, 1), (4801, 1)] : List FactorBlock).map factorBlockValue).prod) = 1018715778649 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_23
      · exact prime_seventySevenBW_619
      · exact prime_seventySevenBW_4801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 1018715778649) ^ 509357889324 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (11 : ZMod 1018715778649) ^ 339571926216 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (11 : ZMod 1018715778649) ^ 44291990376 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (11 : ZMod 1018715778649) ^ 1645744392 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (11 : ZMod 1018715778649) ^ 212188248 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_1107805252247 : Nat.Prime 1107805252247 := by
  apply lucas_primality 1107805252247 (7 : ZMod 1107805252247)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 3), (11, 1), (17, 1), (977, 1), (8839, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 3), (11, 1), (17, 1), (977, 1), (8839, 1)] : List FactorBlock).map factorBlockValue).prod) = 1107805252247 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_7
      · exact prime_seventySevenBW_11
      · exact prime_seventySevenBW_17
      · exact prime_seventySevenBW_977
      · exact prime_seventySevenBW_8839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1107805252247) ^ 553902626123 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (7 : ZMod 1107805252247) ^ 158257893178 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (7 : ZMod 1107805252247) ^ 100709568386 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (7 : ZMod 1107805252247) ^ 65165014838 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (7 : ZMod 1107805252247) ^ 1133884598 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (7 : ZMod 1107805252247) ^ 125331514 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_1256820086999 : Nat.Prime 1256820086999 := by
  apply lucas_primality 1256820086999 (7 : ZMod 1256820086999)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (433, 1), (6337, 1), (32717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (433, 1), (6337, 1), (32717, 1)] : List FactorBlock).map factorBlockValue).prod) = 1256820086999 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_7
      · exact prime_seventySevenBW_433
      · exact prime_seventySevenBW_6337
      · exact prime_seventySevenBW_32717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1256820086999) ^ 628410043499 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (7 : ZMod 1256820086999) ^ 179545726714 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (7 : ZMod 1256820086999) ^ 2902586806 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (7 : ZMod 1256820086999) ^ 198330454 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (7 : ZMod 1256820086999) ^ 38414894 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_1334527759063 : Nat.Prime 1334527759063 := by
  apply lucas_primality 1334527759063 (5 : ZMod 1334527759063)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (17, 1), (131, 1), (167, 1), (311, 1), (641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (17, 1), (131, 1), (167, 1), (311, 1), (641, 1)] : List FactorBlock).map factorBlockValue).prod) = 1334527759063 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_17
      · exact prime_seventySevenBW_131
      · exact prime_seventySevenBW_167
      · exact prime_seventySevenBW_311
      · exact prime_seventySevenBW_641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1334527759063) ^ 667263879531 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 1334527759063) ^ 444842586354 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 1334527759063) ^ 78501632886 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 1334527759063) ^ 10187234802 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 1334527759063) ^ 7991184186 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 1334527759063) ^ 4291086042 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 1334527759063) ^ 2081946582 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_1424414591657 : Nat.Prime 1424414591657 := by
  apply lucas_primality 1424414591657 (3 : ZMod 1424414591657)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 2), (3633710693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 2), (3633710693, 1)] : List FactorBlock).map factorBlockValue).prod) = 1424414591657 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_7
      · exact prime_seventySevenBW_3633710693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1424414591657) ^ 712207295828 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 1424414591657) ^ 203487798808 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 1424414591657) ^ 392 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_1737865754861 : Nat.Prime 1737865754861 := by
  apply lucas_primality 1737865754861 (2 : ZMod 1737865754861)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (29, 1), (2996320267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (29, 1), (2996320267, 1)] : List FactorBlock).map factorBlockValue).prod) = 1737865754861 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_5
      · exact prime_seventySevenBW_29
      · exact prime_seventySevenBW_2996320267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1737865754861) ^ 868932877430 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1737865754861) ^ 347573150972 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1737865754861) ^ 59926405340 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1737865754861) ^ 580 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_1971039134627 : Nat.Prime 1971039134627 := by
  apply lucas_primality 1971039134627 (2 : ZMod 1971039134627)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1123, 1), (877577531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1123, 1), (877577531, 1)] : List FactorBlock).map factorBlockValue).prod) = 1971039134627 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_1123
      · exact prime_seventySevenBW_877577531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1971039134627) ^ 985519567313 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1971039134627) ^ 1755155062 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1971039134627) ^ 2246 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_2346769411199 : Nat.Prime 2346769411199 := by
  apply lucas_primality 2346769411199 (11 : ZMod 2346769411199)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (977, 1), (1201007887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (977, 1), (1201007887, 1)] : List FactorBlock).map factorBlockValue).prod) = 2346769411199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_977
      · exact prime_seventySevenBW_1201007887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 2346769411199) ^ 1173384705599 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (11 : ZMod 2346769411199) ^ 2402015774 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (11 : ZMod 2346769411199) ^ 1954 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_3038387599969 : Nat.Prime 3038387599969 := by
  apply lucas_primality 3038387599969 (11 : ZMod 3038387599969)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (7, 1), (4521410119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (7, 1), (4521410119, 1)] : List FactorBlock).map factorBlockValue).prod) = 3038387599969 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_7
      · exact prime_seventySevenBW_4521410119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 3038387599969) ^ 1519193799984 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (11 : ZMod 3038387599969) ^ 1012795866656 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (11 : ZMod 3038387599969) ^ 434055371424 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (11 : ZMod 3038387599969) ^ 672 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_3185899456697 : Nat.Prime 3185899456697 := by
  apply lucas_primality 3185899456697 (3 : ZMod 3185899456697)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 3), (31, 1), (79, 1), (122173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 3), (31, 1), (79, 1), (122173, 1)] : List FactorBlock).map factorBlockValue).prod) = 3185899456697 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_11
      · exact prime_seventySevenBW_31
      · exact prime_seventySevenBW_79
      · exact prime_seventySevenBW_122173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3185899456697) ^ 1592949728348 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 3185899456697) ^ 289627223336 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 3185899456697) ^ 102770950216 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 3185899456697) ^ 40327841224 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 3185899456697) ^ 26076952 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_3250053307037 : Nat.Prime 3250053307037 := by
  apply lucas_primality 3250053307037 (2 : ZMod 3250053307037)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (409, 1), (643, 1), (3089557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (409, 1), (643, 1), (3089557, 1)] : List FactorBlock).map factorBlockValue).prod) = 3250053307037 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_409
      · exact prime_seventySevenBW_643
      · exact prime_seventySevenBW_3089557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3250053307037) ^ 1625026653518 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 3250053307037) ^ 7946340604 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 3250053307037) ^ 5054515252 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 3250053307037) ^ 1051948 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_3356157660787 : Nat.Prime 3356157660787 := by
  apply lucas_primality 3356157660787 (3 : ZMod 3356157660787)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (28603, 1), (931237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (28603, 1), (931237, 1)] : List FactorBlock).map factorBlockValue).prod) = 3356157660787 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_7
      · exact prime_seventySevenBW_28603
      · exact prime_seventySevenBW_931237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3356157660787) ^ 1678078830393 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 3356157660787) ^ 1118719220262 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 3356157660787) ^ 479451094398 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 3356157660787) ^ 117335862 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 3356157660787) ^ 3603978 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_4023349811477 : Nat.Prime 4023349811477 := by
  apply lucas_primality 4023349811477 (2 : ZMod 4023349811477)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (97, 1), (10369458277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (97, 1), (10369458277, 1)] : List FactorBlock).map factorBlockValue).prod) = 4023349811477 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_97
      · exact prime_seventySevenBW_10369458277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4023349811477) ^ 2011674905738 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 4023349811477) ^ 41477833108 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 4023349811477) ^ 388 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_4034716961311 : Nat.Prime 4034716961311 := by
  apply lucas_primality 4034716961311 (6 : ZMod 4034716961311)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (5, 1), (7, 1), (47, 1), (227, 1), (66697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (5, 1), (7, 1), (47, 1), (227, 1), (66697, 1)] : List FactorBlock).map factorBlockValue).prod) = 4034716961311 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_5
      · exact prime_seventySevenBW_7
      · exact prime_seventySevenBW_47
      · exact prime_seventySevenBW_227
      · exact prime_seventySevenBW_66697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 4034716961311) ^ 2017358480655 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (6 : ZMod 4034716961311) ^ 1344905653770 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (6 : ZMod 4034716961311) ^ 806943392262 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (6 : ZMod 4034716961311) ^ 576388137330 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (6 : ZMod 4034716961311) ^ 85845041730 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (6 : ZMod 4034716961311) ^ 17774083530 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (6 : ZMod 4034716961311) ^ 60493230 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_4097936781539 : Nat.Prime 4097936781539 := by
  apply lucas_primality 4097936781539 (2 : ZMod 4097936781539)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2647, 1), (774071927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2647, 1), (774071927, 1)] : List FactorBlock).map factorBlockValue).prod) = 4097936781539 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_2647
      · exact prime_seventySevenBW_774071927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4097936781539) ^ 2048968390769 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 4097936781539) ^ 1548143854 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 4097936781539) ^ 5294 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_4261893406171 : Nat.Prime 4261893406171 := by
  apply lucas_primality 4261893406171 (7 : ZMod 4261893406171)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (47, 1), (5923, 1), (510319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (47, 1), (5923, 1), (510319, 1)] : List FactorBlock).map factorBlockValue).prod) = 4261893406171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_5
      · exact prime_seventySevenBW_47
      · exact prime_seventySevenBW_5923
      · exact prime_seventySevenBW_510319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 4261893406171) ^ 2130946703085 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (7 : ZMod 4261893406171) ^ 1420631135390 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (7 : ZMod 4261893406171) ^ 852378681234 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (7 : ZMod 4261893406171) ^ 90678583110 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (7 : ZMod 4261893406171) ^ 719549790 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (7 : ZMod 4261893406171) ^ 8351430 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_4592945068493 : Nat.Prime 4592945068493 := by
  apply lucas_primality 4592945068493 (2 : ZMod 4592945068493)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (1193, 1), (87498001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (1193, 1), (87498001, 1)] : List FactorBlock).map factorBlockValue).prod) = 4592945068493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_11
      · exact prime_seventySevenBW_1193
      · exact prime_seventySevenBW_87498001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4592945068493) ^ 2296472534246 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 4592945068493) ^ 417540460772 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 4592945068493) ^ 3849912044 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 4592945068493) ^ 52492 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_4733201951593 : Nat.Prime 4733201951593 := by
  apply lucas_primality 4733201951593 (5 : ZMod 4733201951593)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (26683, 1), (7391101, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (26683, 1), (7391101, 1)] : List FactorBlock).map factorBlockValue).prod) = 4733201951593 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_26683
      · exact prime_seventySevenBW_7391101
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 4733201951593) ^ 2366600975796 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 4733201951593) ^ 1577733983864 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 4733201951593) ^ 177386424 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 4733201951593) ^ 640392 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_5566247406437 : Nat.Prime 5566247406437 := by
  apply lucas_primality 5566247406437 (2 : ZMod 5566247406437)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (845237, 1), (1646357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (845237, 1), (1646357, 1)] : List FactorBlock).map factorBlockValue).prod) = 5566247406437 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_845237
      · exact prime_seventySevenBW_1646357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 5566247406437) ^ 2783123703218 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 5566247406437) ^ 6585428 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 5566247406437) ^ 3380948 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_6948485070481 : Nat.Prime 6948485070481 := by
  apply lucas_primality 6948485070481 (7 : ZMod 6948485070481)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5, 1), (19301, 1), (500009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5, 1), (19301, 1), (500009, 1)] : List FactorBlock).map factorBlockValue).prod) = 6948485070481 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_5
      · exact prime_seventySevenBW_19301
      · exact prime_seventySevenBW_500009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 6948485070481) ^ 3474242535240 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (7 : ZMod 6948485070481) ^ 2316161690160 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (7 : ZMod 6948485070481) ^ 1389697014096 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (7 : ZMod 6948485070481) ^ 360006480 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (7 : ZMod 6948485070481) ^ 13896720 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_7879728894473 : Nat.Prime 7879728894473 := by
  apply lucas_primality 7879728894473 (3 : ZMod 7879728894473)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (173, 1), (7687, 1), (740659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (173, 1), (7687, 1), (740659, 1)] : List FactorBlock).map factorBlockValue).prod) = 7879728894473 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_173
      · exact prime_seventySevenBW_7687
      · exact prime_seventySevenBW_740659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 7879728894473) ^ 3939864447236 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 7879728894473) ^ 45547565864 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 7879728894473) ^ 1025072056 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 7879728894473) ^ 10638808 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_8064837625699 : Nat.Prime 8064837625699 := by
  apply lucas_primality 8064837625699 (3 : ZMod 8064837625699)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (29, 1), (163, 1), (2099, 1), (6451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (29, 1), (163, 1), (2099, 1), (6451, 1)] : List FactorBlock).map factorBlockValue).prod) = 8064837625699 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_7
      · exact prime_seventySevenBW_29
      · exact prime_seventySevenBW_163
      · exact prime_seventySevenBW_2099
      · exact prime_seventySevenBW_6451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 8064837625699) ^ 4032418812849 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 8064837625699) ^ 2688279208566 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 8064837625699) ^ 1152119660814 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 8064837625699) ^ 278097849162 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 8064837625699) ^ 49477531446 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 8064837625699) ^ 3842228502 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 8064837625699) ^ 1250168598 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_8932668636113 : Nat.Prime 8932668636113 := by
  apply lucas_primality 8932668636113 (3 : ZMod 8932668636113)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (13, 1), (42945522289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (13, 1), (42945522289, 1)] : List FactorBlock).map factorBlockValue).prod) = 8932668636113 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_13
      · exact prime_seventySevenBW_42945522289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 8932668636113) ^ 4466334318056 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 8932668636113) ^ 687128356624 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 8932668636113) ^ 208 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_11716513956677 : Nat.Prime 11716513956677 := by
  apply lucas_primality 11716513956677 (2 : ZMod 11716513956677)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 1), (101004430661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 1), (101004430661, 1)] : List FactorBlock).map factorBlockValue).prod) = 11716513956677 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_29
      · exact prime_seventySevenBW_101004430661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 11716513956677) ^ 5858256978338 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 11716513956677) ^ 404017722644 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 11716513956677) ^ 116 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_18159221275109 : Nat.Prime 18159221275109 := by
  apply lucas_primality 18159221275109 (2 : ZMod 18159221275109)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (4231, 1), (1072986367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (4231, 1), (1072986367, 1)] : List FactorBlock).map factorBlockValue).prod) = 18159221275109 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_4231
      · exact prime_seventySevenBW_1072986367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 18159221275109) ^ 9079610637554 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 18159221275109) ^ 4291945468 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 18159221275109) ^ 16924 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_21577718233171 : Nat.Prime 21577718233171 := by
  apply lucas_primality 21577718233171 (2 : ZMod 21577718233171)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (11, 1), (2713, 1), (8033791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (11, 1), (2713, 1), (8033791, 1)] : List FactorBlock).map factorBlockValue).prod) = 21577718233171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_5
      · exact prime_seventySevenBW_11
      · exact prime_seventySevenBW_2713
      · exact prime_seventySevenBW_8033791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 21577718233171) ^ 10788859116585 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 21577718233171) ^ 7192572744390 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 21577718233171) ^ 4315543646634 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 21577718233171) ^ 1961610748470 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 21577718233171) ^ 7953453090 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 21577718233171) ^ 2685870 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_35341756038997 : Nat.Prime 35341756038997 := by
  apply lucas_primality 35341756038997 (2 : ZMod 35341756038997)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (23, 1), (29, 1), (2239, 1), (179281, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (23, 1), (29, 1), (2239, 1), (179281, 1)] : List FactorBlock).map factorBlockValue).prod) = 35341756038997 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_11
      · exact prime_seventySevenBW_23
      · exact prime_seventySevenBW_29
      · exact prime_seventySevenBW_2239
      · exact prime_seventySevenBW_179281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 35341756038997) ^ 17670878019498 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 35341756038997) ^ 11780585346332 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 35341756038997) ^ 3212886912636 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 35341756038997) ^ 1536598088652 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 35341756038997) ^ 1218681242724 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 35341756038997) ^ 15784616364 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 35341756038997) ^ 197130516 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_40954908323647 : Nat.Prime 40954908323647 := by
  apply lucas_primality 40954908323647 (5 : ZMod 40954908323647)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (277, 1), (587, 1), (3323, 1), (4211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (277, 1), (587, 1), (3323, 1), (4211, 1)] : List FactorBlock).map factorBlockValue).prod) = 40954908323647 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_277
      · exact prime_seventySevenBW_587
      · exact prime_seventySevenBW_3323
      · exact prime_seventySevenBW_4211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 40954908323647) ^ 20477454161823 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 40954908323647) ^ 13651636107882 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 40954908323647) ^ 147851654598 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 40954908323647) ^ 69769860858 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 40954908323647) ^ 12324679002 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 40954908323647) ^ 9725696586 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_63717989133941 : Nat.Prime 63717989133941 := by
  apply lucas_primality 63717989133941 (2 : ZMod 63717989133941)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (3185899456697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (3185899456697, 1)] : List FactorBlock).map factorBlockValue).prod) = 63717989133941 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_5
      · exact prime_seventySevenBW_3185899456697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 63717989133941) ^ 31858994566970 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 63717989133941) ^ 12743597826788 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 63717989133941) ^ 20 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_68699214993041 : Nat.Prime 68699214993041 := by
  apply lucas_primality 68699214993041 (3 : ZMod 68699214993041)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (197381, 1), (4350673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (197381, 1), (4350673, 1)] : List FactorBlock).map factorBlockValue).prod) = 68699214993041 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_5
      · exact prime_seventySevenBW_197381
      · exact prime_seventySevenBW_4350673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 68699214993041) ^ 34349607496520 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 68699214993041) ^ 13739842998608 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 68699214993041) ^ 348053840 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 68699214993041) ^ 15790480 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_77927463690119 : Nat.Prime 77927463690119 := by
  apply lucas_primality 77927463690119 (7 : ZMod 77927463690119)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (5566247406437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (5566247406437, 1)] : List FactorBlock).map factorBlockValue).prod) = 77927463690119 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_7
      · exact prime_seventySevenBW_5566247406437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 77927463690119) ^ 38963731845059 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (7 : ZMod 77927463690119) ^ 11132494812874 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (7 : ZMod 77927463690119) ^ 14 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_82819860173383 : Nat.Prime 82819860173383 := by
  apply lucas_primality 82819860173383 (3 : ZMod 82819860173383)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 1), (2063, 1), (13421, 1), (17191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 1), (2063, 1), (13421, 1), (17191, 1)] : List FactorBlock).map factorBlockValue).prod) = 82819860173383 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_29
      · exact prime_seventySevenBW_2063
      · exact prime_seventySevenBW_13421
      · exact prime_seventySevenBW_17191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 82819860173383) ^ 41409930086691 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 82819860173383) ^ 27606620057794 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 82819860173383) ^ 2855857247358 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 82819860173383) ^ 40145351514 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 82819860173383) ^ 6170915742 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 82819860173383) ^ 4817629002 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_97680175640819 : Nat.Prime 97680175640819 := by
  apply lucas_primality 97680175640819 (6 : ZMod 97680175640819)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (59, 1), (48694005803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (59, 1), (48694005803, 1)] : List FactorBlock).map factorBlockValue).prod) = 97680175640819 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_17
      · exact prime_seventySevenBW_59
      · exact prime_seventySevenBW_48694005803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 97680175640819) ^ 48840087820409 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (6 : ZMod 97680175640819) ^ 5745892684754 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (6 : ZMod 97680175640819) ^ 1655596197302 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (6 : ZMod 97680175640819) ^ 2006 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_111817036902799 : Nat.Prime 111817036902799 := by
  apply lucas_primality 111817036902799 (6 : ZMod 111817036902799)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (37, 1), (683, 1), (245817641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (37, 1), (683, 1), (245817641, 1)] : List FactorBlock).map factorBlockValue).prod) = 111817036902799 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_37
      · exact prime_seventySevenBW_683
      · exact prime_seventySevenBW_245817641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 111817036902799) ^ 55908518451399 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (6 : ZMod 111817036902799) ^ 37272345634266 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (6 : ZMod 111817036902799) ^ 3022082078454 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (6 : ZMod 111817036902799) ^ 163714548906 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (6 : ZMod 111817036902799) ^ 454878 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_149273342996017 : Nat.Prime 149273342996017 := by
  apply lucas_primality 149273342996017 (5 : ZMod 149273342996017)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (37, 1), (877, 1), (4409, 1), (21737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (37, 1), (877, 1), (4409, 1), (21737, 1)] : List FactorBlock).map factorBlockValue).prod) = 149273342996017 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_37
      · exact prime_seventySevenBW_877
      · exact prime_seventySevenBW_4409
      · exact prime_seventySevenBW_21737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 149273342996017) ^ 74636671498008 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 149273342996017) ^ 49757780998672 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 149273342996017) ^ 4034414675568 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 149273342996017) ^ 170209057008 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 149273342996017) ^ 33856507824 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 149273342996017) ^ 6867246768 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_159495722471207 : Nat.Prime 159495722471207 := by
  apply lucas_primality 159495722471207 (5 : ZMod 159495722471207)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (4481, 1), (1617899033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (4481, 1), (1617899033, 1)] : List FactorBlock).map factorBlockValue).prod) = 159495722471207 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_11
      · exact prime_seventySevenBW_4481
      · exact prime_seventySevenBW_1617899033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 159495722471207) ^ 79747861235603 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 159495722471207) ^ 14499611133746 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 159495722471207) ^ 35593778726 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 159495722471207) ^ 98582 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_205958547905263 : Nat.Prime 205958547905263 := by
  apply lucas_primality 205958547905263 (5 : ZMod 205958547905263)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (577, 1), (59491203901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (577, 1), (59491203901, 1)] : List FactorBlock).map factorBlockValue).prod) = 205958547905263 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_577
      · exact prime_seventySevenBW_59491203901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 205958547905263) ^ 102979273952631 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 205958547905263) ^ 68652849301754 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 205958547905263) ^ 356947223406 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 205958547905263) ^ 3462 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_227380503673013 : Nat.Prime 227380503673013 := by
  apply lucas_primality 227380503673013 (2 : ZMod 227380503673013)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (2623141, 1), (21670633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (2623141, 1), (21670633, 1)] : List FactorBlock).map factorBlockValue).prod) = 227380503673013 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_2623141
      · exact prime_seventySevenBW_21670633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 227380503673013) ^ 113690251836506 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 227380503673013) ^ 86682532 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 227380503673013) ^ 10492564 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_330146434868357 : Nat.Prime 330146434868357 := by
  apply lucas_primality 330146434868357 (3 : ZMod 330146434868357)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (1790671, 1), (2711327, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (1790671, 1), (2711327, 1)] : List FactorBlock).map factorBlockValue).prod) = 330146434868357 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_17
      · exact prime_seventySevenBW_1790671
      · exact prime_seventySevenBW_2711327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 330146434868357) ^ 165073217434178 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 330146434868357) ^ 19420378521668 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 330146434868357) ^ 184370236 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 330146434868357) ^ 121765628 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_355038634440029 : Nat.Prime 355038634440029 := by
  apply lucas_primality 355038634440029 (2 : ZMod 355038634440029)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (11, 1), (47, 1), (83, 1), (295494191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (11, 1), (47, 1), (83, 1), (295494191, 1)] : List FactorBlock).map factorBlockValue).prod) = 355038634440029 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_7
      · exact prime_seventySevenBW_11
      · exact prime_seventySevenBW_47
      · exact prime_seventySevenBW_83
      · exact prime_seventySevenBW_295494191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 355038634440029) ^ 177519317220014 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 355038634440029) ^ 50719804920004 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 355038634440029) ^ 32276239494548 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 355038634440029) ^ 7554013498724 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 355038634440029) ^ 4277573908916 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 355038634440029) ^ 1201508 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_369167914746781 : Nat.Prime 369167914746781 := by
  apply lucas_primality 369167914746781 (2 : ZMod 369167914746781)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (101, 1), (107, 1), (797, 1), (809, 1), (883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (101, 1), (107, 1), (797, 1), (809, 1), (883, 1)] : List FactorBlock).map factorBlockValue).prod) = 369167914746781 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_5
      · exact prime_seventySevenBW_101
      · exact prime_seventySevenBW_107
      · exact prime_seventySevenBW_797
      · exact prime_seventySevenBW_809
      · exact prime_seventySevenBW_883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 369167914746781) ^ 184583957373390 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 369167914746781) ^ 123055971582260 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 369167914746781) ^ 73833582949356 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 369167914746781) ^ 3655127868780 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 369167914746781) ^ 3450167427540 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 369167914746781) ^ 463196881740 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 369167914746781) ^ 456326223420 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 369167914746781) ^ 418083708660 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_465415497110021 : Nat.Prime 465415497110021 := by
  apply lucas_primality 465415497110021 (2 : ZMod 465415497110021)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (71, 1), (327757392331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (71, 1), (327757392331, 1)] : List FactorBlock).map factorBlockValue).prod) = 465415497110021 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_5
      · exact prime_seventySevenBW_71
      · exact prime_seventySevenBW_327757392331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 465415497110021) ^ 232707748555010 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 465415497110021) ^ 93083099422004 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 465415497110021) ^ 6555147846620 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 465415497110021) ^ 1420 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_504046257646573 : Nat.Prime 504046257646573 := by
  apply lucas_primality 504046257646573 (2 : ZMod 504046257646573)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (379, 1), (47051, 1), (261721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (379, 1), (47051, 1), (261721, 1)] : List FactorBlock).map factorBlockValue).prod) = 504046257646573 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_379
      · exact prime_seventySevenBW_47051
      · exact prime_seventySevenBW_261721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 504046257646573) ^ 252023128823286 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 504046257646573) ^ 168015419215524 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 504046257646573) ^ 1329937355268 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 504046257646573) ^ 10712763972 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 504046257646573) ^ 1925891532 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_549736156734101 : Nat.Prime 549736156734101 := by
  apply lucas_primality 549736156734101 (2 : ZMod 549736156734101)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (7, 1), (578029, 1), (1358647, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (7, 1), (578029, 1), (1358647, 1)] : List FactorBlock).map factorBlockValue).prod) = 549736156734101 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_5
      · exact prime_seventySevenBW_7
      · exact prime_seventySevenBW_578029
      · exact prime_seventySevenBW_1358647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 549736156734101) ^ 274868078367050 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 549736156734101) ^ 109947231346820 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 549736156734101) ^ 78533736676300 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 549736156734101) ^ 951052900 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 549736156734101) ^ 404620300 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_608251276365893 : Nat.Prime 608251276365893 := by
  apply lucas_primality 608251276365893 (2 : ZMod 608251276365893)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5049721, 1), (30113113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5049721, 1), (30113113, 1)] : List FactorBlock).map factorBlockValue).prod) = 608251276365893 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_5049721
      · exact prime_seventySevenBW_30113113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 608251276365893) ^ 304125638182946 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 608251276365893) ^ 120452452 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 608251276365893) ^ 20198884 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_609851352215957 : Nat.Prime 609851352215957 := by
  apply lucas_primality 609851352215957 (2 : ZMod 609851352215957)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 1), (211, 1), (2797, 1), (8908223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 1), (211, 1), (2797, 1), (8908223, 1)] : List FactorBlock).map factorBlockValue).prod) = 609851352215957 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_29
      · exact prime_seventySevenBW_211
      · exact prime_seventySevenBW_2797
      · exact prime_seventySevenBW_8908223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 609851352215957) ^ 304925676107978 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 609851352215957) ^ 21029356972964 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 609851352215957) ^ 2890290768796 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 609851352215957) ^ 218037666148 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 609851352215957) ^ 68459372 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_737188349825647 : Nat.Prime 737188349825647 := by
  apply lucas_primality 737188349825647 (3 : ZMod 737188349825647)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (40954908323647, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (40954908323647, 1)] : List FactorBlock).map factorBlockValue).prod) = 737188349825647 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_40954908323647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 737188349825647) ^ 368594174912823 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 737188349825647) ^ 245729449941882 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 737188349825647) ^ 18 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_783426104154877 : Nat.Prime 783426104154877 := by
  apply lucas_primality 783426104154877 (2 : ZMod 783426104154877)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (13, 1), (43, 1), (113, 1), (147648317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (13, 1), (43, 1), (113, 1), (147648317, 1)] : List FactorBlock).map factorBlockValue).prod) = 783426104154877 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_7
      · exact prime_seventySevenBW_13
      · exact prime_seventySevenBW_43
      · exact prime_seventySevenBW_113
      · exact prime_seventySevenBW_147648317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 783426104154877) ^ 391713052077438 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 783426104154877) ^ 261142034718292 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 783426104154877) ^ 111918014879268 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 783426104154877) ^ 60263546473452 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 783426104154877) ^ 18219211724532 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 783426104154877) ^ 6932974373052 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 783426104154877) ^ 5306028 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_905311149667643 : Nat.Prime 905311149667643 := by
  apply lucas_primality 905311149667643 (2 : ZMod 905311149667643)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (257, 1), (1249519, 1), (1409587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (257, 1), (1249519, 1), (1409587, 1)] : List FactorBlock).map factorBlockValue).prod) = 905311149667643 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_257
      · exact prime_seventySevenBW_1249519
      · exact prime_seventySevenBW_1409587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 905311149667643) ^ 452655574833821 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 905311149667643) ^ 3522611477306 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 905311149667643) ^ 724527718 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 905311149667643) ^ 642252766 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_1090984491661667 : Nat.Prime 1090984491661667 := by
  apply lucas_primality 1090984491661667 (2 : ZMod 1090984491661667)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (77927463690119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (77927463690119, 1)] : List FactorBlock).map factorBlockValue).prod) = 1090984491661667 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_7
      · exact prime_seventySevenBW_77927463690119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1090984491661667) ^ 545492245830833 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1090984491661667) ^ 155854927380238 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1090984491661667) ^ 14 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_1875935571851597 : Nat.Prime 1875935571851597 := by
  apply lucas_primality 1875935571851597 (2 : ZMod 1875935571851597)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (19, 1), (29, 1), (1567, 1), (31951291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (19, 1), (29, 1), (1567, 1), (31951291, 1)] : List FactorBlock).map factorBlockValue).prod) = 1875935571851597 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_17
      · exact prime_seventySevenBW_19
      · exact prime_seventySevenBW_29
      · exact prime_seventySevenBW_1567
      · exact prime_seventySevenBW_31951291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1875935571851597) ^ 937967785925798 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1875935571851597) ^ 110349151285388 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1875935571851597) ^ 98733451150084 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1875935571851597) ^ 64687433512124 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1875935571851597) ^ 1197150971188 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1875935571851597) ^ 58712356 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_2032895660341163 : Nat.Prime 2032895660341163 := by
  apply lucas_primality 2032895660341163 (2 : ZMod 2032895660341163)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1481, 1), (686325341101, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1481, 1), (686325341101, 1)] : List FactorBlock).map factorBlockValue).prod) = 2032895660341163 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_1481
      · exact prime_seventySevenBW_686325341101
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2032895660341163) ^ 1016447830170581 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2032895660341163) ^ 1372650682202 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2032895660341163) ^ 2962 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_2142078358690553 : Nat.Prime 2142078358690553 := by
  apply lucas_primality 2142078358690553 (3 : ZMod 2142078358690553)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (6449, 1), (41519583631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (6449, 1), (41519583631, 1)] : List FactorBlock).map factorBlockValue).prod) = 2142078358690553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_6449
      · exact prime_seventySevenBW_41519583631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2142078358690553) ^ 1071039179345276 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 2142078358690553) ^ 332156669048 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 2142078358690553) ^ 51592 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_2930405269224571 : Nat.Prime 2930405269224571 := by
  apply lucas_primality 2930405269224571 (2 : ZMod 2930405269224571)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (97680175640819, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (97680175640819, 1)] : List FactorBlock).map factorBlockValue).prod) = 2930405269224571 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_5
      · exact prime_seventySevenBW_97680175640819
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2930405269224571) ^ 1465202634612285 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2930405269224571) ^ 976801756408190 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2930405269224571) ^ 586081053844914 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2930405269224571) ^ 30 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_4097864238220639 : Nat.Prime 4097864238220639 := by
  apply lucas_primality 4097864238220639 (15 : ZMod 4097864238220639)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (677, 1), (19037, 1), (17664359, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (677, 1), (19037, 1), (17664359, 1)] : List FactorBlock).map factorBlockValue).prod) = 4097864238220639 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_677
      · exact prime_seventySevenBW_19037
      · exact prime_seventySevenBW_17664359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 4097864238220639) ^ 2048932119110319 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (15 : ZMod 4097864238220639) ^ 1365954746073546 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (15 : ZMod 4097864238220639) ^ 6052975241094 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (15 : ZMod 4097864238220639) ^ 215257878774 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (15 : ZMod 4097864238220639) ^ 231984882 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_5144672913727219 : Nat.Prime 5144672913727219 := by
  apply lucas_primality 5144672913727219 (3 : ZMod 5144672913727219)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (601, 1), (3089, 1), (24308633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (601, 1), (3089, 1), (24308633, 1)] : List FactorBlock).map factorBlockValue).prod) = 5144672913727219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_19
      · exact prime_seventySevenBW_601
      · exact prime_seventySevenBW_3089
      · exact prime_seventySevenBW_24308633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 5144672913727219) ^ 2572336456863609 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 5144672913727219) ^ 1714890971242406 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 5144672913727219) ^ 270772258617222 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 5144672913727219) ^ 8560187876418 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 5144672913727219) ^ 1665481681362 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 5144672913727219) ^ 211639746 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_5818426729168337 : Nat.Prime 5818426729168337 := by
  apply lucas_primality 5818426729168337 (3 : ZMod 5818426729168337)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (23, 1), (73, 1), (69457, 1), (3118307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (23, 1), (73, 1), (69457, 1), (3118307, 1)] : List FactorBlock).map factorBlockValue).prod) = 5818426729168337 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_23
      · exact prime_seventySevenBW_73
      · exact prime_seventySevenBW_69457
      · exact prime_seventySevenBW_3118307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 5818426729168337) ^ 2909213364584168 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 5818426729168337) ^ 252975075181232 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 5818426729168337) ^ 79704475742032 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 5818426729168337) ^ 83770199248 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 5818426729168337) ^ 1865892848 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_6048555091758877 : Nat.Prime 6048555091758877 := by
  apply lucas_primality 6048555091758877 (5 : ZMod 6048555091758877)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (504046257646573, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (504046257646573, 1)] : List FactorBlock).map factorBlockValue).prod) = 6048555091758877 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_504046257646573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 6048555091758877) ^ 3024277545879438 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 6048555091758877) ^ 2016185030586292 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 6048555091758877) ^ 12 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_7209063491936693 : Nat.Prime 7209063491936693 := by
  apply lucas_primality 7209063491936693 (2 : ZMod 7209063491936693)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (117721, 1), (15309637813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (117721, 1), (15309637813, 1)] : List FactorBlock).map factorBlockValue).prod) = 7209063491936693 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_117721
      · exact prime_seventySevenBW_15309637813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 7209063491936693) ^ 3604531745968346 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 7209063491936693) ^ 61238551252 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 7209063491936693) ^ 470884 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_8151214823568527 : Nat.Prime 8151214823568527 := by
  apply lucas_primality 8151214823568527 (5 : ZMod 8151214823568527)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (59, 1), (130841, 1), (527954477, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (59, 1), (130841, 1), (527954477, 1)] : List FactorBlock).map factorBlockValue).prod) = 8151214823568527 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_59
      · exact prime_seventySevenBW_130841
      · exact prime_seventySevenBW_527954477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 8151214823568527) ^ 4075607411784263 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 8151214823568527) ^ 138156183450314 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 8151214823568527) ^ 62298628286 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 8151214823568527) ^ 15439238 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_11674969486397039 : Nat.Prime 11674969486397039 := by
  apply lucas_primality 11674969486397039 (7 : ZMod 11674969486397039)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (24071, 1), (5159810687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (24071, 1), (5159810687, 1)] : List FactorBlock).map factorBlockValue).prod) = 11674969486397039 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_47
      · exact prime_seventySevenBW_24071
      · exact prime_seventySevenBW_5159810687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 11674969486397039) ^ 5837484743198519 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (7 : ZMod 11674969486397039) ^ 248403606093554 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (7 : ZMod 11674969486397039) ^ 485022204578 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (7 : ZMod 11674969486397039) ^ 2262674 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_21011515127254237 : Nat.Prime 21011515127254237 := by
  apply lucas_primality 21011515127254237 (2 : ZMod 21011515127254237)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 2), (601, 1), (2903, 1), (5938379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 2), (601, 1), (2903, 1), (5938379, 1)] : List FactorBlock).map factorBlockValue).prod) = 21011515127254237 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_13
      · exact prime_seventySevenBW_601
      · exact prime_seventySevenBW_2903
      · exact prime_seventySevenBW_5938379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 21011515127254237) ^ 10505757563627118 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 21011515127254237) ^ 7003838375751412 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 21011515127254237) ^ 1616270394404172 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 21011515127254237) ^ 34960923672636 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 21011515127254237) ^ 7237862599812 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 21011515127254237) ^ 3538257684 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_21884661805067407 : Nat.Prime 21884661805067407 := by
  apply lucas_primality 21884661805067407 (3 : ZMod 21884661805067407)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (15731, 1), (21031, 1), (3674947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (15731, 1), (21031, 1), (3674947, 1)] : List FactorBlock).map factorBlockValue).prod) = 21884661805067407 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_15731
      · exact prime_seventySevenBW_21031
      · exact prime_seventySevenBW_3674947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 21884661805067407) ^ 10942330902533703 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 21884661805067407) ^ 7294887268355802 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 21884661805067407) ^ 1391180586426 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 21884661805067407) ^ 1040590642626 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 21884661805067407) ^ 5955095898 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_25751421919731847 : Nat.Prime 25751421919731847 := by
  apply lucas_primality 25751421919731847 (6 : ZMod 25751421919731847)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (330146434868357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (330146434868357, 1)] : List FactorBlock).map factorBlockValue).prod) = 25751421919731847 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_13
      · exact prime_seventySevenBW_330146434868357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 25751421919731847) ^ 12875710959865923 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (6 : ZMod 25751421919731847) ^ 8583807306577282 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (6 : ZMod 25751421919731847) ^ 1980878609210142 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (6 : ZMod 25751421919731847) ^ 78 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_27124634560394947 : Nat.Prime 27124634560394947 := by
  apply lucas_primality 27124634560394947 (2 : ZMod 27124634560394947)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (463, 1), (4801, 1), (2033761157, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (463, 1), (4801, 1), (2033761157, 1)] : List FactorBlock).map factorBlockValue).prod) = 27124634560394947 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_463
      · exact prime_seventySevenBW_4801
      · exact prime_seventySevenBW_2033761157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 27124634560394947) ^ 13562317280197473 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 27124634560394947) ^ 9041544853464982 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 27124634560394947) ^ 58584523888542 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 27124634560394947) ^ 5649788494146 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 27124634560394947) ^ 13337178 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_27960588541885231 : Nat.Prime 27960588541885231 := by
  apply lucas_primality 27960588541885231 (11 : ZMod 27960588541885231)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 1), (11, 1), (4034716961311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 1), (11, 1), (4034716961311, 1)] : List FactorBlock).map factorBlockValue).prod) = 27960588541885231 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_5
      · exact prime_seventySevenBW_7
      · exact prime_seventySevenBW_11
      · exact prime_seventySevenBW_4034716961311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 27960588541885231) ^ 13980294270942615 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (11 : ZMod 27960588541885231) ^ 9320196180628410 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (11 : ZMod 27960588541885231) ^ 5592117708377046 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (11 : ZMod 27960588541885231) ^ 3994369791697890 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (11 : ZMod 27960588541885231) ^ 2541871685625930 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (11 : ZMod 27960588541885231) ^ 6930 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_29806211125866113 : Nat.Prime 29806211125866113 := by
  apply lucas_primality 29806211125866113 (5 : ZMod 29806211125866113)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (7, 1), (23, 1), (31, 1), (46656186019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (7, 1), (23, 1), (31, 1), (46656186019, 1)] : List FactorBlock).map factorBlockValue).prod) = 29806211125866113 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_7
      · exact prime_seventySevenBW_23
      · exact prime_seventySevenBW_31
      · exact prime_seventySevenBW_46656186019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 29806211125866113) ^ 14903105562933056 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 29806211125866113) ^ 4258030160838016 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 29806211125866113) ^ 1295922222863744 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 29806211125866113) ^ 961490681479552 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 29806211125866113) ^ 638848 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_36291330550553263 : Nat.Prime 36291330550553263 := by
  apply lucas_primality 36291330550553263 (3 : ZMod 36291330550553263)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (6048555091758877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (6048555091758877, 1)] : List FactorBlock).map factorBlockValue).prod) = 36291330550553263 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_6048555091758877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 36291330550553263) ^ 18145665275276631 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 36291330550553263) ^ 12097110183517754 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 36291330550553263) ^ 6 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_40405690961470673 : Nat.Prime 40405690961470673 := by
  apply lucas_primality 40405690961470673 (3 : ZMod 40405690961470673)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (61, 1), (4017649, 1), (10304353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (61, 1), (4017649, 1), (10304353, 1)] : List FactorBlock).map factorBlockValue).prod) = 40405690961470673 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_61
      · exact prime_seventySevenBW_4017649
      · exact prime_seventySevenBW_10304353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 40405690961470673) ^ 20202845480735336 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 40405690961470673) ^ 662388376417552 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 40405690961470673) ^ 10057048528 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 40405690961470673) ^ 3921225424 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_68135728055607911 : Nat.Prime 68135728055607911 := by
  apply lucas_primality 68135728055607911 (23 : ZMod 68135728055607911)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (222193, 1), (30665110087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (222193, 1), (30665110087, 1)] : List FactorBlock).map factorBlockValue).prod) = 68135728055607911 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_5
      · exact prime_seventySevenBW_222193
      · exact prime_seventySevenBW_30665110087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (23 : ZMod 68135728055607911) ^ 34067864027803955 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (23 : ZMod 68135728055607911) ^ 13627145611121582 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (23 : ZMod 68135728055607911) ^ 306651100870 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (23 : ZMod 68135728055607911) ^ 2221930 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_85542336878398889 : Nat.Prime 85542336878398889 := by
  apply lucas_primality 85542336878398889 (3 : ZMod 85542336878398889)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (23, 1), (59, 1), (7879728894473, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (23, 1), (59, 1), (7879728894473, 1)] : List FactorBlock).map factorBlockValue).prod) = 85542336878398889 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_23
      · exact prime_seventySevenBW_59
      · exact prime_seventySevenBW_7879728894473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 85542336878398889) ^ 42771168439199444 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 85542336878398889) ^ 3719232038191256 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 85542336878398889) ^ 1449870116583032 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 85542336878398889) ^ 10856 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_103005687678927389 : Nat.Prime 103005687678927389 := by
  apply lucas_primality 103005687678927389 (2 : ZMod 103005687678927389)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (25751421919731847, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (25751421919731847, 1)] : List FactorBlock).map factorBlockValue).prod) = 103005687678927389 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_25751421919731847
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 103005687678927389) ^ 51502843839463694 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 103005687678927389) ^ 4 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_126912440068283977 : Nat.Prime 126912440068283977 := by
  apply lucas_primality 126912440068283977 (5 : ZMod 126912440068283977)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (17, 1), (23, 1), (109, 1), (124076546521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (17, 1), (23, 1), (109, 1), (124076546521, 1)] : List FactorBlock).map factorBlockValue).prod) = 126912440068283977 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_17
      · exact prime_seventySevenBW_23
      · exact prime_seventySevenBW_109
      · exact prime_seventySevenBW_124076546521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 126912440068283977) ^ 63456220034141988 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 126912440068283977) ^ 42304146689427992 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 126912440068283977) ^ 7465437651075528 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 126912440068283977) ^ 5517932176881912 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 126912440068283977) ^ 1164334312553064 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 126912440068283977) ^ 1022856 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_130780257091602337 : Nat.Prime 130780257091602337 := by
  apply lucas_primality 130780257091602337 (5 : ZMod 130780257091602337)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (1487, 1), (305378691931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (1487, 1), (305378691931, 1)] : List FactorBlock).map factorBlockValue).prod) = 130780257091602337 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_1487
      · exact prime_seventySevenBW_305378691931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 130780257091602337) ^ 65390128545801168 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 130780257091602337) ^ 43593419030534112 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 130780257091602337) ^ 87949063276128 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 130780257091602337) ^ 428256 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_163024296471370541 : Nat.Prime 163024296471370541 := by
  apply lucas_primality 163024296471370541 (3 : ZMod 163024296471370541)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (8151214823568527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (8151214823568527, 1)] : List FactorBlock).map factorBlockValue).prod) = 163024296471370541 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_5
      · exact prime_seventySevenBW_8151214823568527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 163024296471370541) ^ 81512148235685270 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 163024296471370541) ^ 32604859294274108 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 163024296471370541) ^ 20 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_187835428241006849 : Nat.Prime 187835428241006849 := by
  apply lucas_primality 187835428241006849 (3 : ZMod 187835428241006849)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (29, 1), (5881, 1), (4302177917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (29, 1), (5881, 1), (4302177917, 1)] : List FactorBlock).map factorBlockValue).prod) = 187835428241006849 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_29
      · exact prime_seventySevenBW_5881
      · exact prime_seventySevenBW_4302177917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 187835428241006849) ^ 93917714120503424 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 187835428241006849) ^ 6477083732448512 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 187835428241006849) ^ 31939368855808 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 187835428241006849) ^ 43660544 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_252813333891601369 : Nat.Prime 252813333891601369 := by
  apply lucas_primality 252813333891601369 (7 : ZMod 252813333891601369)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (17, 1), (79, 1), (167, 1), (181, 1), (1193, 1), (72503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (17, 1), (79, 1), (167, 1), (181, 1), (1193, 1), (72503, 1)] : List FactorBlock).map factorBlockValue).prod) = 252813333891601369 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_17
      · exact prime_seventySevenBW_79
      · exact prime_seventySevenBW_167
      · exact prime_seventySevenBW_181
      · exact prime_seventySevenBW_1193
      · exact prime_seventySevenBW_72503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 252813333891601369) ^ 126406666945800684 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (7 : ZMod 252813333891601369) ^ 84271111297200456 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (7 : ZMod 252813333891601369) ^ 14871372581858904 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (7 : ZMod 252813333891601369) ^ 3200168783437992 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (7 : ZMod 252813333891601369) ^ 1513852298752104 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (7 : ZMod 252813333891601369) ^ 1396758750782328 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (7 : ZMod 252813333891601369) ^ 211913942909976 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (7 : ZMod 252813333891601369) ^ 3486936180456 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_383878791035889731 : Nat.Prime 383878791035889731 := by
  apply lucas_primality 383878791035889731 (2 : ZMod 383878791035889731)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 2), (783426104154877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 2), (783426104154877, 1)] : List FactorBlock).map factorBlockValue).prod) = 383878791035889731 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_5
      · exact prime_seventySevenBW_7
      · exact prime_seventySevenBW_783426104154877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 383878791035889731) ^ 191939395517944865 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 383878791035889731) ^ 76775758207177946 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 383878791035889731) ^ 54839827290841390 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 383878791035889731) ^ 490 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_428414776695523129 : Nat.Prime 428414776695523129 := by
  apply lucas_primality 428414776695523129 (11 : ZMod 428414776695523129)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (2029, 1), (1256820086999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (2029, 1), (1256820086999, 1)] : List FactorBlock).map factorBlockValue).prod) = 428414776695523129 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_7
      · exact prime_seventySevenBW_2029
      · exact prime_seventySevenBW_1256820086999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 428414776695523129) ^ 214207388347761564 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (11 : ZMod 428414776695523129) ^ 142804925565174376 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (11 : ZMod 428414776695523129) ^ 61202110956503304 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (11 : ZMod 428414776695523129) ^ 211145774615832 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (11 : ZMod 428414776695523129) ^ 340872 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_502950773984652247 : Nat.Prime 502950773984652247 := by
  apply lucas_primality 502950773984652247 (3 : ZMod 502950773984652247)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (37, 1), (205958547905263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (37, 1), (205958547905263, 1)] : List FactorBlock).map factorBlockValue).prod) = 502950773984652247 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_11
      · exact prime_seventySevenBW_37
      · exact prime_seventySevenBW_205958547905263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 502950773984652247) ^ 251475386992326123 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 502950773984652247) ^ 167650257994884082 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 502950773984652247) ^ 45722797634968386 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 502950773984652247) ^ 13593264161747358 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 502950773984652247) ^ 2442 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_723848108156616419 : Nat.Prime 723848108156616419 := by
  apply lucas_primality 723848108156616419 (2 : ZMod 723848108156616419)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (11674969486397039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (11674969486397039, 1)] : List FactorBlock).map factorBlockValue).prod) = 723848108156616419 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_31
      · exact prime_seventySevenBW_11674969486397039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 723848108156616419) ^ 361924054078308209 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 723848108156616419) ^ 23349938972794078 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 723848108156616419) ^ 62 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_744758621333547137 : Nat.Prime 744758621333547137 := by
  apply lucas_primality 744758621333547137 (3 : ZMod 744758621333547137)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (5818426729168337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (5818426729168337, 1)] : List FactorBlock).map factorBlockValue).prod) = 744758621333547137 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_5818426729168337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 744758621333547137) ^ 372379310666773568 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 744758621333547137) ^ 128 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_761474640409703863 : Nat.Prime 761474640409703863 := by
  apply lucas_primality 761474640409703863 (6 : ZMod 761474640409703863)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (126912440068283977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (126912440068283977, 1)] : List FactorBlock).map factorBlockValue).prod) = 761474640409703863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_126912440068283977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 761474640409703863) ^ 380737320204851931 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (6 : ZMod 761474640409703863) ^ 253824880136567954 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (6 : ZMod 761474640409703863) ^ 6 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_777676918852972891 : Nat.Prime 777676918852972891 := by
  apply lucas_primality 777676918852972891 (28 : ZMod 777676918852972891)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (41, 1), (167, 1), (457, 1), (45083, 1), (61253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (41, 1), (167, 1), (457, 1), (45083, 1), (61253, 1)] : List FactorBlock).map factorBlockValue).prod) = 777676918852972891 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_5
      · exact prime_seventySevenBW_41
      · exact prime_seventySevenBW_167
      · exact prime_seventySevenBW_457
      · exact prime_seventySevenBW_45083
      · exact prime_seventySevenBW_61253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (28 : ZMod 777676918852972891) ^ 388838459426486445 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (28 : ZMod 777676918852972891) ^ 259225639617657630 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (28 : ZMod 777676918852972891) ^ 155535383770594578 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (28 : ZMod 777676918852972891) ^ 18967729728121290 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (28 : ZMod 777676918852972891) ^ 4656748017083670 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (28 : ZMod 777676918852972891) ^ 1701700041253770 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (28 : ZMod 777676918852972891) ^ 17249892838830 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (28 : ZMod 777676918852972891) ^ 12696144170130 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_798409272112171787 : Nat.Prime 798409272112171787 := by
  apply lucas_primality 798409272112171787 (2 : ZMod 798409272112171787)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (36291330550553263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (36291330550553263, 1)] : List FactorBlock).map factorBlockValue).prod) = 798409272112171787 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_11
      · exact prime_seventySevenBW_36291330550553263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 798409272112171787) ^ 399204636056085893 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 798409272112171787) ^ 72582661101106526 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 798409272112171787) ^ 22 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_970483800888884057 : Nat.Prime 970483800888884057 := by
  apply lucas_primality 970483800888884057 (3 : ZMod 970483800888884057)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (63858611, 1), (1899672937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (63858611, 1), (1899672937, 1)] : List FactorBlock).map factorBlockValue).prod) = 970483800888884057 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_63858611
      · exact prime_seventySevenBW_1899672937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 970483800888884057) ^ 485241900444442028 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 970483800888884057) ^ 15197383496 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 970483800888884057) ^ 510868888 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_1144212164056845409 : Nat.Prime 1144212164056845409 := by
  apply lucas_primality 1144212164056845409 (13 : ZMod 1144212164056845409)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (7, 1), (29, 1), (53, 1), (1107805252247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (7, 1), (29, 1), (53, 1), (1107805252247, 1)] : List FactorBlock).map factorBlockValue).prod) = 1144212164056845409 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_7
      · exact prime_seventySevenBW_29
      · exact prime_seventySevenBW_53
      · exact prime_seventySevenBW_1107805252247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 1144212164056845409) ^ 572106082028422704 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (13 : ZMod 1144212164056845409) ^ 381404054685615136 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (13 : ZMod 1144212164056845409) ^ 163458880579549344 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (13 : ZMod 1144212164056845409) ^ 39455591864029152 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (13 : ZMod 1144212164056845409) ^ 21588908755789536 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (13 : ZMod 1144212164056845409) ^ 1032864 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_1975554835858264979 : Nat.Prime 1975554835858264979 := by
  apply lucas_primality 1975554835858264979 (2 : ZMod 1975554835858264979)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (82128707, 1), (12027188227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (82128707, 1), (12027188227, 1)] : List FactorBlock).map factorBlockValue).prod) = 1975554835858264979 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_82128707
      · exact prime_seventySevenBW_12027188227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1975554835858264979) ^ 987777417929132489 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1975554835858264979) ^ 24054376454 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1975554835858264979) ^ 164257414 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_3267715550013314333 : Nat.Prime 3267715550013314333 := by
  apply lucas_primality 3267715550013314333 (2 : ZMod 3267715550013314333)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (44987, 1), (18159221275109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (44987, 1), (18159221275109, 1)] : List FactorBlock).map factorBlockValue).prod) = 3267715550013314333 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_44987
      · exact prime_seventySevenBW_18159221275109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3267715550013314333) ^ 1633857775006657166 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 3267715550013314333) ^ 72636885100436 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 3267715550013314333) ^ 179948 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_5598213111593622587 : Nat.Prime 5598213111593622587 := by
  apply lucas_primality 5598213111593622587 (2 : ZMod 5598213111593622587)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (61, 1), (1652687, 1), (2524098509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (61, 1), (1652687, 1), (2524098509, 1)] : List FactorBlock).map factorBlockValue).prod) = 5598213111593622587 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_11
      · exact prime_seventySevenBW_61
      · exact prime_seventySevenBW_1652687
      · exact prime_seventySevenBW_2524098509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5598213111593622587) ^ 2799106555796811293 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 5598213111593622587) ^ 508928464690329326 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 5598213111593622587) ^ 91773985435961026 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 5598213111593622587) ^ 3387340199078 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 5598213111593622587) ^ 2217905954 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_5759107460282792149 : Nat.Prime 5759107460282792149 := by
  apply lucas_primality 5759107460282792149 (10 : ZMod 5759107460282792149)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (37, 1), (307, 1), (3250053307037, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (37, 1), (307, 1), (3250053307037, 1)] : List FactorBlock).map factorBlockValue).prod) = 5759107460282792149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_13
      · exact prime_seventySevenBW_37
      · exact prime_seventySevenBW_307
      · exact prime_seventySevenBW_3250053307037
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 5759107460282792149) ^ 2879553730141396074 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (10 : ZMod 5759107460282792149) ^ 1919702486760930716 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (10 : ZMod 5759107460282792149) ^ 443008266175599396 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (10 : ZMod 5759107460282792149) ^ 155651552980616004 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (10 : ZMod 5759107460282792149) ^ 18759307688217564 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (10 : ZMod 5759107460282792149) ^ 1772004 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_17374794547725177133 : Nat.Prime 17374794547725177133 := by
  apply lucas_primality 17374794547725177133 (2 : ZMod 17374794547725177133)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (47, 1), (67, 1), (2447581, 1), (187857569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (47, 1), (67, 1), (2447581, 1), (187857569, 1)] : List FactorBlock).map factorBlockValue).prod) = 17374794547725177133 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_47
      · exact prime_seventySevenBW_67
      · exact prime_seventySevenBW_2447581
      · exact prime_seventySevenBW_187857569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 17374794547725177133) ^ 8687397273862588566 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 17374794547725177133) ^ 5791598182575059044 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 17374794547725177133) ^ 369676479738833556 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 17374794547725177133) ^ 259325291757092196 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 17374794547725177133) ^ 7098761817372 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 17374794547725177133) ^ 92489190828 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_36817887509490585457 : Nat.Prime 36817887509490585457 := by
  apply lucas_primality 36817887509490585457 (15 : ZMod 36817887509490585457)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (7, 1), (29, 1), (47, 1), (8932668636113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (7, 1), (29, 1), (47, 1), (8932668636113, 1)] : List FactorBlock).map factorBlockValue).prod) = 36817887509490585457 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_7
      · exact prime_seventySevenBW_29
      · exact prime_seventySevenBW_47
      · exact prime_seventySevenBW_8932668636113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 36817887509490585457) ^ 18408943754745292728 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (15 : ZMod 36817887509490585457) ^ 12272629169830195152 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (15 : ZMod 36817887509490585457) ^ 5259698215641512208 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (15 : ZMod 36817887509490585457) ^ 1269582327913468464 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (15 : ZMod 36817887509490585457) ^ 783359308712565648 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (15 : ZMod 36817887509490585457) ^ 4121712 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_43473582261879569119 : Nat.Prime 43473582261879569119 := by
  apply lucas_primality 43473582261879569119 (3 : ZMod 43473582261879569119)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (127, 1), (449, 1), (340103, 1), (11321389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (127, 1), (449, 1), (340103, 1), (11321389, 1)] : List FactorBlock).map factorBlockValue).prod) = 43473582261879569119 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_11
      · exact prime_seventySevenBW_127
      · exact prime_seventySevenBW_449
      · exact prime_seventySevenBW_340103
      · exact prime_seventySevenBW_11321389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 43473582261879569119) ^ 21736791130939784559 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 43473582261879569119) ^ 14491194087293189706 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 43473582261879569119) ^ 3952143841989051738 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 43473582261879569119) ^ 342311671353382434 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 43473582261879569119) ^ 96823123077682782 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 43473582261879569119) ^ 127824753859506 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 43473582261879569119) ^ 3839951287062 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_46296211010427227299 : Nat.Prime 46296211010427227299 := by
  apply lucas_primality 46296211010427227299 (7 : ZMod 46296211010427227299)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (59, 1), (130780257091602337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (59, 1), (130780257091602337, 1)] : List FactorBlock).map factorBlockValue).prod) = 46296211010427227299 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_59
      · exact prime_seventySevenBW_130780257091602337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 46296211010427227299) ^ 23148105505213613649 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (7 : ZMod 46296211010427227299) ^ 15432070336809075766 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (7 : ZMod 46296211010427227299) ^ 784681542549614022 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (7 : ZMod 46296211010427227299) ^ 354 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_66060447363398968993 : Nat.Prime 66060447363398968993 := by
  apply lucas_primality 66060447363398968993 (5 : ZMod 66060447363398968993)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 3), (121064557, 1), (631554379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 3), (121064557, 1), (631554379, 1)] : List FactorBlock).map factorBlockValue).prod) = 66060447363398968993 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_121064557
      · exact prime_seventySevenBW_631554379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 66060447363398968993) ^ 33030223681699484496 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 66060447363398968993) ^ 22020149121132989664 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 66060447363398968993) ^ 545662983456 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 66060447363398968993) ^ 104599777248 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_70382473756235746279 : Nat.Prime 70382473756235746279 := by
  apply lucas_primality 70382473756235746279 (3 : ZMod 70382473756235746279)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (4003, 1), (2930405269224571, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (4003, 1), (2930405269224571, 1)] : List FactorBlock).map factorBlockValue).prod) = 70382473756235746279 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_4003
      · exact prime_seventySevenBW_2930405269224571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 70382473756235746279) ^ 35191236878117873139 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 70382473756235746279) ^ 23460824585411915426 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 70382473756235746279) ^ 17582431615347426 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 70382473756235746279) ^ 24018 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_82818944565180771463 : Nat.Prime 82818944565180771463 := by
  apply lucas_primality 82818944565180771463 (3 : ZMod 82818944565180771463)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2683, 1), (5144672913727219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2683, 1), (5144672913727219, 1)] : List FactorBlock).map factorBlockValue).prod) = 82818944565180771463 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_2683
      · exact prime_seventySevenBW_5144672913727219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 82818944565180771463) ^ 41409472282590385731 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 82818944565180771463) ^ 27606314855060257154 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 82818944565180771463) ^ 30868037482363314 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 82818944565180771463) ^ 16098 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_91044343351754296201 : Nat.Prime 91044343351754296201 := by
  apply lucas_primality 91044343351754296201 (14 : ZMod 91044343351754296201)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (5, 2), (1439, 1), (11716513956677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (5, 2), (1439, 1), (11716513956677, 1)] : List FactorBlock).map factorBlockValue).prod) = 91044343351754296201 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_5
      · exact prime_seventySevenBW_1439
      · exact prime_seventySevenBW_11716513956677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 91044343351754296201) ^ 45522171675877148100 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (14 : ZMod 91044343351754296201) ^ 30348114450584765400 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (14 : ZMod 91044343351754296201) ^ 18208868670350859240 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (14 : ZMod 91044343351754296201) ^ 63269175366055800 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (14 : ZMod 91044343351754296201) ^ 7770600 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_268714229356493884177 : Nat.Prime 268714229356493884177 := by
  apply lucas_primality 268714229356493884177 (5 : ZMod 268714229356493884177)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5598213111593622587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5598213111593622587, 1)] : List FactorBlock).map factorBlockValue).prod) = 268714229356493884177 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_5598213111593622587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 268714229356493884177) ^ 134357114678246942088 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 268714229356493884177) ^ 89571409785497961392 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 268714229356493884177) ^ 48 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_597393062329651798927 : Nat.Prime 597393062329651798927 := by
  apply lucas_primality 597393062329651798927 (5 : ZMod 597393062329651798927)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1811, 1), (27893, 1), (1971039134627, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1811, 1), (27893, 1), (1971039134627, 1)] : List FactorBlock).map factorBlockValue).prod) = 597393062329651798927 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_1811
      · exact prime_seventySevenBW_27893
      · exact prime_seventySevenBW_1971039134627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 597393062329651798927) ^ 298696531164825899463 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 597393062329651798927) ^ 199131020776550599642 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 597393062329651798927) ^ 329869167492905466 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 597393062329651798927) ^ 21417311236856982 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 597393062329651798927) ^ 303085338 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_827432058988506289727 : Nat.Prime 827432058988506289727 := by
  apply lucas_primality 827432058988506289727 (5 : ZMod 827432058988506289727)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (101, 1), (8467, 1), (72859, 1), (6640001971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (101, 1), (8467, 1), (72859, 1), (6640001971, 1)] : List FactorBlock).map factorBlockValue).prod) = 827432058988506289727 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_101
      · exact prime_seventySevenBW_8467
      · exact prime_seventySevenBW_72859
      · exact prime_seventySevenBW_6640001971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 827432058988506289727) ^ 413716029494253144863 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 827432058988506289727) ^ 8192396623648577126 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 827432058988506289727) ^ 97724348528227978 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 827432058988506289727) ^ 11356621131068314 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 827432058988506289727) ^ 124613224906 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_2481152241400839325019 : Nat.Prime 2481152241400839325019 := by
  apply lucas_primality 2481152241400839325019 (2 : ZMod 2481152241400839325019)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (23, 1), (61, 1), (619, 1), (12271219, 1), (16629889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (23, 1), (61, 1), (619, 1), (12271219, 1), (16629889, 1)] : List FactorBlock).map factorBlockValue).prod) = 2481152241400839325019 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_7
      · exact prime_seventySevenBW_23
      · exact prime_seventySevenBW_61
      · exact prime_seventySevenBW_619
      · exact prime_seventySevenBW_12271219
      · exact prime_seventySevenBW_16629889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2481152241400839325019) ^ 1240576120700419662509 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2481152241400839325019) ^ 354450320200119903574 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2481152241400839325019) ^ 107876184408732144566 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2481152241400839325019) ^ 40674626908210480738 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2481152241400839325019) ^ 4008323491762260622 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2481152241400839325019) ^ 202192809157822 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2481152241400839325019) ^ 149198364547162 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_2604899406231579731959 : Nat.Prime 2604899406231579731959 := by
  apply lucas_primality 2604899406231579731959 (3 : ZMod 2604899406231579731959)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (67049, 1), (613967, 1), (3515451557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (67049, 1), (613967, 1), (3515451557, 1)] : List FactorBlock).map factorBlockValue).prod) = 2604899406231579731959 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_67049
      · exact prime_seventySevenBW_613967
      · exact prime_seventySevenBW_3515451557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2604899406231579731959) ^ 1302449703115789865979 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 2604899406231579731959) ^ 868299802077193243986 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 2604899406231579731959) ^ 38850682429739142 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 2604899406231579731959) ^ 4242735206015274 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 2604899406231579731959) ^ 740985720894 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_2691950697209873905679 : Nat.Prime 2691950697209873905679 := by
  apply lucas_primality 2691950697209873905679 (11 : ZMod 2691950697209873905679)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (59, 1), (1181, 1), (9621869, 1), (2007593389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (59, 1), (1181, 1), (9621869, 1), (2007593389, 1)] : List FactorBlock).map factorBlockValue).prod) = 2691950697209873905679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_59
      · exact prime_seventySevenBW_1181
      · exact prime_seventySevenBW_9621869
      · exact prime_seventySevenBW_2007593389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 2691950697209873905679) ^ 1345975348604936952839 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (11 : ZMod 2691950697209873905679) ^ 45626283003557184842 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (11 : ZMod 2691950697209873905679) ^ 2279382470118436838 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (11 : ZMod 2691950697209873905679) ^ 279774199504262 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (11 : ZMod 2691950697209873905679) ^ 1340884420102 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_4154734329174576898147 : Nat.Prime 4154734329174576898147 := by
  apply lucas_primality 4154734329174576898147 (3 : ZMod 4154734329174576898147)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (83, 1), (252813333891601369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (83, 1), (252813333891601369, 1)] : List FactorBlock).map factorBlockValue).prod) = 4154734329174576898147 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_11
      · exact prime_seventySevenBW_83
      · exact prime_seventySevenBW_252813333891601369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4154734329174576898147) ^ 2077367164587288449073 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 4154734329174576898147) ^ 1384911443058192299382 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 4154734329174576898147) ^ 377703120834052445286 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 4154734329174576898147) ^ 50057040110537071062 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 4154734329174576898147) ^ 16434 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_5085695528706420896129 : Nat.Prime 5085695528706420896129 := by
  apply lucas_primality 5085695528706420896129 (3 : ZMod 5085695528706420896129)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (7, 2), (29, 1), (27960588541885231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (7, 2), (29, 1), (27960588541885231, 1)] : List FactorBlock).map factorBlockValue).prod) = 5085695528706420896129 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_7
      · exact prime_seventySevenBW_29
      · exact prime_seventySevenBW_27960588541885231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 5085695528706420896129) ^ 2542847764353210448064 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 5085695528706420896129) ^ 726527932672345842304 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 5085695528706420896129) ^ 175368811334704168832 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 5085695528706420896129) ^ 181888 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_6254926037181063767881 : Nat.Prime 6254926037181063767881 := by
  apply lucas_primality 6254926037181063767881 (7 : ZMod 6254926037181063767881)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (17374794547725177133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (17374794547725177133, 1)] : List FactorBlock).map factorBlockValue).prod) = 6254926037181063767881 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_5
      · exact prime_seventySevenBW_17374794547725177133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 6254926037181063767881) ^ 3127463018590531883940 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (7 : ZMod 6254926037181063767881) ^ 2084975345727021255960 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (7 : ZMod 6254926037181063767881) ^ 1250985207436212753576 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (7 : ZMod 6254926037181063767881) ^ 360 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_15318020242050200379301 : Nat.Prime 15318020242050200379301 := by
  apply lucas_primality 15318020242050200379301 (10 : ZMod 15318020242050200379301)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (557, 1), (1534411, 1), (59742650453, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (557, 1), (1534411, 1), (59742650453, 1)] : List FactorBlock).map factorBlockValue).prod) = 15318020242050200379301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_5
      · exact prime_seventySevenBW_557
      · exact prime_seventySevenBW_1534411
      · exact prime_seventySevenBW_59742650453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 15318020242050200379301) ^ 7659010121025100189650 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (10 : ZMod 15318020242050200379301) ^ 5106006747350066793100 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (10 : ZMod 15318020242050200379301) ^ 3063604048410040075860 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (10 : ZMod 15318020242050200379301) ^ 27500934007271454900 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (10 : ZMod 15318020242050200379301) ^ 9982996890696300 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (10 : ZMod 15318020242050200379301) ^ 256400078100 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_32158856058219111360017 : Nat.Prime 32158856058219111360017 := by
  apply lucas_primality 32158856058219111360017 (3 : ZMod 32158856058219111360017)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (349, 1), (5759107460282792149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (349, 1), (5759107460282792149, 1)] : List FactorBlock).map factorBlockValue).prod) = 32158856058219111360017 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_349
      · exact prime_seventySevenBW_5759107460282792149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 32158856058219111360017) ^ 16079428029109555680008 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 32158856058219111360017) ^ 92145719364524674384 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 32158856058219111360017) ^ 5584 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_50004696502052886756737 : Nat.Prime 50004696502052886756737 := by
  apply lucas_primality 50004696502052886756737 (3 : ZMod 50004696502052886756737)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (7, 1), (13619, 1), (4097864238220639, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (7, 1), (13619, 1), (4097864238220639, 1)] : List FactorBlock).map factorBlockValue).prod) = 50004696502052886756737 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_7
      · exact prime_seventySevenBW_13619
      · exact prime_seventySevenBW_4097864238220639
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 50004696502052886756737) ^ 25002348251026443378368 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 50004696502052886756737) ^ 7143528071721840965248 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 50004696502052886756737) ^ 3671686357445692544 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 50004696502052886756737) ^ 12202624 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_167201232183604190930801 : Nat.Prime 167201232183604190930801 := by
  apply lucas_primality 167201232183604190930801 (6 : ZMod 167201232183604190930801)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 2), (13, 1), (4974463961, 1), (6463828739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 2), (13, 1), (4974463961, 1), (6463828739, 1)] : List FactorBlock).map factorBlockValue).prod) = 167201232183604190930801 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_5
      · exact prime_seventySevenBW_13
      · exact prime_seventySevenBW_4974463961
      · exact prime_seventySevenBW_6463828739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 167201232183604190930801) ^ 83600616091802095465400 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (6 : ZMod 167201232183604190930801) ^ 33440246436720838186160 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (6 : ZMod 167201232183604190930801) ^ 12861633244892630071600 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (6 : ZMod 167201232183604190930801) ^ 33611909442800 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (6 : ZMod 167201232183604190930801) ^ 25867212597200 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_201904613157670508935601 : Nat.Prime 201904613157670508935601 := by
  apply lucas_primality 201904613157670508935601 (6 : ZMod 201904613157670508935601)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 2), (37, 1), (43, 1), (311, 1), (8663, 1), (117757172053, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 2), (37, 1), (43, 1), (311, 1), (8663, 1), (117757172053, 1)] : List FactorBlock).map factorBlockValue).prod) = 201904613157670508935601 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_5
      · exact prime_seventySevenBW_37
      · exact prime_seventySevenBW_43
      · exact prime_seventySevenBW_311
      · exact prime_seventySevenBW_8663
      · exact prime_seventySevenBW_117757172053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 201904613157670508935601) ^ 100952306578835254467800 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (6 : ZMod 201904613157670508935601) ^ 40380922631534101787120 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (6 : ZMod 201904613157670508935601) ^ 5456881436693797538800 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (6 : ZMod 201904613157670508935601) ^ 4695456119945825789200 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (6 : ZMod 201904613157670508935601) ^ 649210974783506459600 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (6 : ZMod 201904613157670508935601) ^ 23306546595598581200 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (6 : ZMod 201904613157670508935601) ^ 1714584425200 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_271688154940511897210657 : Nat.Prime 271688154940511897210657 := by
  apply lucas_primality 271688154940511897210657 (3 : ZMod 271688154940511897210657)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (11, 2), (43, 1), (48757469, 1), (33467690719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (11, 2), (43, 1), (48757469, 1), (33467690719, 1)] : List FactorBlock).map factorBlockValue).prod) = 271688154940511897210657 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_11
      · exact prime_seventySevenBW_43
      · exact prime_seventySevenBW_48757469
      · exact prime_seventySevenBW_33467690719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 271688154940511897210657) ^ 135844077470255948605328 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 271688154940511897210657) ^ 24698923176410172473696 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 271688154940511897210657) ^ 6318329184663067376992 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 271688154940511897210657) ^ 5572236633950624 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 271688154940511897210657) ^ 8117923558624 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_289060972133404421901791 : Nat.Prime 289060972133404421901791 := by
  apply lucas_primality 289060972133404421901791 (7 : ZMod 289060972133404421901791)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (10555699087, 1), (391205018731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (10555699087, 1), (391205018731, 1)] : List FactorBlock).map factorBlockValue).prod) = 289060972133404421901791 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_5
      · exact prime_seventySevenBW_7
      · exact prime_seventySevenBW_10555699087
      · exact prime_seventySevenBW_391205018731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 289060972133404421901791) ^ 144530486066702210950895 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (7 : ZMod 289060972133404421901791) ^ 57812194426680884380358 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (7 : ZMod 289060972133404421901791) ^ 41294424590486345985970 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (7 : ZMod 289060972133404421901791) ^ 27384351311170 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (7 : ZMod 289060972133404421901791) ^ 738898936090 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_411306872434452272165431 : Nat.Prime 411306872434452272165431 := by
  apply lucas_primality 411306872434452272165431 (3 : ZMod 411306872434452272165431)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (953, 1), (10099861, 1), (1424414591657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (953, 1), (10099861, 1), (1424414591657, 1)] : List FactorBlock).map factorBlockValue).prod) = 411306872434452272165431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_5
      · exact prime_seventySevenBW_953
      · exact prime_seventySevenBW_10099861
      · exact prime_seventySevenBW_1424414591657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 411306872434452272165431) ^ 205653436217226136082715 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 411306872434452272165431) ^ 137102290811484090721810 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 411306872434452272165431) ^ 82261374486890454433086 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 411306872434452272165431) ^ 431591681463223790310 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 411306872434452272165431) ^ 40724013175473630 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 411306872434452272165431) ^ 288755025990 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_481043256726328556775247 : Nat.Prime 481043256726328556775247 := by
  apply lucas_primality 481043256726328556775247 (3 : ZMod 481043256726328556775247)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (151, 1), (498493, 1), (355038634440029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (151, 1), (498493, 1), (355038634440029, 1)] : List FactorBlock).map factorBlockValue).prod) = 481043256726328556775247 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_151
      · exact prime_seventySevenBW_498493
      · exact prime_seventySevenBW_355038634440029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 481043256726328556775247) ^ 240521628363164278387623 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 481043256726328556775247) ^ 160347752242109518925082 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 481043256726328556775247) ^ 3185716931962440773346 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 481043256726328556775247) ^ 964995008407998822 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 481043256726328556775247) ^ 1354903974 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_624580969694739191634991 : Nat.Prime 624580969694739191634991 := by
  apply lucas_primality 624580969694739191634991 (3 : ZMod 624580969694739191634991)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 2), (97, 1), (34721, 1), (238481, 1), (528997561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 2), (97, 1), (34721, 1), (238481, 1), (528997561, 1)] : List FactorBlock).map factorBlockValue).prod) = 624580969694739191634991 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_5
      · exact prime_seventySevenBW_7
      · exact prime_seventySevenBW_97
      · exact prime_seventySevenBW_34721
      · exact prime_seventySevenBW_238481
      · exact prime_seventySevenBW_528997561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 624580969694739191634991) ^ 312290484847369595817495 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 624580969694739191634991) ^ 208193656564913063878330 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 624580969694739191634991) ^ 124916193938947838326998 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 624580969694739191634991) ^ 89225852813534170233570 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 624580969694739191634991) ^ 6438979069017929810670 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 624580969694739191634991) ^ 17988565124700878190 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 624580969694739191634991) ^ 2618996774144435790 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 624580969694739191634991) ^ 1180687806034590 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_990388716855428984512009 : Nat.Prime 990388716855428984512009 := by
  apply lucas_primality 990388716855428984512009 (7 : ZMod 990388716855428984512009)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (96323, 1), (428414776695523129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (96323, 1), (428414776695523129, 1)] : List FactorBlock).map factorBlockValue).prod) = 990388716855428984512009 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_96323
      · exact prime_seventySevenBW_428414776695523129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 990388716855428984512009) ^ 495194358427714492256004 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (7 : ZMod 990388716855428984512009) ^ 330129572285142994837336 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (7 : ZMod 990388716855428984512009) ^ 10281954640692555096 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (7 : ZMod 990388716855428984512009) ^ 2311752 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_2887510707517915481916289 : Nat.Prime 2887510707517915481916289 := by
  apply lucas_primality 2887510707517915481916289 (7 : ZMod 2887510707517915481916289)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (7381410293, 1), (1018715778649, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (7381410293, 1), (1018715778649, 1)] : List FactorBlock).map factorBlockValue).prod) = 2887510707517915481916289 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_7381410293
      · exact prime_seventySevenBW_1018715778649
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 2887510707517915481916289) ^ 1443755353758957740958144 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (7 : ZMod 2887510707517915481916289) ^ 962503569172638493972096 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (7 : ZMod 2887510707517915481916289) ^ 391186859001216 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (7 : ZMod 2887510707517915481916289) ^ 2834461552512 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_3015087936803806226554991 : Nat.Prime 3015087936803806226554991 := by
  apply lucas_primality 3015087936803806226554991 (7 : ZMod 3015087936803806226554991)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (63700809043, 1), (4733201951593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (63700809043, 1), (4733201951593, 1)] : List FactorBlock).map factorBlockValue).prod) = 3015087936803806226554991 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_5
      · exact prime_seventySevenBW_63700809043
      · exact prime_seventySevenBW_4733201951593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 3015087936803806226554991) ^ 1507543968401903113277495 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (7 : ZMod 3015087936803806226554991) ^ 603017587360761245310998 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (7 : ZMod 3015087936803806226554991) ^ 47332019515930 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (7 : ZMod 3015087936803806226554991) ^ 637008090430 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_6543599056635805160895259 : Nat.Prime 6543599056635805160895259 := by
  apply lucas_primality 6543599056635805160895259 (2 : ZMod 6543599056635805160895259)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23557, 1), (46296211010427227299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23557, 1), (46296211010427227299, 1)] : List FactorBlock).map factorBlockValue).prod) = 6543599056635805160895259 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_23557
      · exact prime_seventySevenBW_46296211010427227299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 6543599056635805160895259) ^ 3271799528317902580447629 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 6543599056635805160895259) ^ 2181199685545268386965086 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 6543599056635805160895259) ^ 277777266062563363794 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 6543599056635805160895259) ^ 141342 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_11537965789089647832493643 : Nat.Prime 11537965789089647832493643 := by
  apply lucas_primality 11537965789089647832493643 (2 : ZMod 11537965789089647832493643)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (613, 1), (727, 1), (761474640409703863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (613, 1), (727, 1), (761474640409703863, 1)] : List FactorBlock).map factorBlockValue).prod) = 11537965789089647832493643 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_17
      · exact prime_seventySevenBW_613
      · exact prime_seventySevenBW_727
      · exact prime_seventySevenBW_761474640409703863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 11537965789089647832493643) ^ 5768982894544823916246821 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 11537965789089647832493643) ^ 678703869946449872499626 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 11537965789089647832493643) ^ 18822130161647060085634 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 11537965789089647832493643) ^ 15870654455419047912646 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 11537965789089647832493643) ^ 15152134 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_13983801854979619262423171 : Nat.Prime 13983801854979619262423171 := by
  apply lucas_primality 13983801854979619262423171 (2 : ZMod 13983801854979619262423171)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (19, 1), (1999, 1), (36817887509490585457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (19, 1), (1999, 1), (36817887509490585457, 1)] : List FactorBlock).map factorBlockValue).prod) = 13983801854979619262423171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_5
      · exact prime_seventySevenBW_19
      · exact prime_seventySevenBW_1999
      · exact prime_seventySevenBW_36817887509490585457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 13983801854979619262423171) ^ 6991900927489809631211585 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 13983801854979619262423171) ^ 2796760370995923852484634 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 13983801854979619262423171) ^ 735989571314716803285430 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 13983801854979619262423171) ^ 6995398626803211236830 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 13983801854979619262423171) ^ 379810 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_39666470621314736992755923 : Nat.Prime 39666470621314736992755923 := by
  apply lucas_primality 39666470621314736992755923 (2 : ZMod 39666470621314736992755923)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (73, 1), (271688154940511897210657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (73, 1), (271688154940511897210657, 1)] : List FactorBlock).map factorBlockValue).prod) = 39666470621314736992755923 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_73
      · exact prime_seventySevenBW_271688154940511897210657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 39666470621314736992755923) ^ 19833235310657368496377961 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 39666470621314736992755923) ^ 543376309881023794421314 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 39666470621314736992755923) ^ 146 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_90762263286059143966475417 : Nat.Prime 90762263286059143966475417 := by
  apply lucas_primality 90762263286059143966475417 (3 : ZMod 90762263286059143966475417)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (19, 1), (32611, 1), (2635163, 1), (6948485070481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (19, 1), (32611, 1), (2635163, 1), (6948485070481, 1)] : List FactorBlock).map factorBlockValue).prod) = 90762263286059143966475417 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_19
      · exact prime_seventySevenBW_32611
      · exact prime_seventySevenBW_2635163
      · exact prime_seventySevenBW_6948485070481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 90762263286059143966475417) ^ 45381131643029571983237708 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 90762263286059143966475417) ^ 4776961225582060208761864 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 90762263286059143966475417) ^ 2783179396095156357256 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 90762263286059143966475417) ^ 34442751088285295432 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 90762263286059143966475417) ^ 13062165690136 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_237069140822701357808267821 : Nat.Prime 237069140822701357808267821 := by
  apply lucas_primality 237069140822701357808267821 (2 : ZMod 237069140822701357808267821)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (317, 1), (4154734329174576898147, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (317, 1), (4154734329174576898147, 1)] : List FactorBlock).map factorBlockValue).prod) = 237069140822701357808267821 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_5
      · exact prime_seventySevenBW_317
      · exact prime_seventySevenBW_4154734329174576898147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 237069140822701357808267821) ^ 118534570411350678904133910 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 237069140822701357808267821) ^ 79023046940900452602755940 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 237069140822701357808267821) ^ 47413828164540271561653564 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 237069140822701357808267821) ^ 747852179251423841666460 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 237069140822701357808267821) ^ 57060 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_348791379601215790798371047 : Nat.Prime 348791379601215790798371047 := by
  apply lucas_primality 348791379601215790798371047 (5 : ZMod 348791379601215790798371047)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (10513, 1), (277827019, 1), (4592945068493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (10513, 1), (277827019, 1), (4592945068493, 1)] : List FactorBlock).map factorBlockValue).prod) = 348791379601215790798371047 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_13
      · exact prime_seventySevenBW_10513
      · exact prime_seventySevenBW_277827019
      · exact prime_seventySevenBW_4592945068493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 348791379601215790798371047) ^ 174395689800607895399185523 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 348791379601215790798371047) ^ 26830106123170445446028542 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 348791379601215790798371047) ^ 33177150157064186321542 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 348791379601215790798371047) ^ 1255426419131739634 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 348791379601215790798371047) ^ 75940681719422 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_842912500702938161096063363 : Nat.Prime 842912500702938161096063363 := by
  apply lucas_primality 842912500702938161096063363 (2 : ZMod 842912500702938161096063363)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5088887, 1), (82818944565180771463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5088887, 1), (82818944565180771463, 1)] : List FactorBlock).map factorBlockValue).prod) = 842912500702938161096063363 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_5088887
      · exact prime_seventySevenBW_82818944565180771463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 842912500702938161096063363) ^ 421456250351469080548031681 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 842912500702938161096063363) ^ 165637889130361542926 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 842912500702938161096063363) ^ 10177774 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_1167109616357914376902241579 : Nat.Prime 1167109616357914376902241579 := by
  apply lucas_primality 1167109616357914376902241579 (2 : ZMod 1167109616357914376902241579)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13, 1), (19, 1), (23, 1), (63649, 1), (41610857, 1), (5540648219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13, 1), (19, 1), (23, 1), (63649, 1), (41610857, 1), (5540648219, 1)] : List FactorBlock).map factorBlockValue).prod) = 1167109616357914376902241579 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_7
      · exact prime_seventySevenBW_13
      · exact prime_seventySevenBW_19
      · exact prime_seventySevenBW_23
      · exact prime_seventySevenBW_63649
      · exact prime_seventySevenBW_41610857
      · exact prime_seventySevenBW_5540648219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1167109616357914376902241579) ^ 583554808178957188451120789 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1167109616357914376902241579) ^ 166729945193987768128891654 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1167109616357914376902241579) ^ 89777662796762644377095506 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1167109616357914376902241579) ^ 61426821913574440889591662 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1167109616357914376902241579) ^ 50743896363387581604445286 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1167109616357914376902241579) ^ 18336652835989793663722 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1167109616357914376902241579) ^ 28048199448473612954 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1167109616357914376902241579) ^ 210644958897708062 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_1182266884102822355823049913 : Nat.Prime 1182266884102822355823049913 := by
  apply lucas_primality 1182266884102822355823049913 (3 : ZMod 1182266884102822355823049913)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (45225283, 1), (3267715550013314333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (45225283, 1), (3267715550013314333, 1)] : List FactorBlock).map factorBlockValue).prod) = 1182266884102822355823049913 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_45225283
      · exact prime_seventySevenBW_3267715550013314333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1182266884102822355823049913) ^ 591133442051411177911524956 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 1182266884102822355823049913) ^ 26141724400106514664 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 1182266884102822355823049913) ^ 361802264 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_2334219232715828753804483159 : Nat.Prime 2334219232715828753804483159 := by
  apply lucas_primality 2334219232715828753804483159 (11 : ZMod 2334219232715828753804483159)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1167109616357914376902241579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1167109616357914376902241579, 1)] : List FactorBlock).map factorBlockValue).prod) = 2334219232715828753804483159 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_1167109616357914376902241579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (11 : ZMod 2334219232715828753804483159) ^ 1167109616357914376902241579 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (11 : ZMod 2334219232715828753804483159) ^ 2 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_3641382003036692855934993731 : Nat.Prime 3641382003036692855934993731 := by
  apply lucas_primality 3641382003036692855934993731 (2 : ZMod 3641382003036692855934993731)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (14303, 1), (159621013, 1), (159495722471207, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (14303, 1), (159621013, 1), (159495722471207, 1)] : List FactorBlock).map factorBlockValue).prod) = 3641382003036692855934993731 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_5
      · exact prime_seventySevenBW_14303
      · exact prime_seventySevenBW_159621013
      · exact prime_seventySevenBW_159495722471207
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3641382003036692855934993731) ^ 1820691001518346427967496865 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 3641382003036692855934993731) ^ 728276400607338571186998746 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 3641382003036692855934993731) ^ 254588687900209246726910 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 3641382003036692855934993731) ^ 22812673185056737210 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 3641382003036692855934993731) ^ 22830593489390 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_4791292109258806389388149647 : Nat.Prime 4791292109258806389388149647 := by
  apply lucas_primality 4791292109258806389388149647 (5 : ZMod 4791292109258806389388149647)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (191, 1), (178207, 1), (70382473756235746279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (191, 1), (178207, 1), (70382473756235746279, 1)] : List FactorBlock).map factorBlockValue).prod) = 4791292109258806389388149647 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_191
      · exact prime_seventySevenBW_178207
      · exact prime_seventySevenBW_70382473756235746279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 4791292109258806389388149647) ^ 2395646054629403194694074823 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 4791292109258806389388149647) ^ 25085299001355007274283506 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 4791292109258806389388149647) ^ 26886104974882055078578 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (5 : ZMod 4791292109258806389388149647) ^ 68075074 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_10114950008435257933152760361 : Nat.Prime 10114950008435257933152760361 := by
  apply lucas_primality 10114950008435257933152760361 (3 : ZMod 10114950008435257933152760361)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (13, 1), (389, 1), (50004696502052886756737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (13, 1), (389, 1), (50004696502052886756737, 1)] : List FactorBlock).map factorBlockValue).prod) = 10114950008435257933152760361 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_5
      · exact prime_seventySevenBW_13
      · exact prime_seventySevenBW_389
      · exact prime_seventySevenBW_50004696502052886756737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 10114950008435257933152760361) ^ 5057475004217628966576380180 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 10114950008435257933152760361) ^ 2022990001687051586630552072 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 10114950008435257933152760361) ^ 778073077571942917934827720 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 10114950008435257933152760361) ^ 26002442181067501113503240 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 10114950008435257933152760361) ^ 202280 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_18206910015183464279674968641 : Nat.Prime 18206910015183464279674968641 := by
  apply lucas_primality 18206910015183464279674968641 (3 : ZMod 18206910015183464279674968641)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (5, 1), (17, 1), (14719197137, 1), (227380503673013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (5, 1), (17, 1), (14719197137, 1), (227380503673013, 1)] : List FactorBlock).map factorBlockValue).prod) = 18206910015183464279674968641 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_5
      · exact prime_seventySevenBW_17
      · exact prime_seventySevenBW_14719197137
      · exact prime_seventySevenBW_227380503673013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 18206910015183464279674968641) ^ 9103455007591732139837484320 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 18206910015183464279674968641) ^ 3641382003036692855934993728 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 18206910015183464279674968641) ^ 1070994706775497898804409920 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 18206910015183464279674968641) ^ 1236949939981190720 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 18206910015183464279674968641) ^ 80072432425280 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_18206910015183464279674968653 : Nat.Prime 18206910015183464279674968653 := by
  apply lucas_primality 18206910015183464279674968653 (2 : ZMod 18206910015183464279674968653)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1993, 1), (2857, 1), (340634237, 1), (2346769411199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1993, 1), (2857, 1), (340634237, 1), (2346769411199, 1)] : List FactorBlock).map factorBlockValue).prod) = 18206910015183464279674968653 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_1993
      · exact prime_seventySevenBW_2857
      · exact prime_seventySevenBW_340634237
      · exact prime_seventySevenBW_2346769411199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 18206910015183464279674968653) ^ 9103455007591732139837484326 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 18206910015183464279674968653) ^ 9135429009123664967222764 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 18206910015183464279674968653) ^ 6372737142171321063939436 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 18206910015183464279674968653) ^ 53450029496546068796 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 18206910015183464279674968653) ^ 7758286744448948 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_18206910015183464279674968659 : Nat.Prime 18206910015183464279674968659 := by
  apply lucas_primality 18206910015183464279674968659 (2 : ZMod 18206910015183464279674968659)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (79, 1), (45191, 1), (256057, 1), (905311149667643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (79, 1), (45191, 1), (256057, 1), (905311149667643, 1)] : List FactorBlock).map factorBlockValue).prod) = 18206910015183464279674968659 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_11
      · exact prime_seventySevenBW_79
      · exact prime_seventySevenBW_45191
      · exact prime_seventySevenBW_256057
      · exact prime_seventySevenBW_905311149667643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 18206910015183464279674968659) ^ 9103455007591732139837484329 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 18206910015183464279674968659) ^ 1655173637743951298152269878 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 18206910015183464279674968659) ^ 230467215382069168097151502 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 18206910015183464279674968659) ^ 402887964753678039425438 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 18206910015183464279674968659) ^ 71104910294127730464994 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 18206910015183464279674968659) ^ 20111218139606 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_22758637518979330349593710811 : Nat.Prime 22758637518979330349593710811 := by
  apply lucas_primality 22758637518979330349593710811 (2 : ZMod 22758637518979330349593710811)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (13, 1), (389, 1), (50004696502052886756737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (13, 1), (389, 1), (50004696502052886756737, 1)] : List FactorBlock).map factorBlockValue).prod) = 22758637518979330349593710811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_5
      · exact prime_seventySevenBW_13
      · exact prime_seventySevenBW_389
      · exact prime_seventySevenBW_50004696502052886756737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 22758637518979330349593710811) ^ 11379318759489665174796855405 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 22758637518979330349593710811) ^ 7586212506326443449864570270 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 22758637518979330349593710811) ^ 4551727503795866069918742162 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 22758637518979330349593710811) ^ 1750664424536871565353362370 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 22758637518979330349593710811) ^ 58505494907401877505382290 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 22758637518979330349593710811) ^ 455130 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_30344850025305773799458281073 : Nat.Prime 30344850025305773799458281073 := by
  apply lucas_primality 30344850025305773799458281073 (3 : ZMod 30344850025305773799458281073)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (67, 1), (3926552057, 1), (7209063491936693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (67, 1), (3926552057, 1), (7209063491936693, 1)] : List FactorBlock).map factorBlockValue).prod) = 30344850025305773799458281073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_67
      · exact prime_seventySevenBW_3926552057
      · exact prime_seventySevenBW_7209063491936693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 30344850025305773799458281073) ^ 15172425012652886899729140536 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 30344850025305773799458281073) ^ 452908209332921997006840016 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 30344850025305773799458281073) ^ 7728116063356134896 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 30344850025305773799458281073) ^ 4209263805104 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_30344850025305773799458281099 : Nat.Prime 30344850025305773799458281099 := by
  apply lucas_primality 30344850025305773799458281099 (2 : ZMod 30344850025305773799458281099)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (2441, 1), (3065929, 1), (19124197, 1), (721148299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (2441, 1), (3065929, 1), (19124197, 1), (721148299, 1)] : List FactorBlock).map factorBlockValue).prod) = 30344850025305773799458281099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_7
      · exact prime_seventySevenBW_2441
      · exact prime_seventySevenBW_3065929
      · exact prime_seventySevenBW_19124197
      · exact prime_seventySevenBW_721148299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 30344850025305773799458281099) ^ 15172425012652886899729140549 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 30344850025305773799458281099) ^ 10114950008435257933152760366 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 30344850025305773799458281099) ^ 4334978575043681971351183014 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 30344850025305773799458281099) ^ 12431319141870452191502778 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 30344850025305773799458281099) ^ 9897440555637711701562 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 30344850025305773799458281099) ^ 1586725446579836727234 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 30344850025305773799458281099) ^ 42078515705277665502 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_45517275037958660699187421627 : Nat.Prime 45517275037958660699187421627 := by
  apply lucas_primality 45517275037958660699187421627 (2 : ZMod 45517275037958660699187421627)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (139, 1), (313, 1), (51627207371, 1), (482490973049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (139, 1), (313, 1), (51627207371, 1), (482490973049, 1)] : List FactorBlock).map factorBlockValue).prod) = 45517275037958660699187421627 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_7
      · exact prime_seventySevenBW_139
      · exact prime_seventySevenBW_313
      · exact prime_seventySevenBW_51627207371
      · exact prime_seventySevenBW_482490973049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 45517275037958660699187421627) ^ 22758637518979330349593710813 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 45517275037958660699187421627) ^ 15172425012652886899729140542 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 45517275037958660699187421627) ^ 6502467862565522957026774518 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 45517275037958660699187421627) ^ 327462410345026335965377134 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 45517275037958660699187421627) ^ 145422603955139491051717002 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 45517275037958660699187421627) ^ 881652860106599406 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (2 : ZMod 45517275037958660699187421627) ^ 94338086265784074 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_45517275037958660699187421639 : Nat.Prime 45517275037958660699187421639 := by
  apply lucas_primality 45517275037958660699187421639 (6 : ZMod 45517275037958660699187421639)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (1187, 1), (31247, 1), (355093, 1), (3372907, 1), (56924369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (1187, 1), (31247, 1), (355093, 1), (3372907, 1), (56924369, 1)] : List FactorBlock).map factorBlockValue).prod) = 45517275037958660699187421639 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_3
      · exact prime_seventySevenBW_1187
      · exact prime_seventySevenBW_31247
      · exact prime_seventySevenBW_355093
      · exact prime_seventySevenBW_3372907
      · exact prime_seventySevenBW_56924369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 45517275037958660699187421639) ^ 22758637518979330349593710819 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (6 : ZMod 45517275037958660699187421639) ^ 15172425012652886899729140546 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (6 : ZMod 45517275037958660699187421639) ^ 38346482761548998061657474 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (6 : ZMod 45517275037958660699187421639) ^ 1456692643708473155796954 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (6 : ZMod 45517275037958660699187421639) ^ 128184095541051670123566 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (6 : ZMod 45517275037958660699187421639) ^ 13494968891214213940434 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (6 : ZMod 45517275037958660699187421639) ^ 799609654662288144102 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_91034550075917321398374843233 : Nat.Prime 91034550075917321398374843233 := by
  apply lucas_primality 91034550075917321398374843233 (3 : ZMod 91034550075917321398374843233)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5711, 1), (435349, 1), (1144212164056845409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5711, 1), (435349, 1), (1144212164056845409, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843233 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_5711
      · exact prime_seventySevenBW_435349
      · exact prime_seventySevenBW_1144212164056845409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 91034550075917321398374843233) ^ 45517275037958660699187421616 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 91034550075917321398374843233) ^ 15940211885119474942807712 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 91034550075917321398374843233) ^ 209107061405716612185568 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 91034550075917321398374843233) ^ 79560900448 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_91034550075917321398374843239 : Nat.Prime 91034550075917321398374843239 := by
  apply lucas_primality 91034550075917321398374843239 (7 : ZMod 91034550075917321398374843239)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (29, 1), (205523572019, 1), (1090984491661667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (29, 1), (205523572019, 1), (1090984491661667, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843239 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_7
      · exact prime_seventySevenBW_29
      · exact prime_seventySevenBW_205523572019
      · exact prime_seventySevenBW_1090984491661667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 91034550075917321398374843239) ^ 45517275037958660699187421619 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (7 : ZMod 91034550075917321398374843239) ^ 13004935725131045914053549034 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (7 : ZMod 91034550075917321398374843239) ^ 3139122416410942117185339422 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (7 : ZMod 91034550075917321398374843239) ^ 442939703614636802 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (7 : ZMod 91034550075917321398374843239) ^ 83442570239714 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem prime_seventySevenBW_91034550075917321398374843281 : Nat.Prime 91034550075917321398374843281 := by
  apply lucas_primality 91034550075917321398374843281 (3 : ZMod 91034550075917321398374843281)
  · rw [← seventySevenBWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (7, 1), (233, 1), (491, 1), (6841, 1), (1128557, 1), (184050804733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (7, 1), (233, 1), (491, 1), (6841, 1), (1128557, 1), (184050804733, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843281 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_seventySevenBW_2
      · exact prime_seventySevenBW_5
      · exact prime_seventySevenBW_7
      · exact prime_seventySevenBW_233
      · exact prime_seventySevenBW_491
      · exact prime_seventySevenBW_6841
      · exact prime_seventySevenBW_1128557
      · exact prime_seventySevenBW_184050804733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 91034550075917321398374843281) ^ 45517275037958660699187421640 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 91034550075917321398374843281) ^ 18206910015183464279674968656 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 91034550075917321398374843281) ^ 13004935725131045914053549040 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 91034550075917321398374843281) ^ 390706223501791078962982160 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 91034550075917321398374843281) ^ 185406415633232833805244080 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 91034550075917321398374843281) ^ 13307199250974612103256080 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 91034550075917321398374843281) ^ 80664556664765112793040 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide
    · change (3 : ZMod 91034550075917321398374843281) ^ 494616419678142160 ≠ 1
      rw [← seventySevenBWFastPow_eq_pow]
      decide

private theorem phi_seventySevenBW_91034550075917321398374843200 : Nat.totient 91034550075917321398374843200 = 34271830614487405679550791680 := by
  rw [← show ((([(2, 6), (5, 2), (17, 1), (14719197137, 1), (227380503673013, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843200 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_2, prime_seventySevenBW_5, prime_seventySevenBW_17, prime_seventySevenBW_14719197137, prime_seventySevenBW_227380503673013]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843201 : Nat.totient 91034550075917321398374843201 = 56021261585179890091307595792 := by
  rw [← show ((([(3, 1), (13, 1), (2334219232715828753804483159, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843201 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_3, prime_seventySevenBW_13, prime_seventySevenBW_2334219232715828753804483159]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843202 : Nat.totient 91034550075917321398374843202 = 40977599728175279741925246720 := by
  rw [← show ((([(2, 1), (11, 1), (103, 1), (994268789, 1), (40405690961470673, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843202 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_2, prime_seventySevenBW_11, prime_seventySevenBW_103, prime_seventySevenBW_994268789, prime_seventySevenBW_40405690961470673]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843203 : Nat.totient 91034550075917321398374843203 = 78029163212522295437154073440 := by
  rw [← show ((([(7, 1), (172987, 1), (1179865987, 1), (63717989133941, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843203 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_7, prime_seventySevenBW_172987, prime_seventySevenBW_1179865987, prime_seventySevenBW_63717989133941]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843204 : Nat.totient 91034550075917321398374843204 = 30344850025305773799458281032 := by
  rw [← show ((([(2, 2), (3, 3), (842912500702938161096063363, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843204 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_2, prime_seventySevenBW_3, prime_seventySevenBW_842912500702938161096063363]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843205 : Nat.totient 91034550075917321398374843205 = 72827640060733857118699874560 := by
  rw [← show ((([(5, 1), (18206910015183464279674968641, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843205 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_5, prime_seventySevenBW_18206910015183464279674968641]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843206 : Nat.totient 91034550075917321398374843206 = 45425475777983653597836016008 := by
  rw [← show ((([(2, 1), (503, 1), (34739, 1), (2604899406231579731959, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843206 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_2, prime_seventySevenBW_503, prime_seventySevenBW_34739, prime_seventySevenBW_2604899406231579731959]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843207 : Nat.totient 91034550075917321398374843207 = 60689700048670579934603283392 := by
  rw [← show ((([(3, 1), (31267755317, 1), (970483800888884057, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843207 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_3, prime_seventySevenBW_31267755317, prime_seventySevenBW_970483800888884057]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843208 : Nat.totient 91034550075917321398374843208 = 43344800151155573385770188992 := by
  rw [← show ((([(2, 3), (37, 1), (47, 1), (6543599056635805160895259, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843208 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_2, prime_seventySevenBW_37, prime_seventySevenBW_47, prime_seventySevenBW_6543599056635805160895259]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843209 : Nat.totient 91034550075917321398374843209 = 87894527211536749146068690176 := by
  rw [← show ((([(29, 1), (97613, 1), (32158856058219111360017, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843209 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_29, prime_seventySevenBW_97613, prime_seventySevenBW_32158856058219111360017]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843210 : Nat.totient 91034550075917321398374843210 = 20136674671170651737889364800 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (7, 1), (31, 1), (13983801854979619262423171, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843210 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_2, prime_seventySevenBW_3, prime_seventySevenBW_5, prime_seventySevenBW_7, prime_seventySevenBW_31, prime_seventySevenBW_13983801854979619262423171]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843211 : Nat.totient 91034550075917321398374843211 = 89881646130056830004915450400 := by
  rw [← show ((([(79, 1), (159571, 1), (19561459, 1), (369167914746781, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843211 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_79, prime_seventySevenBW_159571, prime_seventySevenBW_19561459, prime_seventySevenBW_369167914746781]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843212 : Nat.totient 91034550075917321398374843212 = 44434452636346927734743158800 := by
  rw [← show ((([(2, 2), (43, 1), (1831, 1), (289060972133404421901791, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843212 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_2, prime_seventySevenBW_43, prime_seventySevenBW_1831, prime_seventySevenBW_289060972133404421901791]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843213 : Nat.totient 91034550075917321398374843213 = 55164413479101785070504186240 := by
  rw [← show ((([(3, 2), (11, 1), (6869, 1), (6116989, 1), (21884661805067407, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843213 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_3, prime_seventySevenBW_11, prime_seventySevenBW_6869, prime_seventySevenBW_6116989, prime_seventySevenBW_21884661805067407]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843214 : Nat.totient 91034550075917321398374843214 = 42015687331598500416441323520 := by
  rw [← show ((([(2, 1), (13, 1), (245783, 1), (477941, 1), (29806211125866113, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843214 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_2, prime_seventySevenBW_13, prime_seventySevenBW_245783, prime_seventySevenBW_477941, prime_seventySevenBW_29806211125866113]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843215 : Nat.totient 91034550075917321398374843215 = 72777875503330025479218731040 := by
  rw [← show ((([(5, 1), (1471, 1), (284707, 1), (43473582261879569119, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843215 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_5, prime_seventySevenBW_1471, prime_seventySevenBW_284707, prime_seventySevenBW_43473582261879569119]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843216 : Nat.totient 91034550075917321398374843216 = 29891941808360076608527322112 := by
  rw [← show ((([(2, 4), (3, 1), (67, 1), (3926552057, 1), (7209063491936693, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843216 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_2, prime_seventySevenBW_3, prime_seventySevenBW_67, prime_seventySevenBW_3926552057, prime_seventySevenBW_7209063491936693]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843217 : Nat.totient 91034550075917321398374843217 = 67445116079632999911195033600 := by
  rw [← show ((([(7, 1), (17, 1), (19, 1), (41, 1), (157, 1), (6254926037181063767881, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843217 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_7, prime_seventySevenBW_17, prime_seventySevenBW_19, prime_seventySevenBW_41, prime_seventySevenBW_157, prime_seventySevenBW_6254926037181063767881]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843218 : Nat.totient 91034550075917321398374843218 = 45473036089784883949329408000 := by
  rw [← show ((([(2, 1), (1031, 1), (504797, 1), (227741851, 1), (384023655937, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843218 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_2, prime_seventySevenBW_1031, prime_seventySevenBW_504797, prime_seventySevenBW_227741851, prime_seventySevenBW_384023655937]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843219 : Nat.totient 91034550075917321398374843219 = 60689700050611547598916562144 := by
  rw [← show ((([(3, 1), (30344850025305773799458281073, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843219 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_3, prime_seventySevenBW_30344850025305773799458281073]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843220 : Nat.totient 91034550075917321398374843220 = 36407510946127550951236915200 := by
  rw [← show ((([(2, 2), (5, 1), (5843, 1), (488417, 1), (14562271, 1), (109526822261, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843220 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_2, prime_seventySevenBW_5, prime_seventySevenBW_5843, prime_seventySevenBW_488417, prime_seventySevenBW_14562271, prime_seventySevenBW_109526822261]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843221 : Nat.totient 91034550075917321398374843221 = 90792843563145345564974174208 := by
  rw [← show ((([(383, 1), (23719, 1), (476929, 1), (21011515127254237, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843221 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_383, prime_seventySevenBW_23719, prime_seventySevenBW_476929, prime_seventySevenBW_21011515127254237]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843222 : Nat.totient 91034550075917321398374843222 = 29024837408047907430178707456 := by
  rw [← show ((([(2, 1), (3, 2), (23, 1), (43237, 1), (5085695528706420896129, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843222 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_2, prime_seventySevenBW_3, prime_seventySevenBW_23, prime_seventySevenBW_43237, prime_seventySevenBW_5085695528706420896129]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843223 : Nat.totient 91034550075917321398374843223 = 91033925494947626659183062480 := by
  rw [← show ((([(145753, 1), (624580969694739191634991, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843223 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_145753, prime_seventySevenBW_624580969694739191634991]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843224 : Nat.totient 91034550075917321398374843224 = 35468005738832938660641989760 := by
  rw [← show ((([(2, 3), (7, 1), (11, 1), (45225283, 1), (3267715550013314333, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843224 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_2, prime_seventySevenBW_7, prime_seventySevenBW_11, prime_seventySevenBW_45225283, prime_seventySevenBW_3267715550013314333]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843225 : Nat.totient 91034550075917321398374843225 = 48283512910047665859839385600 := by
  rw [← show ((([(3, 1), (5, 2), (181, 1), (9004319, 1), (744758621333547137, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843225 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_3, prime_seventySevenBW_5, prime_seventySevenBW_181, prime_seventySevenBW_9004319, prime_seventySevenBW_744758621333547137]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843226 : Nat.totient 91034550075917321398374843226 = 45514488174159058735215055104 := by
  rw [← show ((([(2, 1), (16333, 1), (1300992937, 1), (2142078358690553, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843226 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_2, prime_seventySevenBW_16333, prime_seventySevenBW_1300992937, prime_seventySevenBW_2142078358690553]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843227 : Nat.totient 91034550075917321398374843227 = 83470923705207036572255556000 := by
  rw [← show ((([(13, 1), (151, 1), (18691, 1), (2481152241400839325019, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843227 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_13, prime_seventySevenBW_151, prime_seventySevenBW_18691, prime_seventySevenBW_2481152241400839325019]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843228 : Nat.totient 91034550075917321398374843228 = 30096841595923350838969344000 := by
  rw [← show ((([(2, 2), (3, 1), (239, 1), (251, 1), (48757, 1), (853637, 1), (3038387599969, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843228 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_2, prime_seventySevenBW_3, prime_seventySevenBW_239, prime_seventySevenBW_251, prime_seventySevenBW_48757, prime_seventySevenBW_853637, prime_seventySevenBW_3038387599969]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843229 : Nat.totient 91034550075917321398374843229 = 89206752466257753148782105600 := by
  rw [← show ((([(53, 1), (811, 1), (2723393, 1), (777676918852972891, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843229 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_53, prime_seventySevenBW_811, prime_seventySevenBW_2723393, prime_seventySevenBW_777676918852972891]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843230 : Nat.totient 91034550075917321398374843230 = 36412174802877190750261187040 := by
  rw [← show ((([(2, 1), (5, 1), (22133, 1), (411306872434452272165431, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843230 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_2, prime_seventySevenBW_5, prime_seventySevenBW_22133, prime_seventySevenBW_411306872434452272165431]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843231 : Nat.totient 91034550075917321398374843231 = 52019549345171988848944266192 := by
  rw [← show ((([(3, 4), (7, 1), (268759, 1), (597393062329651798927, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843231 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_3, prime_seventySevenBW_7, prime_seventySevenBW_268759, prime_seventySevenBW_597393062329651798927]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843232 : Nat.totient 91034550075917321398374843232 = 45509200396792792688546058240 := by
  rw [← show ((([(2, 5), (5711, 1), (435349, 1), (1144212164056845409, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843232 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_2, prime_seventySevenBW_5711, prime_seventySevenBW_435349, prime_seventySevenBW_1144212164056845409]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843233 : Nat.totient 91034550075917321398374843233 = 91034550075917321398374843232 := by
  rw [← show ((([(91034550075917321398374843233, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843233 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_91034550075917321398374843233]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843234 : Nat.totient 91034550075917321398374843234 = 28559855933927623378333094400 := by
  rw [← show ((([(2, 1), (3, 1), (17, 1), (9802867, 1), (91044343351754296201, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843234 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_2, prime_seventySevenBW_3, prime_seventySevenBW_17, prime_seventySevenBW_9802867, prime_seventySevenBW_91044343351754296201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843235 : Nat.totient 91034550075917321398374843235 = 66194655376037476598852895360 := by
  rw [← show ((([(5, 1), (11, 1), (5387, 1), (74977564789, 1), (4097936781539, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843235 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_5, prime_seventySevenBW_11, prime_seventySevenBW_5387, prime_seventySevenBW_74977564789, prime_seventySevenBW_4097936781539]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843236 : Nat.totient 91034550075917321398374843236 = 42694444344101627906128051200 := by
  rw [← show ((([(2, 2), (19, 1), (101, 1), (179527, 1), (66060447363398968993, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843236 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_2, prime_seventySevenBW_19, prime_seventySevenBW_101, prime_seventySevenBW_179527, prime_seventySevenBW_66060447363398968993]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843237 : Nat.totient 91034550075917321398374843237 = 60689700046660437896479700400 := by
  rw [← show ((([(3, 1), (15360165901, 1), (1975554835858264979, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843237 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_3, prime_seventySevenBW_15360165901, prime_seventySevenBW_1975554835858264979]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843238 : Nat.totient 91034550075917321398374843238 = 37669468996747985483664813984 := by
  rw [← show ((([(2, 1), (7, 1), (29, 1), (205523572019, 1), (1090984491661667, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843238 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_2, prime_seventySevenBW_7, prime_seventySevenBW_29, prime_seventySevenBW_205523572019, prime_seventySevenBW_1090984491661667]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843239 : Nat.totient 91034550075917321398374843239 = 91034550075917321398374843238 := by
  rw [← show ((([(91034550075917321398374843239, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843239 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_91034550075917321398374843239]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843240 : Nat.totient 91034550075917321398374843240 = 22350899223701591110978830336 := by
  rw [← show ((([(2, 3), (3, 2), (5, 1), (13, 1), (389, 1), (50004696502052886756737, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843240 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_2, prime_seventySevenBW_3, prime_seventySevenBW_5, prime_seventySevenBW_13, prime_seventySevenBW_389, prime_seventySevenBW_50004696502052886756737]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843241 : Nat.totient 91034550075917321398374843241 = 88097951683281429867625464720 := by
  rw [← show ((([(31, 1), (28509089699, 1), (103005687678927389, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843241 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_31, prime_seventySevenBW_28509089699, prime_seventySevenBW_103005687678927389]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843242 : Nat.totient 91034550075917321398374843242 = 45511066155861793427747211360 := by
  rw [← show ((([(2, 1), (7331, 1), (8422374953, 1), (737188349825647, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843242 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_2, prime_seventySevenBW_7331, prime_seventySevenBW_8422374953, prime_seventySevenBW_737188349825647]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843243 : Nat.totient 91034550075917321398374843243 = 60653525617142441313349516320 := by
  rw [← show ((([(3, 1), (3229, 1), (3491, 1), (2691950697209873905679, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843243 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_3, prime_seventySevenBW_3229, prime_seventySevenBW_3491, prime_seventySevenBW_2691950697209873905679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843244 : Nat.totient 91034550075917321398374843244 = 45517275037958660699187421620 := by
  rw [← show ((([(2, 2), (22758637518979330349593710811, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843244 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_2, prime_seventySevenBW_22758637518979330349593710811]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843245 : Nat.totient 91034550075917321398374843245 = 58001684121329172745640232960 := by
  rw [← show ((([(5, 1), (7, 2), (23, 1), (37, 1), (719, 1), (5087, 1), (29671, 1), (4023349811477, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843245 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_5, prime_seventySevenBW_7, prime_seventySevenBW_23, prime_seventySevenBW_37, prime_seventySevenBW_719, prime_seventySevenBW_5087, prime_seventySevenBW_29671, prime_seventySevenBW_4023349811477]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843246 : Nat.totient 91034550075917321398374843246 = 27585515882502890959465267200 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (41017, 1), (720619, 1), (50419757, 1), (925533121, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843246 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_2, prime_seventySevenBW_3, prime_seventySevenBW_11, prime_seventySevenBW_41017, prime_seventySevenBW_720619, prime_seventySevenBW_50419757, prime_seventySevenBW_925533121]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843247 : Nat.totient 91034550075917321398374843247 = 89751627045617200540154127360 := by
  rw [← show ((([(71, 1), (143687, 1), (748039, 1), (101544217, 1), (117476497, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843247 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_71, prime_seventySevenBW_143687, prime_seventySevenBW_748039, prime_seventySevenBW_101544217, prime_seventySevenBW_117476497]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843248 : Nat.totient 91034550075917321398374843248 = 45517275037957448546586090240 := by
  rw [← show ((([(2, 4), (68699214993041, 1), (82819860173383, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843248 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_2, prime_seventySevenBW_68699214993041, prime_seventySevenBW_82819860173383]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843249 : Nat.totient 91034550075917321398374843249 = 60689700050611547598916562160 := by
  rw [← show ((([(3, 2), (10114950008435257933152760361, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843249 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_3, prime_seventySevenBW_10114950008435257933152760361]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843250 : Nat.totient 91034550075917321398374843250 = 36411273915376915898591054400 := by
  rw [← show ((([(2, 1), (5, 3), (14303, 1), (159621013, 1), (159495722471207, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843250 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_2, prime_seventySevenBW_5, prime_seventySevenBW_14303, prime_seventySevenBW_159621013, prime_seventySevenBW_159495722471207]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843251 : Nat.totient 91034550075917321398374843251 = 84227380329462885600889186048 := by
  rw [← show ((([(17, 1), (59, 1), (90762263286059143966475417, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843251 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_17, prime_seventySevenBW_59, prime_seventySevenBW_90762263286059143966475417]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843252 : Nat.totient 91034550075917321398374843252 = 25740249273415126352439613440 := by
  rw [← show ((([(2, 2), (3, 1), (7, 1), (139, 1), (313, 1), (51627207371, 1), (482490973049, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843252 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_2, prime_seventySevenBW_3, prime_seventySevenBW_7, prime_seventySevenBW_139, prime_seventySevenBW_313, prime_seventySevenBW_51627207371, prime_seventySevenBW_482490973049]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843253 : Nat.totient 91034550075917321398374843253 = 81949525491268554390475776000 := by
  rw [← show ((([(13, 2), (73, 1), (89, 1), (178141801, 1), (465415497110021, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843253 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_13, prime_seventySevenBW_73, prime_seventySevenBW_89, prime_seventySevenBW_178141801, prime_seventySevenBW_465415497110021]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843254 : Nat.totient 91034550075917321398374843254 = 45517275037958660699187421626 := by
  rw [← show ((([(2, 1), (45517275037958660699187421627, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843254 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_2, prime_seventySevenBW_45517275037958660699187421627]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843255 : Nat.totient 91034550075917321398374843255 = 43970832759241859258058001920 := by
  rw [← show ((([(3, 1), (5, 1), (19, 1), (43, 1), (47, 1), (37084505573, 1), (4261893406171, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843255 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_3, prime_seventySevenBW_5, prime_seventySevenBW_19, prime_seventySevenBW_43, prime_seventySevenBW_47, prime_seventySevenBW_37084505573, prime_seventySevenBW_4261893406171]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843256 : Nat.totient 91034550075917321398374843256 = 45453748389076745399558073600 := by
  rw [← show ((([(2, 3), (761, 1), (12239, 1), (915499391, 1), (1334527759063, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843256 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_2, prime_seventySevenBW_761, prime_seventySevenBW_12239, prime_seventySevenBW_915499391, prime_seventySevenBW_1334527759063]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843257 : Nat.totient 91034550075917321398374843257 = 80840678938214196234280320000 := by
  rw [← show ((([(11, 1), (61, 1), (197, 1), (547, 1), (2290213, 1), (549736156734101, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843257 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_11, prime_seventySevenBW_61, prime_seventySevenBW_197, prime_seventySevenBW_547, prime_seventySevenBW_2290213, prime_seventySevenBW_549736156734101]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843258 : Nat.totient 91034550075917321398374843258 = 29246441407913433559361126400 := by
  rw [← show ((([(2, 1), (3, 3), (41, 1), (131, 1), (229, 1), (7297, 1), (187835428241006849, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843258 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_2, prime_seventySevenBW_3, prime_seventySevenBW_41, prime_seventySevenBW_131, prime_seventySevenBW_229, prime_seventySevenBW_7297, prime_seventySevenBW_187835428241006849]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843259 : Nat.totient 91034550075917321398374843259 = 77089472642419604688096502272 := by
  rw [← show ((([(7, 1), (83, 1), (3008569, 1), (309539023, 1), (168249868697, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843259 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_7, prime_seventySevenBW_83, prime_seventySevenBW_3008569, prime_seventySevenBW_309539023, prime_seventySevenBW_168249868697]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843260 : Nat.totient 91034550075917321398374843260 = 36382809986359874503319605248 := by
  rw [← show ((([(2, 2), (5, 1), (1993, 1), (2857, 1), (340634237, 1), (2346769411199, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843260 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_2, prime_seventySevenBW_5, prime_seventySevenBW_1993, prime_seventySevenBW_2857, prime_seventySevenBW_340634237, prime_seventySevenBW_2346769411199]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843261 : Nat.totient 91034550075917321398374843261 = 60031930403201248711794432000 := by
  rw [← show ((([(3, 1), (97, 1), (1871, 1), (167201232183604190930801, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843261 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_3, prime_seventySevenBW_97, prime_seventySevenBW_1871, prime_seventySevenBW_167201232183604190930801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843262 : Nat.totient 91034550075917321398374843262 = 45516284649241805270202863664 := by
  rw [← show ((([(2, 1), (45959, 1), (990388716855428984512009, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843262 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_2, prime_seventySevenBW_45959, prime_seventySevenBW_990388716855428984512009]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843263 : Nat.totient 91034550075917321398374843263 = 89873741220247856001151141920 := by
  rw [← show ((([(109, 1), (277, 1), (3015087936803806226554991, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843263 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_109, prime_seventySevenBW_277, prime_seventySevenBW_3015087936803806226554991]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843264 : Nat.totient 91034550075917321398374843264 = 30344850025305773799458280960 := by
  rw [← show ((([(2, 7), (3, 1), (237069140822701357808267821, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843264 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_2, prime_seventySevenBW_3, prime_seventySevenBW_237069140822701357808267821]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843265 : Nat.totient 91034550075917321398374843265 = 72827640060733857118699874608 := by
  rw [← show ((([(5, 1), (18206910015183464279674968653, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843265 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_5, prime_seventySevenBW_18206910015183464279674968653]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843266 : Nat.totient 91034550075917321398374843266 = 35779303777774736991938902272 := by
  rw [← show ((([(2, 1), (7, 1), (13, 1), (173, 1), (1367, 1), (262255507, 1), (8064837625699, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843266 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_2, prime_seventySevenBW_7, prime_seventySevenBW_13, prime_seventySevenBW_173, prime_seventySevenBW_1367, prime_seventySevenBW_262255507, prime_seventySevenBW_8064837625699]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843267 : Nat.totient 91034550075917321398374843267 = 58596951773004252854126335728 := by
  rw [← show ((([(3, 2), (29, 1), (348791379601215790798371047, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843267 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_3, prime_seventySevenBW_29, prime_seventySevenBW_348791379601215790798371047]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843268 : Nat.totient 91034550075917321398374843268 = 37251989800886883436675050240 := by
  rw [← show ((([(2, 2), (11, 2), (17, 1), (23, 1), (481043256726328556775247, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843268 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_2, prime_seventySevenBW_11, prime_seventySevenBW_17, prime_seventySevenBW_23, prime_seventySevenBW_481043256726328556775247]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843269 : Nat.totient 91034550075917321398374843269 = 91034550075916562273679631296 := by
  rw [← show ((([(149273342996017, 1), (609851352215957, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843269 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_149273342996017, prime_seventySevenBW_609851352215957]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843270 : Nat.totient 91034550075917321398374843270 = 24183576293931901856906673632 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (263, 1), (11537965789089647832493643, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843270 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_2, prime_seventySevenBW_3, prime_seventySevenBW_5, prime_seventySevenBW_263, prime_seventySevenBW_11537965789089647832493643]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843271 : Nat.totient 91034550075917321398374843271 = 91034534757897079348168521000 := by
  rw [← show ((([(5942971, 1), (15318020242050200379301, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843271 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_5942971, prime_seventySevenBW_15318020242050200379301]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843272 : Nat.totient 91034550075917321398374843272 = 44040036290096142076752138240 := by
  rw [← show ((([(2, 3), (31, 1), (5189, 1), (97729, 1), (723848108156616419, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843272 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_2, prime_seventySevenBW_31, prime_seventySevenBW_5189, prime_seventySevenBW_97729, prime_seventySevenBW_723848108156616419]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843273 : Nat.totient 91034550075917321398374843273 = 51997233258868684695599275200 := by
  rw [← show ((([(3, 1), (7, 1), (2311, 1), (3083926231, 1), (608251276365893, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843273 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_3, prime_seventySevenBW_7, prime_seventySevenBW_2311, prime_seventySevenBW_3083926231, prime_seventySevenBW_608251276365893]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843274 : Nat.totient 91034550075917321398374843274 = 42895620584256816112163056560 := by
  rw [← show ((([(2, 1), (19, 1), (191, 1), (178207, 1), (70382473756235746279, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843274 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_2, prime_seventySevenBW_19, prime_seventySevenBW_191, prime_seventySevenBW_178207, prime_seventySevenBW_70382473756235746279]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843275 : Nat.totient 91034550075917321398374843275 = 72827640060733857118699874600 := by
  rw [← show ((([(5, 2), (3641382003036692855934993731, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843275 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_5, prime_seventySevenBW_3641382003036692855934993731]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843276 : Nat.totient 91034550075917321398374843276 = 30318220490475686115094382592 := by
  rw [← show ((([(2, 2), (3, 2), (1187, 1), (31247, 1), (355093, 1), (3372907, 1), (56924369, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843276 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_2, prime_seventySevenBW_3, prime_seventySevenBW_1187, prime_seventySevenBW_31247, prime_seventySevenBW_355093, prime_seventySevenBW_3372907, prime_seventySevenBW_56924369]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843277 : Nat.totient 91034550075917321398374843277 = 90985133260424432816242214400 := by
  rw [← show ((([(1861, 1), (182041, 1), (268714229356493884177, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843277 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_1861, prime_seventySevenBW_182041, prime_seventySevenBW_268714229356493884177]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843278 : Nat.totient 91034550075917321398374843278 = 45517275037958660699187421638 := by
  rw [← show ((([(2, 1), (45517275037958660699187421639, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843278 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_2, prime_seventySevenBW_45517275037958660699187421639]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843279 : Nat.totient 91034550075917321398374843279 = 50879962515732968251771200000 := by
  rw [← show ((([(3, 1), (11, 1), (13, 1), (1051, 1), (201904613157670508935601, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843279 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_3, prime_seventySevenBW_11, prime_seventySevenBW_13, prime_seventySevenBW_1051, prime_seventySevenBW_201904613157670508935601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843280 : Nat.totient 91034550075917321398374843280 = 31010033118183010045791436800 := by
  rw [← show ((([(2, 4), (5, 1), (7, 1), (233, 1), (491, 1), (6841, 1), (1128557, 1), (184050804733, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843280 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_2, prime_seventySevenBW_5, prime_seventySevenBW_7, prime_seventySevenBW_233, prime_seventySevenBW_491, prime_seventySevenBW_6841, prime_seventySevenBW_1128557, prime_seventySevenBW_184050804733]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843281 : Nat.totient 91034550075917321398374843281 = 91034550075917321398374843280 := by
  rw [← show ((([(91034550075917321398374843281, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843281 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_91034550075917321398374843281]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843282 : Nat.totient 91034550075917321398374843282 = 28865287445497380795155127552 := by
  rw [← show ((([(2, 1), (3, 1), (37, 1), (53, 1), (283, 1), (13448563, 1), (2032895660341163, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843282 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_2, prime_seventySevenBW_3, prime_seventySevenBW_37, prime_seventySevenBW_53, prime_seventySevenBW_283, prime_seventySevenBW_13448563, prime_seventySevenBW_2032895660341163]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843283 : Nat.totient 91034550075917321398374843283 = 89675702461486144884838003200 := by
  rw [← show ((([(67, 1), (729649, 1), (1071522341, 1), (1737865754861, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843283 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_67, prime_seventySevenBW_729649, prime_seventySevenBW_1071522341, prime_seventySevenBW_1737865754861]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843284 : Nat.totient 91034550075917321398374843284 = 45517275036952759060717659864 := by
  rw [← show ((([(2, 2), (45250228643, 1), (502950773984652247, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843284 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_2, prime_seventySevenBW_45250228643, prime_seventySevenBW_502950773984652247]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843285 : Nat.totient 91034550075917321398374843285 = 45695774155754577015654822144 := by
  rw [← show ((([(3, 3), (5, 1), (17, 1), (39666470621314736992755923, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843285 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_3, prime_seventySevenBW_5, prime_seventySevenBW_17, prime_seventySevenBW_39666470621314736992755923]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843286 : Nat.totient 91034550075917321398374843286 = 45517112510266735915867155360 := by
  rw [← show ((([(2, 1), (280069, 1), (7531919957, 1), (21577718233171, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843286 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_2, prime_seventySevenBW_280069, prime_seventySevenBW_7531919957, prime_seventySevenBW_21577718233171]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843287 : Nat.totient 91034550075917321398374843287 = 77999520612274972814306783232 := by
  rw [← show ((([(7, 1), (2593, 1), (58630633, 1), (85542336878398889, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843287 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_7, prime_seventySevenBW_2593, prime_seventySevenBW_58630633, prime_seventySevenBW_85542336878398889]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843288 : Nat.totient 91034550075917321398374843288 = 30309440682514801209799040000 := by
  rw [← show ((([(2, 3), (3, 1), (857, 1), (27149501, 1), (163024296471370541, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843288 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_2, prime_seventySevenBW_3, prime_seventySevenBW_857, prime_seventySevenBW_27149501, prime_seventySevenBW_163024296471370541]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843289 : Nat.totient 91034550075917321398374843289 = 91034550075890193407656787556 := by
  rw [← show ((([(3356157660787, 1), (27124634560394947, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843289 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_3356157660787, prime_seventySevenBW_27124634560394947]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843290 : Nat.totient 91034550075917321398374843290 = 32683590560708458389504345600 := by
  rw [← show ((([(2, 1), (5, 1), (11, 1), (79, 1), (45191, 1), (256057, 1), (905311149667643, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843290 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_2, prime_seventySevenBW_5, prime_seventySevenBW_11, prime_seventySevenBW_79, prime_seventySevenBW_45191, prime_seventySevenBW_256057, prime_seventySevenBW_905311149667643]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843291 : Nat.totient 91034550075917321398374843291 = 57694876215057096338824199424 := by
  rw [← show ((([(3, 1), (23, 1), (163, 1), (4314710249, 1), (1875935571851597, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843291 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_3, prime_seventySevenBW_23, prime_seventySevenBW_163, prime_seventySevenBW_4314710249, prime_seventySevenBW_1875935571851597]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843292 : Nat.totient 91034550075917321398374843292 = 41860903309509447792002808000 := by
  rw [← show ((([(2, 2), (13, 1), (271, 1), (16828271, 1), (383878791035889731, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843292 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_2, prime_seventySevenBW_13, prime_seventySevenBW_271, prime_seventySevenBW_16828271, prime_seventySevenBW_383878791035889731]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843293 : Nat.totient 91034550075917321398374843293 = 86243257966658515008986693628 := by
  rw [← show ((([(19, 1), (4791292109258806389388149647, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843293 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_19, prime_seventySevenBW_4791292109258806389388149647]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843294 : Nat.totient 91034550075917321398374843294 = 25999206158264446414541445120 := by
  rw [← show ((([(2, 1), (3, 2), (7, 2), (2441, 1), (3065929, 1), (19124197, 1), (721148299, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843294 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_2, prime_seventySevenBW_3, prime_seventySevenBW_7, prime_seventySevenBW_2441, prime_seventySevenBW_3065929, prime_seventySevenBW_19124197, prime_seventySevenBW_721148299]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843295 : Nat.totient 91034550075917321398374843295 = 72827640060733857118699874632 := by
  rw [← show ((([(5, 1), (18206910015183464279674968659, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843295 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_5, prime_seventySevenBW_18206910015183464279674968659]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843296 : Nat.totient 91034550075917321398374843296 = 43932830941583830910921241600 := by
  rw [← show ((([(2, 5), (29, 1), (2971, 1), (484597, 1), (68135728055607911, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843296 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_2, prime_seventySevenBW_29, prime_seventySevenBW_2971, prime_seventySevenBW_484597, prime_seventySevenBW_68135728055607911]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843297 : Nat.totient 91034550075917321398374843297 = 60689700050611547598916562196 := by
  rw [← show ((([(3, 1), (30344850025305773799458281099, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843297 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_3, prime_seventySevenBW_30344850025305773799458281099]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843298 : Nat.totient 91034550075917321398374843298 = 44458699005859656188865163536 := by
  rw [← show ((([(2, 1), (43, 1), (1279309, 1), (827432058988506289727, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843298 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_2, prime_seventySevenBW_43, prime_seventySevenBW_1279309, prime_seventySevenBW_827432058988506289727]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843299 : Nat.totient 91034550075917321398374843299 = 87697264683182352522251558400 := by
  rw [← show ((([(41, 1), (127, 1), (211, 1), (741017113, 1), (111817036902799, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843299 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_41, prime_seventySevenBW_127, prime_seventySevenBW_211, prime_seventySevenBW_741017113, prime_seventySevenBW_111817036902799]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843300 : Nat.totient 91034550075917321398374843300 = 24275879956371877240187573760 := by
  rw [← show ((([(2, 2), (3, 1), (5, 2), (380066353, 1), (798409272112171787, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843300 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_2, prime_seventySevenBW_3, prime_seventySevenBW_5, prime_seventySevenBW_380066353, prime_seventySevenBW_798409272112171787]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843301 : Nat.totient 91034550075917321398374843301 = 70936013046169341349382994720 := by
  rw [← show ((([(7, 1), (11, 1), (1182266884102822355823049913, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843301 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_7, prime_seventySevenBW_11, prime_seventySevenBW_1182266884102822355823049913]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843302 : Nat.totient 91034550075917321398374843302 = 41928107211774429939138295296 := by
  rw [← show ((([(2, 1), (17, 1), (47, 1), (220123, 1), (7322779, 1), (35341756038997, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843302 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_2, prime_seventySevenBW_17, prime_seventySevenBW_47, prime_seventySevenBW_220123, prime_seventySevenBW_7322779, prime_seventySevenBW_35341756038997]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_seventySevenBW_91034550075917321398374843303 : Nat.totient 91034550075917321398374843303 = 58212215863561176115432366080 := by
  rw [← show ((([(3, 2), (31, 1), (113, 1), (2887510707517915481916289, 1)] : List FactorBlock).map factorBlockValue).prod) = 91034550075917321398374843303 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_seventySevenBW_3, prime_seventySevenBW_31, prime_seventySevenBW_113, prime_seventySevenBW_2887510707517915481916289]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64SeventySevenBW : certifiedKill 3 91034550075917321398374843199 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_seventySevenBW_91034550075917321398374843200, phi_seventySevenBW_91034550075917321398374843201, phi_seventySevenBW_91034550075917321398374843202,
    phi_seventySevenBW_91034550075917321398374843203, phi_seventySevenBW_91034550075917321398374843204, phi_seventySevenBW_91034550075917321398374843205,
    phi_seventySevenBW_91034550075917321398374843206, phi_seventySevenBW_91034550075917321398374843207, phi_seventySevenBW_91034550075917321398374843208,
    phi_seventySevenBW_91034550075917321398374843209, phi_seventySevenBW_91034550075917321398374843210, phi_seventySevenBW_91034550075917321398374843211,
    phi_seventySevenBW_91034550075917321398374843212, phi_seventySevenBW_91034550075917321398374843213, phi_seventySevenBW_91034550075917321398374843214,
    phi_seventySevenBW_91034550075917321398374843215, phi_seventySevenBW_91034550075917321398374843216, phi_seventySevenBW_91034550075917321398374843217,
    phi_seventySevenBW_91034550075917321398374843218, phi_seventySevenBW_91034550075917321398374843219, phi_seventySevenBW_91034550075917321398374843220,
    phi_seventySevenBW_91034550075917321398374843221, phi_seventySevenBW_91034550075917321398374843222, phi_seventySevenBW_91034550075917321398374843223,
    phi_seventySevenBW_91034550075917321398374843224, phi_seventySevenBW_91034550075917321398374843225, phi_seventySevenBW_91034550075917321398374843226,
    phi_seventySevenBW_91034550075917321398374843227, phi_seventySevenBW_91034550075917321398374843228, phi_seventySevenBW_91034550075917321398374843229,
    phi_seventySevenBW_91034550075917321398374843230, phi_seventySevenBW_91034550075917321398374843231, phi_seventySevenBW_91034550075917321398374843232,
    phi_seventySevenBW_91034550075917321398374843233, phi_seventySevenBW_91034550075917321398374843234, phi_seventySevenBW_91034550075917321398374843235,
    phi_seventySevenBW_91034550075917321398374843236, phi_seventySevenBW_91034550075917321398374843237, phi_seventySevenBW_91034550075917321398374843238,
    phi_seventySevenBW_91034550075917321398374843239, phi_seventySevenBW_91034550075917321398374843240, phi_seventySevenBW_91034550075917321398374843241,
    phi_seventySevenBW_91034550075917321398374843242, phi_seventySevenBW_91034550075917321398374843243, phi_seventySevenBW_91034550075917321398374843244,
    phi_seventySevenBW_91034550075917321398374843245, phi_seventySevenBW_91034550075917321398374843246, phi_seventySevenBW_91034550075917321398374843247,
    phi_seventySevenBW_91034550075917321398374843248, phi_seventySevenBW_91034550075917321398374843249, phi_seventySevenBW_91034550075917321398374843250,
    phi_seventySevenBW_91034550075917321398374843251, phi_seventySevenBW_91034550075917321398374843252, phi_seventySevenBW_91034550075917321398374843253,
    phi_seventySevenBW_91034550075917321398374843254, phi_seventySevenBW_91034550075917321398374843255, phi_seventySevenBW_91034550075917321398374843256,
    phi_seventySevenBW_91034550075917321398374843257, phi_seventySevenBW_91034550075917321398374843258, phi_seventySevenBW_91034550075917321398374843259,
    phi_seventySevenBW_91034550075917321398374843260, phi_seventySevenBW_91034550075917321398374843261, phi_seventySevenBW_91034550075917321398374843262,
    phi_seventySevenBW_91034550075917321398374843263, phi_seventySevenBW_91034550075917321398374843264, phi_seventySevenBW_91034550075917321398374843265,
    phi_seventySevenBW_91034550075917321398374843266, phi_seventySevenBW_91034550075917321398374843267, phi_seventySevenBW_91034550075917321398374843268,
    phi_seventySevenBW_91034550075917321398374843269, phi_seventySevenBW_91034550075917321398374843270, phi_seventySevenBW_91034550075917321398374843271,
    phi_seventySevenBW_91034550075917321398374843272, phi_seventySevenBW_91034550075917321398374843273, phi_seventySevenBW_91034550075917321398374843274,
    phi_seventySevenBW_91034550075917321398374843275, phi_seventySevenBW_91034550075917321398374843276, phi_seventySevenBW_91034550075917321398374843277,
    phi_seventySevenBW_91034550075917321398374843278, phi_seventySevenBW_91034550075917321398374843279, phi_seventySevenBW_91034550075917321398374843280,
    phi_seventySevenBW_91034550075917321398374843281, phi_seventySevenBW_91034550075917321398374843282, phi_seventySevenBW_91034550075917321398374843283,
    phi_seventySevenBW_91034550075917321398374843284, phi_seventySevenBW_91034550075917321398374843285, phi_seventySevenBW_91034550075917321398374843286,
    phi_seventySevenBW_91034550075917321398374843287, phi_seventySevenBW_91034550075917321398374843288, phi_seventySevenBW_91034550075917321398374843289,
    phi_seventySevenBW_91034550075917321398374843290, phi_seventySevenBW_91034550075917321398374843291, phi_seventySevenBW_91034550075917321398374843292,
    phi_seventySevenBW_91034550075917321398374843293, phi_seventySevenBW_91034550075917321398374843294, phi_seventySevenBW_91034550075917321398374843295,
    phi_seventySevenBW_91034550075917321398374843296, phi_seventySevenBW_91034550075917321398374843297, phi_seventySevenBW_91034550075917321398374843298,
    phi_seventySevenBW_91034550075917321398374843299, phi_seventySevenBW_91034550075917321398374843300, phi_seventySevenBW_91034550075917321398374843301,
    phi_seventySevenBW_91034550075917321398374843302, phi_seventySevenBW_91034550075917321398374843303]

end TotientTailPeriodKiller
end Erdos249257
