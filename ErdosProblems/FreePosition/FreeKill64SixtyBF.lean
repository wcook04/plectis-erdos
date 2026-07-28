import Erdos249257.DiagonalPincerCertificatesT64

-- Explicit full-window certificate for the earliest successful 60P sweep coordinate.
namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def sixtyBFFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem sixtyBFFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) :
    sixtyBFFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [sixtyBFFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [sixtyBFFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then sixtyBFFastPow a n * sixtyBFFastPow a n * a
        else sixtyBFFastPow a n * sixtyBFFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_sixtyBF_2 : Nat.Prime 2 := by norm_num
private theorem prime_sixtyBF_3 : Nat.Prime 3 := by norm_num
private theorem prime_sixtyBF_5 : Nat.Prime 5 := by norm_num
private theorem prime_sixtyBF_7 : Nat.Prime 7 := by norm_num
private theorem prime_sixtyBF_11 : Nat.Prime 11 := by norm_num
private theorem prime_sixtyBF_13 : Nat.Prime 13 := by norm_num
private theorem prime_sixtyBF_17 : Nat.Prime 17 := by norm_num
private theorem prime_sixtyBF_19 : Nat.Prime 19 := by norm_num
private theorem prime_sixtyBF_23 : Nat.Prime 23 := by norm_num
private theorem prime_sixtyBF_29 : Nat.Prime 29 := by norm_num
private theorem prime_sixtyBF_31 : Nat.Prime 31 := by norm_num
private theorem prime_sixtyBF_37 : Nat.Prime 37 := by norm_num
private theorem prime_sixtyBF_41 : Nat.Prime 41 := by norm_num
private theorem prime_sixtyBF_43 : Nat.Prime 43 := by norm_num
private theorem prime_sixtyBF_47 : Nat.Prime 47 := by norm_num
private theorem prime_sixtyBF_53 : Nat.Prime 53 := by norm_num
private theorem prime_sixtyBF_59 : Nat.Prime 59 := by norm_num
private theorem prime_sixtyBF_61 : Nat.Prime 61 := by norm_num
private theorem prime_sixtyBF_67 : Nat.Prime 67 := by norm_num
private theorem prime_sixtyBF_71 : Nat.Prime 71 := by norm_num
private theorem prime_sixtyBF_73 : Nat.Prime 73 := by norm_num
private theorem prime_sixtyBF_79 : Nat.Prime 79 := by norm_num
private theorem prime_sixtyBF_83 : Nat.Prime 83 := by norm_num
private theorem prime_sixtyBF_89 : Nat.Prime 89 := by norm_num
private theorem prime_sixtyBF_97 : Nat.Prime 97 := by norm_num
private theorem prime_sixtyBF_101 : Nat.Prime 101 := by norm_num
private theorem prime_sixtyBF_103 : Nat.Prime 103 := by norm_num
private theorem prime_sixtyBF_107 : Nat.Prime 107 := by norm_num
private theorem prime_sixtyBF_109 : Nat.Prime 109 := by norm_num
private theorem prime_sixtyBF_113 : Nat.Prime 113 := by norm_num
private theorem prime_sixtyBF_127 : Nat.Prime 127 := by norm_num
private theorem prime_sixtyBF_131 : Nat.Prime 131 := by norm_num
private theorem prime_sixtyBF_137 : Nat.Prime 137 := by norm_num
private theorem prime_sixtyBF_139 : Nat.Prime 139 := by norm_num
private theorem prime_sixtyBF_149 : Nat.Prime 149 := by norm_num
private theorem prime_sixtyBF_163 : Nat.Prime 163 := by norm_num
private theorem prime_sixtyBF_167 : Nat.Prime 167 := by norm_num
private theorem prime_sixtyBF_173 : Nat.Prime 173 := by norm_num
private theorem prime_sixtyBF_179 : Nat.Prime 179 := by norm_num
private theorem prime_sixtyBF_181 : Nat.Prime 181 := by norm_num
private theorem prime_sixtyBF_191 : Nat.Prime 191 := by norm_num
private theorem prime_sixtyBF_193 : Nat.Prime 193 := by norm_num
private theorem prime_sixtyBF_197 : Nat.Prime 197 := by norm_num
private theorem prime_sixtyBF_199 : Nat.Prime 199 := by norm_num
private theorem prime_sixtyBF_211 : Nat.Prime 211 := by norm_num
private theorem prime_sixtyBF_223 : Nat.Prime 223 := by norm_num
private theorem prime_sixtyBF_227 : Nat.Prime 227 := by norm_num
private theorem prime_sixtyBF_229 : Nat.Prime 229 := by norm_num
private theorem prime_sixtyBF_239 : Nat.Prime 239 := by norm_num
private theorem prime_sixtyBF_251 : Nat.Prime 251 := by norm_num
private theorem prime_sixtyBF_263 : Nat.Prime 263 := by norm_num
private theorem prime_sixtyBF_269 : Nat.Prime 269 := by norm_num
private theorem prime_sixtyBF_271 : Nat.Prime 271 := by norm_num
private theorem prime_sixtyBF_277 : Nat.Prime 277 := by norm_num
private theorem prime_sixtyBF_281 : Nat.Prime 281 := by norm_num
private theorem prime_sixtyBF_283 : Nat.Prime 283 := by norm_num
private theorem prime_sixtyBF_313 : Nat.Prime 313 := by norm_num
private theorem prime_sixtyBF_317 : Nat.Prime 317 := by norm_num
private theorem prime_sixtyBF_331 : Nat.Prime 331 := by norm_num
private theorem prime_sixtyBF_337 : Nat.Prime 337 := by norm_num
private theorem prime_sixtyBF_347 : Nat.Prime 347 := by norm_num
private theorem prime_sixtyBF_367 : Nat.Prime 367 := by norm_num
private theorem prime_sixtyBF_373 : Nat.Prime 373 := by norm_num
private theorem prime_sixtyBF_379 : Nat.Prime 379 := by norm_num
private theorem prime_sixtyBF_383 : Nat.Prime 383 := by norm_num
private theorem prime_sixtyBF_389 : Nat.Prime 389 := by norm_num
private theorem prime_sixtyBF_409 : Nat.Prime 409 := by norm_num
private theorem prime_sixtyBF_419 : Nat.Prime 419 := by norm_num
private theorem prime_sixtyBF_431 : Nat.Prime 431 := by norm_num
private theorem prime_sixtyBF_433 : Nat.Prime 433 := by norm_num
private theorem prime_sixtyBF_443 : Nat.Prime 443 := by norm_num
private theorem prime_sixtyBF_457 : Nat.Prime 457 := by norm_num
private theorem prime_sixtyBF_461 : Nat.Prime 461 := by norm_num
private theorem prime_sixtyBF_463 : Nat.Prime 463 := by norm_num
private theorem prime_sixtyBF_467 : Nat.Prime 467 := by norm_num
private theorem prime_sixtyBF_479 : Nat.Prime 479 := by norm_num
private theorem prime_sixtyBF_487 : Nat.Prime 487 := by norm_num
private theorem prime_sixtyBF_499 : Nat.Prime 499 := by norm_num
private theorem prime_sixtyBF_541 : Nat.Prime 541 := by norm_num
private theorem prime_sixtyBF_557 : Nat.Prime 557 := by norm_num
private theorem prime_sixtyBF_569 : Nat.Prime 569 := by norm_num
private theorem prime_sixtyBF_571 : Nat.Prime 571 := by norm_num
private theorem prime_sixtyBF_577 : Nat.Prime 577 := by norm_num
private theorem prime_sixtyBF_607 : Nat.Prime 607 := by norm_num
private theorem prime_sixtyBF_619 : Nat.Prime 619 := by norm_num
private theorem prime_sixtyBF_631 : Nat.Prime 631 := by norm_num
private theorem prime_sixtyBF_653 : Nat.Prime 653 := by norm_num
private theorem prime_sixtyBF_673 : Nat.Prime 673 := by norm_num
private theorem prime_sixtyBF_691 : Nat.Prime 691 := by norm_num
private theorem prime_sixtyBF_701 : Nat.Prime 701 := by norm_num
private theorem prime_sixtyBF_733 : Nat.Prime 733 := by norm_num
private theorem prime_sixtyBF_739 : Nat.Prime 739 := by norm_num
private theorem prime_sixtyBF_751 : Nat.Prime 751 := by norm_num
private theorem prime_sixtyBF_787 : Nat.Prime 787 := by norm_num
private theorem prime_sixtyBF_821 : Nat.Prime 821 := by norm_num
private theorem prime_sixtyBF_827 : Nat.Prime 827 := by norm_num
private theorem prime_sixtyBF_839 : Nat.Prime 839 := by norm_num
private theorem prime_sixtyBF_853 : Nat.Prime 853 := by norm_num
private theorem prime_sixtyBF_863 : Nat.Prime 863 := by norm_num
private theorem prime_sixtyBF_877 : Nat.Prime 877 := by norm_num
private theorem prime_sixtyBF_881 : Nat.Prime 881 := by norm_num
private theorem prime_sixtyBF_883 : Nat.Prime 883 := by norm_num
private theorem prime_sixtyBF_907 : Nat.Prime 907 := by norm_num
private theorem prime_sixtyBF_953 : Nat.Prime 953 := by norm_num
private theorem prime_sixtyBF_967 : Nat.Prime 967 := by norm_num
private theorem prime_sixtyBF_1021 : Nat.Prime 1021 := by norm_num
private theorem prime_sixtyBF_1051 : Nat.Prime 1051 := by norm_num
private theorem prime_sixtyBF_1069 : Nat.Prime 1069 := by norm_num
private theorem prime_sixtyBF_1091 : Nat.Prime 1091 := by norm_num
private theorem prime_sixtyBF_1093 : Nat.Prime 1093 := by norm_num
private theorem prime_sixtyBF_1109 : Nat.Prime 1109 := by norm_num
private theorem prime_sixtyBF_1117 : Nat.Prime 1117 := by norm_num
private theorem prime_sixtyBF_1123 : Nat.Prime 1123 := by norm_num
private theorem prime_sixtyBF_1187 : Nat.Prime 1187 := by norm_num
private theorem prime_sixtyBF_1231 : Nat.Prime 1231 := by norm_num
private theorem prime_sixtyBF_1249 : Nat.Prime 1249 := by norm_num
private theorem prime_sixtyBF_1321 : Nat.Prime 1321 := by norm_num
private theorem prime_sixtyBF_1327 : Nat.Prime 1327 := by norm_num
private theorem prime_sixtyBF_1367 : Nat.Prime 1367 := by norm_num
private theorem prime_sixtyBF_1381 : Nat.Prime 1381 := by norm_num
private theorem prime_sixtyBF_1409 : Nat.Prime 1409 := by norm_num
private theorem prime_sixtyBF_1423 : Nat.Prime 1423 := by norm_num
private theorem prime_sixtyBF_1429 : Nat.Prime 1429 := by norm_num
private theorem prime_sixtyBF_1483 : Nat.Prime 1483 := by norm_num
private theorem prime_sixtyBF_1579 : Nat.Prime 1579 := by norm_num
private theorem prime_sixtyBF_1597 : Nat.Prime 1597 := by norm_num
private theorem prime_sixtyBF_1607 : Nat.Prime 1607 := by norm_num
private theorem prime_sixtyBF_1609 : Nat.Prime 1609 := by norm_num
private theorem prime_sixtyBF_1619 : Nat.Prime 1619 := by norm_num
private theorem prime_sixtyBF_1621 : Nat.Prime 1621 := by norm_num
private theorem prime_sixtyBF_1721 : Nat.Prime 1721 := by norm_num
private theorem prime_sixtyBF_1723 : Nat.Prime 1723 := by norm_num
private theorem prime_sixtyBF_1741 : Nat.Prime 1741 := by norm_num
private theorem prime_sixtyBF_1783 : Nat.Prime 1783 := by norm_num
private theorem prime_sixtyBF_1831 : Nat.Prime 1831 := by norm_num
private theorem prime_sixtyBF_1871 : Nat.Prime 1871 := by norm_num
private theorem prime_sixtyBF_2063 : Nat.Prime 2063 := by norm_num
private theorem prime_sixtyBF_2087 : Nat.Prime 2087 := by norm_num
private theorem prime_sixtyBF_2113 : Nat.Prime 2113 := by norm_num
private theorem prime_sixtyBF_2179 : Nat.Prime 2179 := by norm_num
private theorem prime_sixtyBF_2213 : Nat.Prime 2213 := by norm_num
private theorem prime_sixtyBF_2237 : Nat.Prime 2237 := by norm_num
private theorem prime_sixtyBF_2267 : Nat.Prime 2267 := by norm_num
private theorem prime_sixtyBF_2371 : Nat.Prime 2371 := by norm_num
private theorem prime_sixtyBF_2399 : Nat.Prime 2399 := by norm_num
private theorem prime_sixtyBF_2441 : Nat.Prime 2441 := by norm_num
private theorem prime_sixtyBF_2579 : Nat.Prime 2579 := by norm_num
private theorem prime_sixtyBF_2731 : Nat.Prime 2731 := by norm_num
private theorem prime_sixtyBF_2767 : Nat.Prime 2767 := by norm_num
private theorem prime_sixtyBF_2851 : Nat.Prime 2851 := by norm_num
private theorem prime_sixtyBF_2897 : Nat.Prime 2897 := by norm_num
private theorem prime_sixtyBF_2917 : Nat.Prime 2917 := by norm_num
private theorem prime_sixtyBF_3061 : Nat.Prime 3061 := by norm_num
private theorem prime_sixtyBF_3181 : Nat.Prime 3181 := by norm_num
private theorem prime_sixtyBF_3209 : Nat.Prime 3209 := by norm_num
private theorem prime_sixtyBF_3307 : Nat.Prime 3307 := by norm_num
private theorem prime_sixtyBF_3329 : Nat.Prime 3329 := by norm_num
private theorem prime_sixtyBF_3371 : Nat.Prime 3371 := by norm_num
private theorem prime_sixtyBF_3433 : Nat.Prime 3433 := by norm_num
private theorem prime_sixtyBF_3449 : Nat.Prime 3449 := by norm_num
private theorem prime_sixtyBF_3461 : Nat.Prime 3461 := by norm_num
private theorem prime_sixtyBF_3677 : Nat.Prime 3677 := by norm_num
private theorem prime_sixtyBF_3851 : Nat.Prime 3851 := by norm_num
private theorem prime_sixtyBF_3881 : Nat.Prime 3881 := by norm_num
private theorem prime_sixtyBF_4027 : Nat.Prime 4027 := by norm_num
private theorem prime_sixtyBF_4327 : Nat.Prime 4327 := by norm_num
private theorem prime_sixtyBF_4349 : Nat.Prime 4349 := by norm_num
private theorem prime_sixtyBF_4421 : Nat.Prime 4421 := by norm_num
private theorem prime_sixtyBF_4517 : Nat.Prime 4517 := by norm_num
private theorem prime_sixtyBF_4663 : Nat.Prime 4663 := by norm_num
private theorem prime_sixtyBF_4703 : Nat.Prime 4703 := by norm_num
private theorem prime_sixtyBF_4957 : Nat.Prime 4957 := by norm_num
private theorem prime_sixtyBF_5011 : Nat.Prime 5011 := by norm_num
private theorem prime_sixtyBF_5087 : Nat.Prime 5087 := by norm_num
private theorem prime_sixtyBF_5107 : Nat.Prime 5107 := by norm_num
private theorem prime_sixtyBF_5233 : Nat.Prime 5233 := by norm_num
private theorem prime_sixtyBF_5431 : Nat.Prime 5431 := by norm_num
private theorem prime_sixtyBF_5867 : Nat.Prime 5867 := by norm_num
private theorem prime_sixtyBF_5897 : Nat.Prime 5897 := by norm_num
private theorem prime_sixtyBF_6011 : Nat.Prime 6011 := by norm_num
private theorem prime_sixtyBF_6037 : Nat.Prime 6037 := by norm_num
private theorem prime_sixtyBF_6053 : Nat.Prime 6053 := by norm_num
private theorem prime_sixtyBF_6067 : Nat.Prime 6067 := by norm_num
private theorem prime_sixtyBF_6163 : Nat.Prime 6163 := by norm_num
private theorem prime_sixtyBF_6229 : Nat.Prime 6229 := by norm_num
private theorem prime_sixtyBF_6337 : Nat.Prime 6337 := by norm_num
private theorem prime_sixtyBF_6709 : Nat.Prime 6709 := by norm_num
private theorem prime_sixtyBF_7229 : Nat.Prime 7229 := by norm_num
private theorem prime_sixtyBF_7307 : Nat.Prime 7307 := by norm_num
private theorem prime_sixtyBF_7459 : Nat.Prime 7459 := by norm_num
private theorem prime_sixtyBF_7507 : Nat.Prime 7507 := by norm_num
private theorem prime_sixtyBF_7699 : Nat.Prime 7699 := by norm_num
private theorem prime_sixtyBF_7817 : Nat.Prime 7817 := by norm_num
private theorem prime_sixtyBF_7877 : Nat.Prime 7877 := by norm_num
private theorem prime_sixtyBF_8059 : Nat.Prime 8059 := by norm_num
private theorem prime_sixtyBF_8069 : Nat.Prime 8069 := by norm_num
private theorem prime_sixtyBF_8599 : Nat.Prime 8599 := by norm_num
private theorem prime_sixtyBF_9283 : Nat.Prime 9283 := by norm_num
private theorem prime_sixtyBF_9311 : Nat.Prime 9311 := by norm_num
private theorem prime_sixtyBF_10099 : Nat.Prime 10099 := by norm_num
private theorem prime_sixtyBF_10243 : Nat.Prime 10243 := by norm_num
private theorem prime_sixtyBF_10427 : Nat.Prime 10427 := by norm_num
private theorem prime_sixtyBF_10589 : Nat.Prime 10589 := by norm_num
private theorem prime_sixtyBF_10729 : Nat.Prime 10729 := by norm_num
private theorem prime_sixtyBF_10853 : Nat.Prime 10853 := by norm_num
private theorem prime_sixtyBF_10883 : Nat.Prime 10883 := by norm_num
private theorem prime_sixtyBF_11071 : Nat.Prime 11071 := by norm_num
private theorem prime_sixtyBF_11779 : Nat.Prime 11779 := by norm_num
private theorem prime_sixtyBF_11887 : Nat.Prime 11887 := by norm_num
private theorem prime_sixtyBF_12263 : Nat.Prime 12263 := by norm_num
private theorem prime_sixtyBF_12457 : Nat.Prime 12457 := by norm_num
private theorem prime_sixtyBF_12553 : Nat.Prime 12553 := by norm_num
private theorem prime_sixtyBF_13063 : Nat.Prime 13063 := by norm_num
private theorem prime_sixtyBF_13463 : Nat.Prime 13463 := by norm_num
private theorem prime_sixtyBF_13681 : Nat.Prime 13681 := by norm_num
private theorem prime_sixtyBF_13759 : Nat.Prime 13759 := by norm_num
private theorem prime_sixtyBF_13997 : Nat.Prime 13997 := by norm_num
private theorem prime_sixtyBF_14741 : Nat.Prime 14741 := by norm_num
private theorem prime_sixtyBF_14767 : Nat.Prime 14767 := by norm_num
private theorem prime_sixtyBF_14969 : Nat.Prime 14969 := by norm_num
private theorem prime_sixtyBF_16981 : Nat.Prime 16981 := by norm_num
private theorem prime_sixtyBF_16993 : Nat.Prime 16993 := by norm_num
private theorem prime_sixtyBF_17239 : Nat.Prime 17239 := by norm_num
private theorem prime_sixtyBF_17383 : Nat.Prime 17383 := by norm_num
private theorem prime_sixtyBF_17449 : Nat.Prime 17449 := by norm_num
private theorem prime_sixtyBF_18593 : Nat.Prime 18593 := by norm_num
private theorem prime_sixtyBF_19477 : Nat.Prime 19477 := by norm_num
private theorem prime_sixtyBF_19753 : Nat.Prime 19753 := by norm_num
private theorem prime_sixtyBF_19843 : Nat.Prime 19843 := by norm_num
private theorem prime_sixtyBF_20231 : Nat.Prime 20231 := by norm_num
private theorem prime_sixtyBF_20599 : Nat.Prime 20599 := by norm_num
private theorem prime_sixtyBF_20639 : Nat.Prime 20639 := by norm_num
private theorem prime_sixtyBF_22153 : Nat.Prime 22153 := by norm_num
private theorem prime_sixtyBF_22541 : Nat.Prime 22541 := by norm_num
private theorem prime_sixtyBF_22621 : Nat.Prime 22621 := by norm_num
private theorem prime_sixtyBF_23063 : Nat.Prime 23063 := by norm_num
private theorem prime_sixtyBF_23497 : Nat.Prime 23497 := by norm_num
private theorem prime_sixtyBF_25841 : Nat.Prime 25841 := by norm_num
private theorem prime_sixtyBF_28111 : Nat.Prime 28111 := by norm_num
private theorem prime_sixtyBF_28621 : Nat.Prime 28621 := by norm_num
private theorem prime_sixtyBF_29387 : Nat.Prime 29387 := by norm_num
private theorem prime_sixtyBF_29789 : Nat.Prime 29789 := by norm_num
private theorem prime_sixtyBF_30223 : Nat.Prime 30223 := by norm_num
private theorem prime_sixtyBF_30553 : Nat.Prime 30553 := by norm_num
private theorem prime_sixtyBF_31849 : Nat.Prime 31849 := by norm_num
private theorem prime_sixtyBF_31859 : Nat.Prime 31859 := by norm_num
private theorem prime_sixtyBF_32561 : Nat.Prime 32561 := by norm_num
private theorem prime_sixtyBF_32831 : Nat.Prime 32831 := by norm_num
private theorem prime_sixtyBF_32983 : Nat.Prime 32983 := by norm_num
private theorem prime_sixtyBF_35323 : Nat.Prime 35323 := by norm_num
private theorem prime_sixtyBF_36587 : Nat.Prime 36587 := by norm_num
private theorem prime_sixtyBF_38261 : Nat.Prime 38261 := by norm_num
private theorem prime_sixtyBF_40099 : Nat.Prime 40099 := by norm_num
private theorem prime_sixtyBF_40459 : Nat.Prime 40459 := by norm_num
private theorem prime_sixtyBF_44279 : Nat.Prime 44279 := by norm_num
private theorem prime_sixtyBF_45869 : Nat.Prime 45869 := by norm_num
private theorem prime_sixtyBF_46327 : Nat.Prime 46327 := by norm_num
private theorem prime_sixtyBF_46601 : Nat.Prime 46601 := by norm_num
private theorem prime_sixtyBF_51349 : Nat.Prime 51349 := by norm_num
private theorem prime_sixtyBF_52583 : Nat.Prime 52583 := by norm_num
private theorem prime_sixtyBF_57119 : Nat.Prime 57119 := by norm_num
private theorem prime_sixtyBF_58231 : Nat.Prime 58231 := by norm_num
private theorem prime_sixtyBF_67943 : Nat.Prime 67943 := by norm_num
private theorem prime_sixtyBF_74323 : Nat.Prime 74323 := by norm_num
private theorem prime_sixtyBF_80789 : Nat.Prime 80789 := by norm_num
private theorem prime_sixtyBF_82351 : Nat.Prime 82351 := by norm_num
private theorem prime_sixtyBF_87151 : Nat.Prime 87151 := by norm_num
private theorem prime_sixtyBF_89003 : Nat.Prime 89003 := by norm_num
private theorem prime_sixtyBF_91303 : Nat.Prime 91303 := by norm_num
private theorem prime_sixtyBF_91969 : Nat.Prime 91969 := by norm_num
private theorem prime_sixtyBF_92461 : Nat.Prime 92461 := by norm_num
private theorem prime_sixtyBF_96013 : Nat.Prime 96013 := by norm_num
private theorem prime_sixtyBF_106979 : Nat.Prime 106979 := by norm_num
private theorem prime_sixtyBF_109451 : Nat.Prime 109451 := by norm_num
private theorem prime_sixtyBF_109537 : Nat.Prime 109537 := by norm_num
private theorem prime_sixtyBF_111959 : Nat.Prime 111959 := by norm_num
private theorem prime_sixtyBF_114757 : Nat.Prime 114757 := by norm_num
private theorem prime_sixtyBF_117223 : Nat.Prime 117223 := by norm_num
private theorem prime_sixtyBF_123121 : Nat.Prime 123121 := by norm_num
private theorem prime_sixtyBF_132263 : Nat.Prime 132263 := by norm_num
private theorem prime_sixtyBF_132541 : Nat.Prime 132541 := by norm_num
private theorem prime_sixtyBF_132707 : Nat.Prime 132707 := by norm_num
private theorem prime_sixtyBF_143519 : Nat.Prime 143519 := by norm_num
private theorem prime_sixtyBF_147451 : Nat.Prime 147451 := by norm_num
private theorem prime_sixtyBF_155047 : Nat.Prime 155047 := by norm_num
private theorem prime_sixtyBF_158551 : Nat.Prime 158551 := by norm_num
private theorem prime_sixtyBF_184081 : Nat.Prime 184081 := by norm_num
private theorem prime_sixtyBF_185551 : Nat.Prime 185551 := by norm_num
private theorem prime_sixtyBF_188249 : Nat.Prime 188249 := by norm_num
private theorem prime_sixtyBF_193379 : Nat.Prime 193379 := by norm_num
private theorem prime_sixtyBF_193619 : Nat.Prime 193619 := by norm_num
private theorem prime_sixtyBF_198377 : Nat.Prime 198377 := by norm_num
private theorem prime_sixtyBF_203279 : Nat.Prime 203279 := by norm_num
private theorem prime_sixtyBF_257437 : Nat.Prime 257437 := by norm_num
private theorem prime_sixtyBF_258721 : Nat.Prime 258721 := by norm_num
private theorem prime_sixtyBF_268883 : Nat.Prime 268883 := by norm_num
private theorem prime_sixtyBF_274019 : Nat.Prime 274019 := by norm_num
private theorem prime_sixtyBF_313883 : Nat.Prime 313883 := by norm_num
private theorem prime_sixtyBF_318301 : Nat.Prime 318301 := by norm_num
private theorem prime_sixtyBF_325411 : Nat.Prime 325411 := by norm_num
private theorem prime_sixtyBF_372709 : Nat.Prime 372709 := by norm_num
private theorem prime_sixtyBF_386227 : Nat.Prime 386227 := by norm_num
private theorem prime_sixtyBF_386777 : Nat.Prime 386777 := by norm_num
private theorem prime_sixtyBF_391249 : Nat.Prime 391249 := by norm_num
private theorem prime_sixtyBF_414451 : Nat.Prime 414451 := by norm_num
private theorem prime_sixtyBF_481699 : Nat.Prime 481699 := by norm_num
private theorem prime_sixtyBF_508091 : Nat.Prime 508091 := by norm_num
private theorem prime_sixtyBF_537773 : Nat.Prime 537773 := by norm_num
private theorem prime_sixtyBF_573481 : Nat.Prime 573481 := by norm_num
private theorem prime_sixtyBF_580711 : Nat.Prime 580711 := by norm_num
private theorem prime_sixtyBF_599243 : Nat.Prime 599243 := by norm_num
private theorem prime_sixtyBF_599783 : Nat.Prime 599783 := by norm_num
private theorem prime_sixtyBF_617333 : Nat.Prime 617333 := by norm_num
private theorem prime_sixtyBF_620393 : Nat.Prime 620393 := by norm_num
private theorem prime_sixtyBF_623719 : Nat.Prime 623719 := by norm_num
private theorem prime_sixtyBF_626261 : Nat.Prime 626261 := by norm_num
private theorem prime_sixtyBF_654743 : Nat.Prime 654743 := by norm_num
private theorem prime_sixtyBF_670951 : Nat.Prime 670951 := by norm_num
private theorem prime_sixtyBF_761443 : Nat.Prime 761443 := by norm_num
private theorem prime_sixtyBF_765881 : Nat.Prime 765881 := by norm_num
private theorem prime_sixtyBF_777209 : Nat.Prime 777209 := by norm_num
private theorem prime_sixtyBF_821507 : Nat.Prime 821507 := by norm_num
private theorem prime_sixtyBF_826393 : Nat.Prime 826393 := by norm_num
private theorem prime_sixtyBF_848791 : Nat.Prime 848791 := by norm_num
private theorem prime_sixtyBF_865661 : Nat.Prime 865661 := by norm_num
private theorem prime_sixtyBF_919427 : Nat.Prime 919427 := by norm_num
private theorem prime_sixtyBF_927439 : Nat.Prime 927439 := by norm_num
private theorem prime_sixtyBF_942509 : Nat.Prime 942509 := by norm_num
private theorem prime_sixtyBF_1017353 : Nat.Prime 1017353 := by norm_num
private theorem prime_sixtyBF_1020751 : Nat.Prime 1020751 := by norm_num
private theorem prime_sixtyBF_1054853 : Nat.Prime 1054853 := by norm_num
private theorem prime_sixtyBF_1060993 : Nat.Prime 1060993 := by norm_num
private theorem prime_sixtyBF_1108201 : Nat.Prime 1108201 := by norm_num
private theorem prime_sixtyBF_1151221 : Nat.Prime 1151221 := by norm_num
private theorem prime_sixtyBF_1325083 : Nat.Prime 1325083 := by norm_num
private theorem prime_sixtyBF_1385507 : Nat.Prime 1385507 := by norm_num
private theorem prime_sixtyBF_1486403 : Nat.Prime 1486403 := by norm_num
private theorem prime_sixtyBF_1605553 : Nat.Prime 1605553 := by norm_num
private theorem prime_sixtyBF_1703833 : Nat.Prime 1703833 := by norm_num
private theorem prime_sixtyBF_1718429 : Nat.Prime 1718429 := by norm_num
private theorem prime_sixtyBF_1736347 : Nat.Prime 1736347 := by norm_num
private theorem prime_sixtyBF_1740853 : Nat.Prime 1740853 := by norm_num
private theorem prime_sixtyBF_2102267 : Nat.Prime 2102267 := by norm_num
private theorem prime_sixtyBF_2134961 : Nat.Prime 2134961 := by norm_num
private theorem prime_sixtyBF_2278831 : Nat.Prime 2278831 := by norm_num
private theorem prime_sixtyBF_2281823 : Nat.Prime 2281823 := by norm_num
private theorem prime_sixtyBF_2357923 : Nat.Prime 2357923 := by norm_num
private theorem prime_sixtyBF_2478023 : Nat.Prime 2478023 := by norm_num
private theorem prime_sixtyBF_2539661 : Nat.Prime 2539661 := by norm_num
private theorem prime_sixtyBF_2552531 : Nat.Prime 2552531 := by norm_num
private theorem prime_sixtyBF_2574947 : Nat.Prime 2574947 := by norm_num
private theorem prime_sixtyBF_2623207 : Nat.Prime 2623207 := by norm_num
private theorem prime_sixtyBF_2775137 : Nat.Prime 2775137 := by norm_num
private theorem prime_sixtyBF_2840681 : Nat.Prime 2840681 := by norm_num
private theorem prime_sixtyBF_3307417 : Nat.Prime 3307417 := by norm_num
private theorem prime_sixtyBF_3381787 : Nat.Prime 3381787 := by norm_num
private theorem prime_sixtyBF_3652367 : Nat.Prime 3652367 := by norm_num
private theorem prime_sixtyBF_3896861 : Nat.Prime 3896861 := by norm_num
private theorem prime_sixtyBF_3919327 : Nat.Prime 3919327 := by norm_num
private theorem prime_sixtyBF_4018837 : Nat.Prime 4018837 := by norm_num
private theorem prime_sixtyBF_4055221 : Nat.Prime 4055221 := by norm_num
private theorem prime_sixtyBF_4098793 : Nat.Prime 4098793 := by norm_num
private theorem prime_sixtyBF_4181867 : Nat.Prime 4181867 := by norm_num
private theorem prime_sixtyBF_4224139 : Nat.Prime 4224139 := by norm_num
private theorem prime_sixtyBF_4318163 : Nat.Prime 4318163 := by norm_num
private theorem prime_sixtyBF_4538041 : Nat.Prime 4538041 := by norm_num
private theorem prime_sixtyBF_4582147 : Nat.Prime 4582147 := by norm_num
private theorem prime_sixtyBF_4766297 : Nat.Prime 4766297 := by norm_num
private theorem prime_sixtyBF_5069873 : Nat.Prime 5069873 := by norm_num
private theorem prime_sixtyBF_5234767 : Nat.Prime 5234767 := by norm_num
private theorem prime_sixtyBF_5867731 : Nat.Prime 5867731 := by norm_num
private theorem prime_sixtyBF_5970301 : Nat.Prime 5970301 := by norm_num
private theorem prime_sixtyBF_6109799 : Nat.Prime 6109799 := by norm_num
private theorem prime_sixtyBF_6888683 : Nat.Prime 6888683 := by norm_num
private theorem prime_sixtyBF_7166261 : Nat.Prime 7166261 := by norm_num
private theorem prime_sixtyBF_7179553 : Nat.Prime 7179553 := by norm_num
private theorem prime_sixtyBF_7247897 : Nat.Prime 7247897 := by norm_num
private theorem prime_sixtyBF_7615039 : Nat.Prime 7615039 := by norm_num
private theorem prime_sixtyBF_7921687 : Nat.Prime 7921687 := by norm_num
private theorem prime_sixtyBF_8033939 : Nat.Prime 8033939 := by norm_num
private theorem prime_sixtyBF_8155451 : Nat.Prime 8155451 := by norm_num
private theorem prime_sixtyBF_8171327 : Nat.Prime 8171327 := by norm_num
private theorem prime_sixtyBF_8483521 : Nat.Prime 8483521 := by norm_num
private theorem prime_sixtyBF_8526173 : Nat.Prime 8526173 := by norm_num
private theorem prime_sixtyBF_8566543 : Nat.Prime 8566543 := by norm_num
private theorem prime_sixtyBF_8890243 : Nat.Prime 8890243 := by norm_num
private theorem prime_sixtyBF_9093017 : Nat.Prime 9093017 := by norm_num
private theorem prime_sixtyBF_9472129 : Nat.Prime 9472129 := by norm_num
private theorem prime_sixtyBF_9839449 : Nat.Prime 9839449 := by norm_num
private theorem prime_sixtyBF_9840293 : Nat.Prime 9840293 := by norm_num
private theorem prime_sixtyBF_9886237 : Nat.Prime 9886237 := by norm_num
private theorem prime_sixtyBF_10042931 : Nat.Prime 10042931 := by norm_num
private theorem prime_sixtyBF_10357973 : Nat.Prime 10357973 := by norm_num
private theorem prime_sixtyBF_10839817 : Nat.Prime 10839817 := by norm_num
private theorem prime_sixtyBF_12150031 : Nat.Prime 12150031 := by norm_num
private theorem prime_sixtyBF_13195753 : Nat.Prime 13195753 := by norm_num
private theorem prime_sixtyBF_16019131 : Nat.Prime 16019131 := by norm_num
private theorem prime_sixtyBF_16086797 : Nat.Prime 16086797 := by norm_num
private theorem prime_sixtyBF_20405767 : Nat.Prime 20405767 := by norm_num
private theorem prime_sixtyBF_20675593 : Nat.Prime 20675593 := by norm_num
private theorem prime_sixtyBF_20930603 : Nat.Prime 20930603 := by norm_num
private theorem prime_sixtyBF_20987359 : Nat.Prime 20987359 := by norm_num
private theorem prime_sixtyBF_22143217 : Nat.Prime 22143217 := by norm_num
private theorem prime_sixtyBF_22278941 : Nat.Prime 22278941 := by norm_num
private theorem prime_sixtyBF_23509721 : Nat.Prime 23509721 := by norm_num
private theorem prime_sixtyBF_23665997 : Nat.Prime 23665997 := by norm_num
private theorem prime_sixtyBF_23796599 : Nat.Prime 23796599 := by norm_num
private theorem prime_sixtyBF_24633913 : Nat.Prime 24633913 := by norm_num
private theorem prime_sixtyBF_25104743 : Nat.Prime 25104743 := by norm_num
private theorem prime_sixtyBF_25537217 : Nat.Prime 25537217 := by norm_num
private theorem prime_sixtyBF_25609457 : Nat.Prime 25609457 := by norm_num
private theorem prime_sixtyBF_26356633 : Nat.Prime 26356633 := by norm_num
private theorem prime_sixtyBF_26809681 : Nat.Prime 26809681 := by norm_num
private theorem prime_sixtyBF_26986489 : Nat.Prime 26986489 := by norm_num

private theorem prime_sixtyBF_33208961 : Nat.Prime 33208961 := by
  apply lucas_primality 33208961 (3 : ZMod 33208961)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (5, 1), (19, 1), (2731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (5, 1), (19, 1), (2731, 1)] : List FactorBlock).map factorBlockValue).prod) = 33208961 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_5
      · exact prime_sixtyBF_19
      · exact prime_sixtyBF_2731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 33208961) ^ 16604480 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 33208961) ^ 6641792 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 33208961) ^ 1747840 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 33208961) ^ 12160 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_33295711 : Nat.Prime 33295711 := by
  apply lucas_primality 33295711 (7 : ZMod 33295711)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (158551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (158551, 1)] : List FactorBlock).map factorBlockValue).prod) = 33295711 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_5
      · exact prime_sixtyBF_7
      · exact prime_sixtyBF_158551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 33295711) ^ 16647855 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (7 : ZMod 33295711) ^ 11098570 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (7 : ZMod 33295711) ^ 6659142 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (7 : ZMod 33295711) ^ 4756530 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (7 : ZMod 33295711) ^ 210 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_35322167 : Nat.Prime 35322167 := by
  apply lucas_primality 35322167 (5 : ZMod 35322167)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (1605553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (1605553, 1)] : List FactorBlock).map factorBlockValue).prod) = 35322167 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_11
      · exact prime_sixtyBF_1605553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 35322167) ^ 17661083 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 35322167) ^ 3211106 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 35322167) ^ 22 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_37236119 : Nat.Prime 37236119 := by
  apply lucas_primality 37236119 (7 : ZMod 37236119)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (577, 1), (787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (577, 1), (787, 1)] : List FactorBlock).map factorBlockValue).prod) = 37236119 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_41
      · exact prime_sixtyBF_577
      · exact prime_sixtyBF_787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 37236119) ^ 18618059 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (7 : ZMod 37236119) ^ 908198 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (7 : ZMod 37236119) ^ 64534 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (7 : ZMod 37236119) ^ 47314 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_37888517 : Nat.Prime 37888517 := by
  apply lucas_primality 37888517 (2 : ZMod 37888517)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (9472129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (9472129, 1)] : List FactorBlock).map factorBlockValue).prod) = 37888517 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_9472129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 37888517) ^ 18944258 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 37888517) ^ 4 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_37944649 : Nat.Prime 37944649 := by
  apply lucas_primality 37944649 (11 : ZMod 37944649)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (7, 1), (79, 1), (953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (7, 1), (79, 1), (953, 1)] : List FactorBlock).map factorBlockValue).prod) = 37944649 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_7
      · exact prime_sixtyBF_79
      · exact prime_sixtyBF_953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 37944649) ^ 18972324 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (11 : ZMod 37944649) ^ 12648216 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (11 : ZMod 37944649) ^ 5420664 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (11 : ZMod 37944649) ^ 480312 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (11 : ZMod 37944649) ^ 39816 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_41861207 : Nat.Prime 41861207 := by
  apply lucas_primality 41861207 (5 : ZMod 41861207)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (20930603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (20930603, 1)] : List FactorBlock).map factorBlockValue).prod) = 41861207 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_20930603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 41861207) ^ 20930603 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 41861207) ^ 2 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_41919061 : Nat.Prime 41919061 := by
  apply lucas_primality 41919061 (2 : ZMod 41919061)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (431, 1), (1621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (431, 1), (1621, 1)] : List FactorBlock).map factorBlockValue).prod) = 41919061 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_5
      · exact prime_sixtyBF_431
      · exact prime_sixtyBF_1621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 41919061) ^ 20959530 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 41919061) ^ 13973020 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 41919061) ^ 8383812 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 41919061) ^ 97260 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 41919061) ^ 25860 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_47593199 : Nat.Prime 47593199 := by
  apply lucas_primality 47593199 (11 : ZMod 47593199)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23796599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23796599, 1)] : List FactorBlock).map factorBlockValue).prod) = 47593199 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_23796599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (11 : ZMod 47593199) ^ 23796599 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (11 : ZMod 47593199) ^ 2 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_47729419 : Nat.Prime 47729419 := by
  apply lucas_primality 47729419 (26 : ZMod 47729419)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 2), (29, 1), (2267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 2), (29, 1), (2267, 1)] : List FactorBlock).map factorBlockValue).prod) = 47729419 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_11
      · exact prime_sixtyBF_29
      · exact prime_sixtyBF_2267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (26 : ZMod 47729419) ^ 23864709 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (26 : ZMod 47729419) ^ 15909806 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (26 : ZMod 47729419) ^ 4339038 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (26 : ZMod 47729419) ^ 1645842 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (26 : ZMod 47729419) ^ 21054 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_52768283 : Nat.Prime 52768283 := by
  apply lucas_primality 52768283 (5 : ZMod 52768283)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (19, 1), (198377, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (19, 1), (198377, 1)] : List FactorBlock).map factorBlockValue).prod) = 52768283 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_7
      · exact prime_sixtyBF_19
      · exact prime_sixtyBF_198377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 52768283) ^ 26384141 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 52768283) ^ 7538326 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 52768283) ^ 2777278 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 52768283) ^ 266 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_55959049 : Nat.Prime 55959049 := by
  apply lucas_primality 55959049 (14 : ZMod 55959049)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (777209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (777209, 1)] : List FactorBlock).map factorBlockValue).prod) = 55959049 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_777209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (14 : ZMod 55959049) ^ 27979524 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (14 : ZMod 55959049) ^ 18653016 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (14 : ZMod 55959049) ^ 72 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_58631429 : Nat.Prime 58631429 := by
  apply lucas_primality 58631429 (2 : ZMod 58631429)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1579, 1), (9283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1579, 1), (9283, 1)] : List FactorBlock).map factorBlockValue).prod) = 58631429 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_1579
      · exact prime_sixtyBF_9283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 58631429) ^ 29315714 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 58631429) ^ 37132 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 58631429) ^ 6316 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_62371901 : Nat.Prime 62371901 := by
  apply lucas_primality 62371901 (2 : ZMod 62371901)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (623719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (623719, 1)] : List FactorBlock).map factorBlockValue).prod) = 62371901 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_5
      · exact prime_sixtyBF_623719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 62371901) ^ 31185950 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 62371901) ^ 12474380 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 62371901) ^ 100 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_65287927 : Nat.Prime 65287927 := by
  apply lucas_primality 65287927 (3 : ZMod 65287927)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (149, 1), (2213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (149, 1), (2213, 1)] : List FactorBlock).map factorBlockValue).prod) = 65287927 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_11
      · exact prime_sixtyBF_149
      · exact prime_sixtyBF_2213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 65287927) ^ 32643963 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 65287927) ^ 21762642 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 65287927) ^ 5935266 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 65287927) ^ 438174 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 65287927) ^ 29502 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_67784903 : Nat.Prime 67784903 := by
  apply lucas_primality 67784903 (5 : ZMod 67784903)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (131, 1), (258721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (131, 1), (258721, 1)] : List FactorBlock).map factorBlockValue).prod) = 67784903 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_131
      · exact prime_sixtyBF_258721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 67784903) ^ 33892451 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 67784903) ^ 517442 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 67784903) ^ 262 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_70715233 : Nat.Prime 70715233 := by
  apply lucas_primality 70715233 (5 : ZMod 70715233)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (7, 2), (5011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (7, 2), (5011, 1)] : List FactorBlock).map factorBlockValue).prod) = 70715233 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_7
      · exact prime_sixtyBF_5011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 70715233) ^ 35357616 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 70715233) ^ 23571744 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 70715233) ^ 10102176 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 70715233) ^ 14112 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_70978223 : Nat.Prime 70978223 := by
  apply lucas_primality 70978223 (7 : ZMod 70978223)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (5069873, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (5069873, 1)] : List FactorBlock).map factorBlockValue).prod) = 70978223 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_7
      · exact prime_sixtyBF_5069873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 70978223) ^ 35489111 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (7 : ZMod 70978223) ^ 10139746 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (7 : ZMod 70978223) ^ 14 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_71299531 : Nat.Prime 71299531 := by
  apply lucas_primality 71299531 (7 : ZMod 71299531)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (17, 1), (46601, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (17, 1), (46601, 1)] : List FactorBlock).map factorBlockValue).prod) = 71299531 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_5
      · exact prime_sixtyBF_17
      · exact prime_sixtyBF_46601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 71299531) ^ 35649765 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (7 : ZMod 71299531) ^ 23766510 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (7 : ZMod 71299531) ^ 14259906 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (7 : ZMod 71299531) ^ 4194090 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (7 : ZMod 71299531) ^ 1530 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_72118003 : Nat.Prime 72118003 := by
  apply lucas_primality 72118003 (5 : ZMod 72118003)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (181, 1), (6037, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (181, 1), (6037, 1)] : List FactorBlock).map factorBlockValue).prod) = 72118003 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_11
      · exact prime_sixtyBF_181
      · exact prime_sixtyBF_6037
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 72118003) ^ 36059001 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 72118003) ^ 24039334 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 72118003) ^ 6556182 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 72118003) ^ 398442 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 72118003) ^ 11946 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_72649541 : Nat.Prime 72649541 := by
  apply lucas_primality 72649541 (3 : ZMod 72649541)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (19, 1), (41, 1), (4663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (19, 1), (41, 1), (4663, 1)] : List FactorBlock).map factorBlockValue).prod) = 72649541 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_5
      · exact prime_sixtyBF_19
      · exact prime_sixtyBF_41
      · exact prime_sixtyBF_4663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 72649541) ^ 36324770 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 72649541) ^ 14529908 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 72649541) ^ 3823660 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 72649541) ^ 1771940 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 72649541) ^ 15580 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_96657259 : Nat.Prime 96657259 := by
  apply lucas_primality 96657259 (3 : ZMod 96657259)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (181, 1), (89003, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (181, 1), (89003, 1)] : List FactorBlock).map factorBlockValue).prod) = 96657259 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_181
      · exact prime_sixtyBF_89003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 96657259) ^ 48328629 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 96657259) ^ 32219086 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 96657259) ^ 534018 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 96657259) ^ 1086 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_98067923 : Nat.Prime 98067923 := by
  apply lucas_primality 98067923 (2 : ZMod 98067923)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1069, 1), (45869, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1069, 1), (45869, 1)] : List FactorBlock).map factorBlockValue).prod) = 98067923 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_1069
      · exact prime_sixtyBF_45869
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 98067923) ^ 49033961 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 98067923) ^ 91738 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 98067923) ^ 2138 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_100925401 : Nat.Prime 100925401 := by
  apply lucas_primality 100925401 (13 : ZMod 100925401)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 2), (59, 1), (2851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 2), (59, 1), (2851, 1)] : List FactorBlock).map factorBlockValue).prod) = 100925401 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_5
      · exact prime_sixtyBF_59
      · exact prime_sixtyBF_2851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 100925401) ^ 50462700 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (13 : ZMod 100925401) ^ 33641800 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (13 : ZMod 100925401) ^ 20185080 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (13 : ZMod 100925401) ^ 1710600 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (13 : ZMod 100925401) ^ 35400 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_105536567 : Nat.Prime 105536567 := by
  apply lucas_primality 105536567 (5 : ZMod 105536567)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (52768283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (52768283, 1)] : List FactorBlock).map factorBlockValue).prod) = 105536567 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_52768283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 105536567) ^ 52768283 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 105536567) ^ 2 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_118831217 : Nat.Prime 118831217 := by
  apply lucas_primality 118831217 (3 : ZMod 118831217)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (1060993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (1060993, 1)] : List FactorBlock).map factorBlockValue).prod) = 118831217 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_7
      · exact prime_sixtyBF_1060993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 118831217) ^ 59415608 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 118831217) ^ 16975888 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 118831217) ^ 112 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_123297259 : Nat.Prime 123297259 := by
  apply lucas_primality 123297259 (2 : ZMod 123297259)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (1423, 1), (2063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (1423, 1), (2063, 1)] : List FactorBlock).map factorBlockValue).prod) = 123297259 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_7
      · exact prime_sixtyBF_1423
      · exact prime_sixtyBF_2063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 123297259) ^ 61648629 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 123297259) ^ 41099086 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 123297259) ^ 17613894 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 123297259) ^ 86646 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 123297259) ^ 59766 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_124072723 : Nat.Prime 124072723 := by
  apply lucas_primality 124072723 (2 : ZMod 124072723)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (765881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (765881, 1)] : List FactorBlock).map factorBlockValue).prod) = 124072723 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_765881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 124072723) ^ 62036361 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 124072723) ^ 41357574 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 124072723) ^ 162 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_136919059 : Nat.Prime 136919059 := by
  apply lucas_primality 136919059 (2 : ZMod 136919059)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (59, 1), (386777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (59, 1), (386777, 1)] : List FactorBlock).map factorBlockValue).prod) = 136919059 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_59
      · exact prime_sixtyBF_386777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 136919059) ^ 68459529 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 136919059) ^ 45639686 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 136919059) ^ 2320662 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 136919059) ^ 354 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_145299083 : Nat.Prime 145299083 := by
  apply lucas_primality 145299083 (2 : ZMod 145299083)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (72649541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (72649541, 1)] : List FactorBlock).map factorBlockValue).prod) = 145299083 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_72649541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 145299083) ^ 72649541 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 145299083) ^ 2 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_165101491 : Nat.Prime 165101491 := by
  apply lucas_primality 165101491 (2 : ZMod 165101491)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 5), (5, 1), (67943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 5), (5, 1), (67943, 1)] : List FactorBlock).map factorBlockValue).prod) = 165101491 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_5
      · exact prime_sixtyBF_67943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 165101491) ^ 82550745 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 165101491) ^ 55033830 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 165101491) ^ 33020298 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 165101491) ^ 2430 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_175549579 : Nat.Prime 175549579 := by
  apply lucas_primality 175549579 (17 : ZMod 175549579)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1723, 1), (16981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1723, 1), (16981, 1)] : List FactorBlock).map factorBlockValue).prod) = 175549579 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_1723
      · exact prime_sixtyBF_16981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 175549579) ^ 87774789 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (17 : ZMod 175549579) ^ 58516526 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (17 : ZMod 175549579) ^ 101886 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (17 : ZMod 175549579) ^ 10338 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_179641277 : Nat.Prime 179641277 := by
  apply lucas_primality 179641277 (2 : ZMod 179641277)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (373, 1), (6337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (373, 1), (6337, 1)] : List FactorBlock).map factorBlockValue).prod) = 179641277 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_19
      · exact prime_sixtyBF_373
      · exact prime_sixtyBF_6337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 179641277) ^ 89820638 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 179641277) ^ 9454804 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 179641277) ^ 481612 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 179641277) ^ 28348 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_189345041 : Nat.Prime 189345041 := by
  apply lucas_primality 189345041 (3 : ZMod 189345041)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (173, 1), (13681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (173, 1), (13681, 1)] : List FactorBlock).map factorBlockValue).prod) = 189345041 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_5
      · exact prime_sixtyBF_173
      · exact prime_sixtyBF_13681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 189345041) ^ 94672520 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 189345041) ^ 37869008 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 189345041) ^ 1094480 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 189345041) ^ 13840 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_208823009 : Nat.Prime 208823009 := by
  apply lucas_primality 208823009 (3 : ZMod 208823009)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (61, 1), (106979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (61, 1), (106979, 1)] : List FactorBlock).map factorBlockValue).prod) = 208823009 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_61
      · exact prime_sixtyBF_106979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 208823009) ^ 104411504 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 208823009) ^ 3423328 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 208823009) ^ 1952 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_221534591 : Nat.Prime 221534591 := by
  apply lucas_primality 221534591 (11 : ZMod 221534591)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (733, 1), (30223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (733, 1), (30223, 1)] : List FactorBlock).map factorBlockValue).prod) = 221534591 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_5
      · exact prime_sixtyBF_733
      · exact prime_sixtyBF_30223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 221534591) ^ 110767295 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (11 : ZMod 221534591) ^ 44306918 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (11 : ZMod 221534591) ^ 302230 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (11 : ZMod 221534591) ^ 7330 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_221807237 : Nat.Prime 221807237 := by
  apply lucas_primality 221807237 (2 : ZMod 221807237)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (7921687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (7921687, 1)] : List FactorBlock).map factorBlockValue).prod) = 221807237 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_7
      · exact prime_sixtyBF_7921687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 221807237) ^ 110903618 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 221807237) ^ 31686748 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 221807237) ^ 28 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_225606083 : Nat.Prime 225606083 := by
  apply lucas_primality 225606083 (2 : ZMod 225606083)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (17, 1), (113, 1), (4517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (17, 1), (113, 1), (4517, 1)] : List FactorBlock).map factorBlockValue).prod) = 225606083 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_13
      · exact prime_sixtyBF_17
      · exact prime_sixtyBF_113
      · exact prime_sixtyBF_4517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 225606083) ^ 112803041 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 225606083) ^ 17354314 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 225606083) ^ 13270946 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 225606083) ^ 1996514 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 225606083) ^ 49946 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_228471293 : Nat.Prime 228471293 := by
  apply lucas_primality 228471293 (2 : ZMod 228471293)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (101, 1), (80789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (101, 1), (80789, 1)] : List FactorBlock).map factorBlockValue).prod) = 228471293 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_7
      · exact prime_sixtyBF_101
      · exact prime_sixtyBF_80789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 228471293) ^ 114235646 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 228471293) ^ 32638756 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 228471293) ^ 2262092 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 228471293) ^ 2828 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_236167033 : Nat.Prime 236167033 := by
  apply lucas_primality 236167033 (5 : ZMod 236167033)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (9840293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (9840293, 1)] : List FactorBlock).map factorBlockValue).prod) = 236167033 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_9840293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 236167033) ^ 118083516 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 236167033) ^ 78722344 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 236167033) ^ 24 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_279926593 : Nat.Prime 279926593 := by
  apply lucas_primality 279926593 (10 : ZMod 279926593)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (11, 1), (132541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (11, 1), (132541, 1)] : List FactorBlock).map factorBlockValue).prod) = 279926593 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_11
      · exact prime_sixtyBF_132541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 279926593) ^ 139963296 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (10 : ZMod 279926593) ^ 93308864 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (10 : ZMod 279926593) ^ 25447872 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (10 : ZMod 279926593) ^ 2112 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_351640271 : Nat.Prime 351640271 := by
  apply lucas_primality 351640271 (11 : ZMod 351640271)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (73, 1), (481699, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (73, 1), (481699, 1)] : List FactorBlock).map factorBlockValue).prod) = 351640271 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_5
      · exact prime_sixtyBF_73
      · exact prime_sixtyBF_481699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 351640271) ^ 175820135 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (11 : ZMod 351640271) ^ 70328054 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (11 : ZMod 351640271) ^ 4816990 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (11 : ZMod 351640271) ^ 730 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_358886551 : Nat.Prime 358886551 := by
  apply lucas_primality 358886551 (3 : ZMod 358886551)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (11, 1), (199, 1), (1093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (11, 1), (199, 1), (1093, 1)] : List FactorBlock).map factorBlockValue).prod) = 358886551 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_5
      · exact prime_sixtyBF_11
      · exact prime_sixtyBF_199
      · exact prime_sixtyBF_1093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 358886551) ^ 179443275 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 358886551) ^ 119628850 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 358886551) ^ 71777310 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 358886551) ^ 32626050 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 358886551) ^ 1803450 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 358886551) ^ 328350 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_367470361 : Nat.Prime 367470361 := by
  apply lucas_primality 367470361 (28 : ZMod 367470361)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (1020751, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (1020751, 1)] : List FactorBlock).map factorBlockValue).prod) = 367470361 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_5
      · exact prime_sixtyBF_1020751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (28 : ZMod 367470361) ^ 183735180 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (28 : ZMod 367470361) ^ 122490120 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (28 : ZMod 367470361) ^ 73494072 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (28 : ZMod 367470361) ^ 360 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_382076273 : Nat.Prime 382076273 := by
  apply lucas_primality 382076273 (3 : ZMod 382076273)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3181, 1), (7507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3181, 1), (7507, 1)] : List FactorBlock).map factorBlockValue).prod) = 382076273 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3181
      · exact prime_sixtyBF_7507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 382076273) ^ 191038136 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 382076273) ^ 120112 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 382076273) ^ 50896 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_386629037 : Nat.Prime 386629037 := by
  apply lucas_primality 386629037 (2 : ZMod 386629037)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (96657259, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (96657259, 1)] : List FactorBlock).map factorBlockValue).prod) = 386629037 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_96657259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 386629037) ^ 193314518 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 386629037) ^ 4 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_419788093 : Nat.Prime 419788093 := by
  apply lucas_primality 419788093 (2 : ZMod 419788093)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (61, 1), (573481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (61, 1), (573481, 1)] : List FactorBlock).map factorBlockValue).prod) = 419788093 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_61
      · exact prime_sixtyBF_573481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 419788093) ^ 209894046 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 419788093) ^ 139929364 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 419788093) ^ 6881772 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 419788093) ^ 732 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_452854081 : Nat.Prime 452854081 := by
  apply lucas_primality 452854081 (23 : ZMod 452854081)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (5, 1), (7, 2), (3209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (5, 1), (7, 2), (3209, 1)] : List FactorBlock).map factorBlockValue).prod) = 452854081 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_5
      · exact prime_sixtyBF_7
      · exact prime_sixtyBF_3209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 452854081) ^ 226427040 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (23 : ZMod 452854081) ^ 150951360 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (23 : ZMod 452854081) ^ 90570816 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (23 : ZMod 452854081) ^ 64693440 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (23 : ZMod 452854081) ^ 141120 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_574363039 : Nat.Prime 574363039 := by
  apply lucas_primality 574363039 (6 : ZMod 574363039)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (29, 1), (143519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (29, 1), (143519, 1)] : List FactorBlock).map factorBlockValue).prod) = 574363039 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_23
      · exact prime_sixtyBF_29
      · exact prime_sixtyBF_143519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 574363039) ^ 287181519 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (6 : ZMod 574363039) ^ 191454346 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (6 : ZMod 574363039) ^ 24972306 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (6 : ZMod 574363039) ^ 19805622 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (6 : ZMod 574363039) ^ 4002 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_644963491 : Nat.Prime 644963491 := by
  apply lucas_primality 644963491 (3 : ZMod 644963491)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7166261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7166261, 1)] : List FactorBlock).map factorBlockValue).prod) = 644963491 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_5
      · exact prime_sixtyBF_7166261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 644963491) ^ 322481745 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 644963491) ^ 214987830 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 644963491) ^ 128992698 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 644963491) ^ 90 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_741168581 : Nat.Prime 741168581 := by
  apply lucas_primality 741168581 (2 : ZMod 741168581)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (331, 1), (111959, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (331, 1), (111959, 1)] : List FactorBlock).map factorBlockValue).prod) = 741168581 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_5
      · exact prime_sixtyBF_331
      · exact prime_sixtyBF_111959
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 741168581) ^ 370584290 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 741168581) ^ 148233716 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 741168581) ^ 2239180 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 741168581) ^ 6620 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_764141549 : Nat.Prime 764141549 := by
  apply lucas_primality 764141549 (2 : ZMod 764141549)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5867, 1), (32561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5867, 1), (32561, 1)] : List FactorBlock).map factorBlockValue).prod) = 764141549 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_5867
      · exact prime_sixtyBF_32561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 764141549) ^ 382070774 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 764141549) ^ 130244 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 764141549) ^ 23468 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_778926529 : Nat.Prime 778926529 := by
  apply lucas_primality 778926529 (7 : ZMod 778926529)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (41, 1), (32983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (41, 1), (32983, 1)] : List FactorBlock).map factorBlockValue).prod) = 778926529 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_41
      · exact prime_sixtyBF_32983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 778926529) ^ 389463264 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (7 : ZMod 778926529) ^ 259642176 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (7 : ZMod 778926529) ^ 18998208 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (7 : ZMod 778926529) ^ 23616 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_837527069 : Nat.Prime 837527069 := by
  apply lucas_primality 837527069 (2 : ZMod 837527069)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (19, 1), (67, 1), (23497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (19, 1), (67, 1), (23497, 1)] : List FactorBlock).map factorBlockValue).prod) = 837527069 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_7
      · exact prime_sixtyBF_19
      · exact prime_sixtyBF_67
      · exact prime_sixtyBF_23497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 837527069) ^ 418763534 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 837527069) ^ 119646724 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 837527069) ^ 44080372 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 837527069) ^ 12500404 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 837527069) ^ 35644 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_900860633 : Nat.Prime 900860633 := by
  apply lucas_primality 900860633 (3 : ZMod 900860633)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (16086797, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (16086797, 1)] : List FactorBlock).map factorBlockValue).prod) = 900860633 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_7
      · exact prime_sixtyBF_16086797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 900860633) ^ 450430316 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 900860633) ^ 128694376 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 900860633) ^ 56 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_985101443 : Nat.Prime 985101443 := by
  apply lucas_primality 985101443 (2 : ZMod 985101443)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (37888517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (37888517, 1)] : List FactorBlock).map factorBlockValue).prod) = 985101443 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_13
      · exact prime_sixtyBF_37888517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 985101443) ^ 492550721 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 985101443) ^ 75777034 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 985101443) ^ 26 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_1056882569 : Nat.Prime 1056882569 := by
  apply lucas_primality 1056882569 (6 : ZMod 1056882569)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 2), (23, 1), (117223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 2), (23, 1), (117223, 1)] : List FactorBlock).map factorBlockValue).prod) = 1056882569 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_7
      · exact prime_sixtyBF_23
      · exact prime_sixtyBF_117223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 1056882569) ^ 528441284 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (6 : ZMod 1056882569) ^ 150983224 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (6 : ZMod 1056882569) ^ 45951416 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (6 : ZMod 1056882569) ^ 9016 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_1067547697 : Nat.Prime 1067547697 := by
  apply lucas_primality 1067547697 (5 : ZMod 1067547697)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (1871, 1), (11887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (1871, 1), (11887, 1)] : List FactorBlock).map factorBlockValue).prod) = 1067547697 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_1871
      · exact prime_sixtyBF_11887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1067547697) ^ 533773848 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1067547697) ^ 355849232 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1067547697) ^ 570576 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1067547697) ^ 89808 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_1119706373 : Nat.Prime 1119706373 := by
  apply lucas_primality 1119706373 (2 : ZMod 1119706373)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (279926593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (279926593, 1)] : List FactorBlock).map factorBlockValue).prod) = 1119706373 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_279926593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 1119706373) ^ 559853186 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1119706373) ^ 4 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_1140911501 : Nat.Prime 1140911501 := by
  apply lucas_primality 1140911501 (2 : ZMod 1140911501)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 3), (2281823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 3), (2281823, 1)] : List FactorBlock).map factorBlockValue).prod) = 1140911501 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_5
      · exact prime_sixtyBF_2281823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1140911501) ^ 570455750 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1140911501) ^ 228182300 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1140911501) ^ 500 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_1344528233 : Nat.Prime 1344528233 := by
  apply lucas_primality 1344528233 (3 : ZMod 1344528233)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17, 1), (9886237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17, 1), (9886237, 1)] : List FactorBlock).map factorBlockValue).prod) = 1344528233 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_17
      · exact prime_sixtyBF_9886237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1344528233) ^ 672264116 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1344528233) ^ 79089896 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1344528233) ^ 136 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_1438619579 : Nat.Prime 1438619579 := by
  apply lucas_primality 1438619579 (2 : ZMod 1438619579)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 2), (67, 1), (83, 1), (1069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 2), (67, 1), (83, 1), (1069, 1)] : List FactorBlock).map factorBlockValue).prod) = 1438619579 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_11
      · exact prime_sixtyBF_67
      · exact prime_sixtyBF_83
      · exact prime_sixtyBF_1069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1438619579) ^ 719309789 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1438619579) ^ 130783598 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1438619579) ^ 21471934 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1438619579) ^ 17332766 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1438619579) ^ 1345762 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_1466288821 : Nat.Prime 1466288821 := by
  apply lucas_primality 1466288821 (2 : ZMod 1466288821)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (43, 1), (389, 1), (487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (43, 1), (389, 1), (487, 1)] : List FactorBlock).map factorBlockValue).prod) = 1466288821 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_5
      · exact prime_sixtyBF_43
      · exact prime_sixtyBF_389
      · exact prime_sixtyBF_487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1466288821) ^ 733144410 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1466288821) ^ 488762940 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1466288821) ^ 293257764 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1466288821) ^ 34099740 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1466288821) ^ 3769380 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1466288821) ^ 3010860 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_1514760329 : Nat.Prime 1514760329 := by
  apply lucas_primality 1514760329 (3 : ZMod 1514760329)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (189345041, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (189345041, 1)] : List FactorBlock).map factorBlockValue).prod) = 1514760329 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_189345041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 1514760329) ^ 757380164 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1514760329) ^ 8 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_1966163113 : Nat.Prime 1966163113 := by
  apply lucas_primality 1966163113 (7 : ZMod 1966163113)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (29, 1), (313883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (29, 1), (313883, 1)] : List FactorBlock).map factorBlockValue).prod) = 1966163113 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_29
      · exact prime_sixtyBF_313883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 1966163113) ^ 983081556 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (7 : ZMod 1966163113) ^ 655387704 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (7 : ZMod 1966163113) ^ 67798728 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (7 : ZMod 1966163113) ^ 6264 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_1970202887 : Nat.Prime 1970202887 := by
  apply lucas_primality 1970202887 (5 : ZMod 1970202887)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (985101443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (985101443, 1)] : List FactorBlock).map factorBlockValue).prod) = 1970202887 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_985101443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 1970202887) ^ 985101443 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1970202887) ^ 2 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_2053678469 : Nat.Prime 2053678469 := by
  apply lucas_primality 2053678469 (2 : ZMod 2053678469)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (2767, 1), (185551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (2767, 1), (185551, 1)] : List FactorBlock).map factorBlockValue).prod) = 2053678469 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_2767
      · exact prime_sixtyBF_185551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2053678469) ^ 1026839234 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2053678469) ^ 742204 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2053678469) ^ 11068 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_2176108141 : Nat.Prime 2176108141 := by
  apply lucas_primality 2176108141 (2 : ZMod 2176108141)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (1609, 1), (22541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (1609, 1), (22541, 1)] : List FactorBlock).map factorBlockValue).prod) = 2176108141 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_5
      · exact prime_sixtyBF_1609
      · exact prime_sixtyBF_22541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2176108141) ^ 1088054070 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2176108141) ^ 725369380 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2176108141) ^ 435221628 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2176108141) ^ 1352460 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2176108141) ^ 96540 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_2370187399 : Nat.Prime 2370187399 := by
  apply lucas_primality 2370187399 (13 : ZMod 2370187399)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (31, 1), (181, 1), (3061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (31, 1), (181, 1), (3061, 1)] : List FactorBlock).map factorBlockValue).prod) = 2370187399 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_23
      · exact prime_sixtyBF_31
      · exact prime_sixtyBF_181
      · exact prime_sixtyBF_3061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 2370187399) ^ 1185093699 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (13 : ZMod 2370187399) ^ 790062466 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (13 : ZMod 2370187399) ^ 103051626 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (13 : ZMod 2370187399) ^ 76457658 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (13 : ZMod 2370187399) ^ 13094958 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (13 : ZMod 2370187399) ^ 774318 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_2469871931 : Nat.Prime 2469871931 := by
  apply lucas_primality 2469871931 (2 : ZMod 2469871931)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (89, 1), (2775137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (89, 1), (2775137, 1)] : List FactorBlock).map factorBlockValue).prod) = 2469871931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_5
      · exact prime_sixtyBF_89
      · exact prime_sixtyBF_2775137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2469871931) ^ 1234935965 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2469871931) ^ 493974386 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2469871931) ^ 27751370 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2469871931) ^ 890 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_2514059767 : Nat.Prime 2514059767 := by
  apply lucas_primality 2514059767 (3 : ZMod 2514059767)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (337, 1), (414451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (337, 1), (414451, 1)] : List FactorBlock).map factorBlockValue).prod) = 2514059767 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_337
      · exact prime_sixtyBF_414451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2514059767) ^ 1257029883 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 2514059767) ^ 838019922 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 2514059767) ^ 7460118 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 2514059767) ^ 6066 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_2781545761 : Nat.Prime 2781545761 := by
  apply lucas_primality 2781545761 (23 : ZMod 2781545761)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (5, 1), (7, 2), (79, 1), (499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (5, 1), (7, 2), (79, 1), (499, 1)] : List FactorBlock).map factorBlockValue).prod) = 2781545761 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_5
      · exact prime_sixtyBF_7
      · exact prime_sixtyBF_79
      · exact prime_sixtyBF_499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 2781545761) ^ 1390772880 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (23 : ZMod 2781545761) ^ 927181920 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (23 : ZMod 2781545761) ^ 556309152 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (23 : ZMod 2781545761) ^ 397363680 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (23 : ZMod 2781545761) ^ 35209440 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (23 : ZMod 2781545761) ^ 5574240 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_2824064351 : Nat.Prime 2824064351 := by
  apply lucas_primality 2824064351 (11 : ZMod 2824064351)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (31, 1), (79, 1), (23063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (31, 1), (79, 1), (23063, 1)] : List FactorBlock).map factorBlockValue).prod) = 2824064351 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_5
      · exact prime_sixtyBF_31
      · exact prime_sixtyBF_79
      · exact prime_sixtyBF_23063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 2824064351) ^ 1412032175 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (11 : ZMod 2824064351) ^ 564812870 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (11 : ZMod 2824064351) ^ 91098850 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (11 : ZMod 2824064351) ^ 35747650 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (11 : ZMod 2824064351) ^ 122450 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_2979558367 : Nat.Prime 2979558367 := by
  apply lucas_primality 2979558367 (3 : ZMod 2979558367)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (16019131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (16019131, 1)] : List FactorBlock).map factorBlockValue).prod) = 2979558367 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_31
      · exact prime_sixtyBF_16019131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2979558367) ^ 1489779183 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 2979558367) ^ 993186122 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 2979558367) ^ 96114786 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 2979558367) ^ 186 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_3069282977 : Nat.Prime 3069282977 := by
  apply lucas_primality 3069282977 (3 : ZMod 3069282977)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (29, 1), (3307417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (29, 1), (3307417, 1)] : List FactorBlock).map factorBlockValue).prod) = 3069282977 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_29
      · exact prime_sixtyBF_3307417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 3069282977) ^ 1534641488 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 3069282977) ^ 105837344 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 3069282977) ^ 928 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_3087650833 : Nat.Prime 3087650833 := by
  apply lucas_primality 3087650833 (5 : ZMod 3087650833)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (7, 1), (2113, 1), (4349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (7, 1), (2113, 1), (4349, 1)] : List FactorBlock).map factorBlockValue).prod) = 3087650833 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_7
      · exact prime_sixtyBF_2113
      · exact prime_sixtyBF_4349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 3087650833) ^ 1543825416 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 3087650833) ^ 1029216944 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 3087650833) ^ 441092976 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 3087650833) ^ 1461264 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 3087650833) ^ 709968 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_3398715337 : Nat.Prime 3398715337 := by
  apply lucas_primality 3398715337 (7 : ZMod 3398715337)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (23, 1), (41, 1), (263, 1), (571, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (23, 1), (41, 1), (263, 1), (571, 1)] : List FactorBlock).map factorBlockValue).prod) = 3398715337 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_23
      · exact prime_sixtyBF_41
      · exact prime_sixtyBF_263
      · exact prime_sixtyBF_571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 3398715337) ^ 1699357668 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (7 : ZMod 3398715337) ^ 1132905112 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (7 : ZMod 3398715337) ^ 147770232 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (7 : ZMod 3398715337) ^ 82895496 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (7 : ZMod 3398715337) ^ 12922872 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (7 : ZMod 3398715337) ^ 5952216 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_3621393409 : Nat.Prime 3621393409 := by
  apply lucas_primality 3621393409 (11 : ZMod 3621393409)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 10), (3, 1), (541, 1), (2179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 10), (3, 1), (541, 1), (2179, 1)] : List FactorBlock).map factorBlockValue).prod) = 3621393409 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_541
      · exact prime_sixtyBF_2179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 3621393409) ^ 1810696704 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (11 : ZMod 3621393409) ^ 1207131136 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (11 : ZMod 3621393409) ^ 6693888 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (11 : ZMod 3621393409) ^ 1661952 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_3662191163 : Nat.Prime 3662191163 := by
  apply lucas_primality 3662191163 (2 : ZMod 3662191163)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (103, 1), (2539661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (103, 1), (2539661, 1)] : List FactorBlock).map factorBlockValue).prod) = 3662191163 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_7
      · exact prime_sixtyBF_103
      · exact prime_sixtyBF_2539661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3662191163) ^ 1831095581 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 3662191163) ^ 523170166 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 3662191163) ^ 35555254 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 3662191163) ^ 1442 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_4197246653 : Nat.Prime 4197246653 := by
  apply lucas_primality 4197246653 (2 : ZMod 4197246653)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (229, 1), (4582147, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (229, 1), (4582147, 1)] : List FactorBlock).map factorBlockValue).prod) = 4197246653 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_229
      · exact prime_sixtyBF_4582147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4197246653) ^ 2098623326 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 4197246653) ^ 18328588 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 4197246653) ^ 916 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_4243657991 : Nat.Prime 4243657991 := by
  apply lucas_primality 4243657991 (17 : ZMod 4243657991)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (13, 1), (631, 1), (4703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (13, 1), (631, 1), (4703, 1)] : List FactorBlock).map factorBlockValue).prod) = 4243657991 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_5
      · exact prime_sixtyBF_11
      · exact prime_sixtyBF_13
      · exact prime_sixtyBF_631
      · exact prime_sixtyBF_4703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 4243657991) ^ 2121828995 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (17 : ZMod 4243657991) ^ 848731598 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (17 : ZMod 4243657991) ^ 385787090 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (17 : ZMod 4243657991) ^ 326435230 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (17 : ZMod 4243657991) ^ 6725290 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (17 : ZMod 4243657991) ^ 902330 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_4697809387 : Nat.Prime 4697809387 := by
  apply lucas_primality 4697809387 (2 : ZMod 4697809387)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (67, 1), (508091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (67, 1), (508091, 1)] : List FactorBlock).map factorBlockValue).prod) = 4697809387 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_23
      · exact prime_sixtyBF_67
      · exact prime_sixtyBF_508091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4697809387) ^ 2348904693 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 4697809387) ^ 1565936462 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 4697809387) ^ 204252582 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 4697809387) ^ 70116558 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 4697809387) ^ 9246 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_4939743863 : Nat.Prime 4939743863 := by
  apply lucas_primality 4939743863 (5 : ZMod 4939743863)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2469871931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2469871931, 1)] : List FactorBlock).map factorBlockValue).prod) = 4939743863 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_2469871931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 4939743863) ^ 2469871931 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 4939743863) ^ 2 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_5278301201 : Nat.Prime 5278301201 := by
  apply lucas_primality 5278301201 (6 : ZMod 5278301201)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 2), (13195753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 2), (13195753, 1)] : List FactorBlock).map factorBlockValue).prod) = 5278301201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_5
      · exact prime_sixtyBF_13195753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 5278301201) ^ 2639150600 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (6 : ZMod 5278301201) ^ 1055660240 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (6 : ZMod 5278301201) ^ 400 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_5865758159 : Nat.Prime 5865758159 := by
  apply lucas_primality 5865758159 (7 : ZMod 5865758159)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (225606083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (225606083, 1)] : List FactorBlock).map factorBlockValue).prod) = 5865758159 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_13
      · exact prime_sixtyBF_225606083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 5865758159) ^ 2932879079 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (7 : ZMod 5865758159) ^ 451212166 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (7 : ZMod 5865758159) ^ 26 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_7626409709 : Nat.Prime 7626409709 := by
  apply lucas_primality 7626409709 (2 : ZMod 7626409709)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (131, 1), (167, 1), (87151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (131, 1), (167, 1), (87151, 1)] : List FactorBlock).map factorBlockValue).prod) = 7626409709 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_131
      · exact prime_sixtyBF_167
      · exact prime_sixtyBF_87151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7626409709) ^ 3813204854 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 7626409709) ^ 58216868 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 7626409709) ^ 45667124 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 7626409709) ^ 87508 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_8797732927 : Nat.Prime 8797732927 := by
  apply lucas_primality 8797732927 (7 : ZMod 8797732927)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1466288821, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1466288821, 1)] : List FactorBlock).map factorBlockValue).prod) = 8797732927 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_1466288821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 8797732927) ^ 4398866463 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (7 : ZMod 8797732927) ^ 2932577642 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (7 : ZMod 8797732927) ^ 6 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_10365144877 : Nat.Prime 10365144877 := by
  apply lucas_primality 10365144877 (2 : ZMod 10365144877)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (71, 1), (4055221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (71, 1), (4055221, 1)] : List FactorBlock).map factorBlockValue).prod) = 10365144877 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_71
      · exact prime_sixtyBF_4055221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 10365144877) ^ 5182572438 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 10365144877) ^ 3455048292 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 10365144877) ^ 145987956 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 10365144877) ^ 2556 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_11802036469 : Nat.Prime 11802036469 := by
  apply lucas_primality 11802036469 (2 : ZMod 11802036469)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (41, 1), (3851, 1), (6229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (41, 1), (3851, 1), (6229, 1)] : List FactorBlock).map factorBlockValue).prod) = 11802036469 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_41
      · exact prime_sixtyBF_3851
      · exact prime_sixtyBF_6229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 11802036469) ^ 5901018234 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 11802036469) ^ 3934012156 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 11802036469) ^ 287854548 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 11802036469) ^ 3064668 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 11802036469) ^ 1894692 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_11857249571 : Nat.Prime 11857249571 := by
  apply lucas_primality 11857249571 (2 : ZMod 11857249571)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (23, 1), (43, 1), (53, 1), (22621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (23, 1), (43, 1), (53, 1), (22621, 1)] : List FactorBlock).map factorBlockValue).prod) = 11857249571 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_5
      · exact prime_sixtyBF_23
      · exact prime_sixtyBF_43
      · exact prime_sixtyBF_53
      · exact prime_sixtyBF_22621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 11857249571) ^ 5928624785 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 11857249571) ^ 2371449914 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 11857249571) ^ 515532590 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 11857249571) ^ 275749990 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 11857249571) ^ 223721690 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 11857249571) ^ 524170 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_13776857323 : Nat.Prime 13776857323 := by
  apply lucas_primality 13776857323 (2 : ZMod 13776857323)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (281, 1), (8171327, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (281, 1), (8171327, 1)] : List FactorBlock).map factorBlockValue).prod) = 13776857323 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_281
      · exact prime_sixtyBF_8171327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 13776857323) ^ 6888428661 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 13776857323) ^ 4592285774 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 13776857323) ^ 49027962 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 13776857323) ^ 1686 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_14012573941 : Nat.Prime 14012573941 := by
  apply lucas_primality 14012573941 (2 : ZMod 14012573941)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (5, 1), (1429, 1), (6053, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (5, 1), (1429, 1), (6053, 1)] : List FactorBlock).map factorBlockValue).prod) = 14012573941 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_5
      · exact prime_sixtyBF_1429
      · exact prime_sixtyBF_6053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 14012573941) ^ 7006286970 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 14012573941) ^ 4670857980 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 14012573941) ^ 2802514788 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 14012573941) ^ 9805860 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 14012573941) ^ 2314980 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_14485573637 : Nat.Prime 14485573637 := by
  apply lucas_primality 14485573637 (2 : ZMod 14485573637)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3621393409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3621393409, 1)] : List FactorBlock).map factorBlockValue).prod) = 14485573637 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3621393409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 14485573637) ^ 7242786818 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 14485573637) ^ 4 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_15170842751 : Nat.Prime 15170842751 := by
  apply lucas_primality 15170842751 (7 : ZMod 15170842751)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 3), (7, 1), (1109, 1), (7817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 3), (7, 1), (1109, 1), (7817, 1)] : List FactorBlock).map factorBlockValue).prod) = 15170842751 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_5
      · exact prime_sixtyBF_7
      · exact prime_sixtyBF_1109
      · exact prime_sixtyBF_7817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 15170842751) ^ 7585421375 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (7 : ZMod 15170842751) ^ 3034168550 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (7 : ZMod 15170842751) ^ 2167263250 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (7 : ZMod 15170842751) ^ 13679750 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (7 : ZMod 15170842751) ^ 1940750 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_17722382539 : Nat.Prime 17722382539 := by
  apply lucas_primality 17722382539 (2 : ZMod 17722382539)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (3677, 1), (114757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (3677, 1), (114757, 1)] : List FactorBlock).map factorBlockValue).prod) = 17722382539 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_7
      · exact prime_sixtyBF_3677
      · exact prime_sixtyBF_114757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 17722382539) ^ 8861191269 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 17722382539) ^ 5907460846 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 17722382539) ^ 2531768934 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 17722382539) ^ 4819794 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 17722382539) ^ 154434 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_19457504483 : Nat.Prime 19457504483 := by
  apply lucas_primality 19457504483 (2 : ZMod 19457504483)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (431, 1), (1736347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (431, 1), (1736347, 1)] : List FactorBlock).map factorBlockValue).prod) = 19457504483 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_13
      · exact prime_sixtyBF_431
      · exact prime_sixtyBF_1736347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 19457504483) ^ 9728752241 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 19457504483) ^ 1496731114 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 19457504483) ^ 45145022 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 19457504483) ^ 11206 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_21339752711 : Nat.Prime 21339752711 := by
  apply lucas_primality 21339752711 (14 : ZMod 21339752711)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (383, 1), (1091, 1), (5107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (383, 1), (1091, 1), (5107, 1)] : List FactorBlock).map factorBlockValue).prod) = 21339752711 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_5
      · exact prime_sixtyBF_383
      · exact prime_sixtyBF_1091
      · exact prime_sixtyBF_5107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 21339752711) ^ 10669876355 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (14 : ZMod 21339752711) ^ 4267950542 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (14 : ZMod 21339752711) ^ 55717370 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (14 : ZMod 21339752711) ^ 19559810 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (14 : ZMod 21339752711) ^ 4178530 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_24046493021 : Nat.Prime 24046493021 := by
  apply lucas_primality 24046493021 (2 : ZMod 24046493021)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (11, 1), (283, 1), (386227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (11, 1), (283, 1), (386227, 1)] : List FactorBlock).map factorBlockValue).prod) = 24046493021 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_5
      · exact prime_sixtyBF_11
      · exact prime_sixtyBF_283
      · exact prime_sixtyBF_386227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 24046493021) ^ 12023246510 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 24046493021) ^ 4809298604 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 24046493021) ^ 2186044820 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 24046493021) ^ 84969940 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 24046493021) ^ 62260 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_26547857257 : Nat.Prime 26547857257 := by
  apply lucas_primality 26547857257 (5 : ZMod 26547857257)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (1783, 1), (620393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (1783, 1), (620393, 1)] : List FactorBlock).map factorBlockValue).prod) = 26547857257 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_1783
      · exact prime_sixtyBF_620393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 26547857257) ^ 13273928628 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 26547857257) ^ 8849285752 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 26547857257) ^ 14889432 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 26547857257) ^ 42792 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_27508611433 : Nat.Prime 27508611433 := by
  apply lucas_primality 27508611433 (5 : ZMod 27508611433)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (23, 1), (29, 1), (1718429, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (23, 1), (29, 1), (1718429, 1)] : List FactorBlock).map factorBlockValue).prod) = 27508611433 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_23
      · exact prime_sixtyBF_29
      · exact prime_sixtyBF_1718429
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 27508611433) ^ 13754305716 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 27508611433) ^ 9169537144 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 27508611433) ^ 1196026584 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 27508611433) ^ 948572808 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 27508611433) ^ 16008 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_32860574161 : Nat.Prime 32860574161 := by
  apply lucas_primality 32860574161 (11 : ZMod 32860574161)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (136919059, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (136919059, 1)] : List FactorBlock).map factorBlockValue).prod) = 32860574161 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_5
      · exact prime_sixtyBF_136919059
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 32860574161) ^ 16430287080 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (11 : ZMod 32860574161) ^ 10953524720 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (11 : ZMod 32860574161) ^ 6572114832 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (11 : ZMod 32860574161) ^ 240 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_35641521709 : Nat.Prime 35641521709 := by
  apply lucas_primality 35641521709 (2 : ZMod 35641521709)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (228471293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (228471293, 1)] : List FactorBlock).map factorBlockValue).prod) = 35641521709 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_13
      · exact prime_sixtyBF_228471293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 35641521709) ^ 17820760854 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 35641521709) ^ 11880507236 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 35641521709) ^ 2741655516 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 35641521709) ^ 156 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_47855842603 : Nat.Prime 47855842603 := by
  apply lucas_primality 47855842603 (3 : ZMod 47855842603)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (419788093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (419788093, 1)] : List FactorBlock).map factorBlockValue).prod) = 47855842603 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_19
      · exact prime_sixtyBF_419788093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 47855842603) ^ 23927921301 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 47855842603) ^ 15951947534 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 47855842603) ^ 2518728558 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 47855842603) ^ 114 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_57916206493 : Nat.Prime 57916206493 := by
  apply lucas_primality 57916206493 (2 : ZMod 57916206493)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (191, 1), (1486403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (191, 1), (1486403, 1)] : List FactorBlock).map factorBlockValue).prod) = 57916206493 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_17
      · exact prime_sixtyBF_191
      · exact prime_sixtyBF_1486403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 57916206493) ^ 28958103246 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 57916206493) ^ 19305402164 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 57916206493) ^ 3406835676 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 57916206493) ^ 303226212 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 57916206493) ^ 38964 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_58761453143 : Nat.Prime 58761453143 := by
  apply lucas_primality 58761453143 (7 : ZMod 58761453143)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (4197246653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (4197246653, 1)] : List FactorBlock).map factorBlockValue).prod) = 58761453143 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_7
      · exact prime_sixtyBF_4197246653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 58761453143) ^ 29380726571 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (7 : ZMod 58761453143) ^ 8394493306 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (7 : ZMod 58761453143) ^ 14 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_63858386897 : Nat.Prime 63858386897 := by
  apply lucas_primality 63858386897 (3 : ZMod 63858386897)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (20639, 1), (193379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (20639, 1), (193379, 1)] : List FactorBlock).map factorBlockValue).prod) = 63858386897 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_20639
      · exact prime_sixtyBF_193379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 63858386897) ^ 31929193448 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 63858386897) ^ 3094064 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 63858386897) ^ 330224 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_73483155901 : Nat.Prime 73483155901 := by
  apply lucas_primality 73483155901 (2 : ZMod 73483155901)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 2), (7, 1), (11, 1), (61, 1), (17383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 2), (7, 1), (11, 1), (61, 1), (17383, 1)] : List FactorBlock).map factorBlockValue).prod) = 73483155901 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_5
      · exact prime_sixtyBF_7
      · exact prime_sixtyBF_11
      · exact prime_sixtyBF_61
      · exact prime_sixtyBF_17383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 73483155901) ^ 36741577950 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 73483155901) ^ 24494385300 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 73483155901) ^ 14696631180 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 73483155901) ^ 10497593700 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 73483155901) ^ 6680286900 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 73483155901) ^ 1204641900 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 73483155901) ^ 4227300 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_73986532577 : Nat.Prime 73986532577 := by
  apply lucas_primality 73986532577 (3 : ZMod 73986532577)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (11, 1), (29, 1), (7247897, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (11, 1), (29, 1), (7247897, 1)] : List FactorBlock).map factorBlockValue).prod) = 73986532577 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_11
      · exact prime_sixtyBF_29
      · exact prime_sixtyBF_7247897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 73986532577) ^ 36993266288 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 73986532577) ^ 6726048416 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 73986532577) ^ 2551259744 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 73986532577) ^ 10208 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_76978371599 : Nat.Prime 76978371599 := by
  apply lucas_primality 76978371599 (17 : ZMod 76978371599)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (61, 1), (33208961, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (61, 1), (33208961, 1)] : List FactorBlock).map factorBlockValue).prod) = 76978371599 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_19
      · exact prime_sixtyBF_61
      · exact prime_sixtyBF_33208961
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 76978371599) ^ 38489185799 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (17 : ZMod 76978371599) ^ 4051493242 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (17 : ZMod 76978371599) ^ 1261940518 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (17 : ZMod 76978371599) ^ 2318 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_77323304627 : Nat.Prime 77323304627 := by
  apply lucas_primality 77323304627 (2 : ZMod 77323304627)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (163, 1), (2579, 1), (91969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (163, 1), (2579, 1), (91969, 1)] : List FactorBlock).map factorBlockValue).prod) = 77323304627 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_163
      · exact prime_sixtyBF_2579
      · exact prime_sixtyBF_91969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 77323304627) ^ 38661652313 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 77323304627) ^ 474376102 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 77323304627) ^ 29981894 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 77323304627) ^ 840754 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_77942437999 : Nat.Prime 77942437999 := by
  apply lucas_primality 77942437999 (3 : ZMod 77942437999)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (764141549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (764141549, 1)] : List FactorBlock).map factorBlockValue).prod) = 77942437999 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_17
      · exact prime_sixtyBF_764141549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 77942437999) ^ 38971218999 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 77942437999) ^ 25980812666 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 77942437999) ^ 4584849294 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 77942437999) ^ 102 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_78754540411 : Nat.Prime 78754540411 := by
  apply lucas_primality 78754540411 (2 : ZMod 78754540411)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (7, 1), (13, 1), (229, 1), (13997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (7, 1), (13, 1), (229, 1), (13997, 1)] : List FactorBlock).map factorBlockValue).prod) = 78754540411 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_5
      · exact prime_sixtyBF_7
      · exact prime_sixtyBF_13
      · exact prime_sixtyBF_229
      · exact prime_sixtyBF_13997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 78754540411) ^ 39377270205 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 78754540411) ^ 26251513470 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 78754540411) ^ 15750908082 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 78754540411) ^ 11250648630 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 78754540411) ^ 6058041570 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 78754540411) ^ 343906290 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 78754540411) ^ 5626530 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_79328534267 : Nat.Prime 79328534267 := by
  apply lucas_primality 79328534267 (2 : ZMod 79328534267)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (389, 1), (2237, 1), (2399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (389, 1), (2237, 1), (2399, 1)] : List FactorBlock).map factorBlockValue).prod) = 79328534267 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_19
      · exact prime_sixtyBF_389
      · exact prime_sixtyBF_2237
      · exact prime_sixtyBF_2399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 79328534267) ^ 39664267133 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 79328534267) ^ 4175186014 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 79328534267) ^ 203929394 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 79328534267) ^ 35462018 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 79328534267) ^ 33067334 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_94427143709 : Nat.Prime 94427143709 := by
  apply lucas_primality 94427143709 (2 : ZMod 94427143709)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (47, 1), (409, 1), (863, 1), (1423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (47, 1), (409, 1), (863, 1), (1423, 1)] : List FactorBlock).map factorBlockValue).prod) = 94427143709 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_47
      · exact prime_sixtyBF_409
      · exact prime_sixtyBF_863
      · exact prime_sixtyBF_1423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 94427143709) ^ 47213571854 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 94427143709) ^ 2009088164 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 94427143709) ^ 230873212 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 94427143709) ^ 109417316 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 94427143709) ^ 66357796 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_95883815399 : Nat.Prime 95883815399 := by
  apply lucas_primality 95883815399 (13 : ZMod 95883815399)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (29, 1), (236167033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (29, 1), (236167033, 1)] : List FactorBlock).map factorBlockValue).prod) = 95883815399 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_7
      · exact prime_sixtyBF_29
      · exact prime_sixtyBF_236167033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 95883815399) ^ 47941907699 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (13 : ZMod 95883815399) ^ 13697687914 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (13 : ZMod 95883815399) ^ 3306338462 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (13 : ZMod 95883815399) ^ 406 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_110034445733 : Nat.Prime 110034445733 := by
  apply lucas_primality 110034445733 (2 : ZMod 110034445733)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (27508611433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (27508611433, 1)] : List FactorBlock).map factorBlockValue).prod) = 110034445733 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_27508611433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 110034445733) ^ 55017222866 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 110034445733) ^ 4 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_144278958127 : Nat.Prime 144278958127 := by
  apply lucas_primality 144278958127 (3 : ZMod 144278958127)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (24046493021, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (24046493021, 1)] : List FactorBlock).map factorBlockValue).prod) = 144278958127 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_24046493021
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 144278958127) ^ 72139479063 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 144278958127) ^ 48092986042 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 144278958127) ^ 6 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_179670036731 : Nat.Prime 179670036731 := by
  apply lucas_primality 179670036731 (10 : ZMod 179670036731)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (1056882569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (1056882569, 1)] : List FactorBlock).map factorBlockValue).prod) = 179670036731 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_5
      · exact prime_sixtyBF_17
      · exact prime_sixtyBF_1056882569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 179670036731) ^ 89835018365 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (10 : ZMod 179670036731) ^ 35934007346 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (10 : ZMod 179670036731) ^ 10568825690 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (10 : ZMod 179670036731) ^ 170 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_208360484561 : Nat.Prime 208360484561 := by
  apply lucas_primality 208360484561 (3 : ZMod 208360484561)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (89, 1), (1321, 1), (22153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (89, 1), (1321, 1), (22153, 1)] : List FactorBlock).map factorBlockValue).prod) = 208360484561 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_5
      · exact prime_sixtyBF_89
      · exact prime_sixtyBF_1321
      · exact prime_sixtyBF_22153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 208360484561) ^ 104180242280 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 208360484561) ^ 41672096912 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 208360484561) ^ 2341129040 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 208360484561) ^ 157729360 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 208360484561) ^ 9405520 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_313799243861 : Nat.Prime 313799243861 := by
  apply lucas_primality 313799243861 (3 : ZMod 313799243861)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (71, 1), (269, 1), (821507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (71, 1), (269, 1), (821507, 1)] : List FactorBlock).map factorBlockValue).prod) = 313799243861 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_5
      · exact prime_sixtyBF_71
      · exact prime_sixtyBF_269
      · exact prime_sixtyBF_821507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 313799243861) ^ 156899621930 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 313799243861) ^ 62759848772 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 313799243861) ^ 4419707660 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 313799243861) ^ 1166539940 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 313799243861) ^ 381980 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_380203396019 : Nat.Prime 380203396019 := by
  apply lucas_primality 380203396019 (2 : ZMod 380203396019)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (2917, 1), (2102267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (2917, 1), (2102267, 1)] : List FactorBlock).map factorBlockValue).prod) = 380203396019 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_31
      · exact prime_sixtyBF_2917
      · exact prime_sixtyBF_2102267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 380203396019) ^ 190101698009 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 380203396019) ^ 12264625678 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 380203396019) ^ 130340554 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 380203396019) ^ 180854 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_408858416389 : Nat.Prime 408858416389 := by
  apply lucas_primality 408858416389 (2 : ZMod 408858416389)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (1249, 1), (9093017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (1249, 1), (9093017, 1)] : List FactorBlock).map factorBlockValue).prod) = 408858416389 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_1249
      · exact prime_sixtyBF_9093017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 408858416389) ^ 204429208194 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 408858416389) ^ 136286138796 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 408858416389) ^ 327348612 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 408858416389) ^ 44964 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_475856301469 : Nat.Prime 475856301469 := by
  apply lucas_primality 475856301469 (2 : ZMod 475856301469)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (179, 1), (221534591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (179, 1), (221534591, 1)] : List FactorBlock).map factorBlockValue).prod) = 475856301469 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_179
      · exact prime_sixtyBF_221534591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 475856301469) ^ 237928150734 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 475856301469) ^ 158618767156 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 475856301469) ^ 2658415092 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 475856301469) ^ 2148 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_485936502283 : Nat.Prime 485936502283 := by
  apply lucas_primality 485936502283 (2 : ZMod 485936502283)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (11, 1), (83, 1), (4224139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (11, 1), (83, 1), (4224139, 1)] : List FactorBlock).map factorBlockValue).prod) = 485936502283 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_7
      · exact prime_sixtyBF_11
      · exact prime_sixtyBF_83
      · exact prime_sixtyBF_4224139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 485936502283) ^ 242968251141 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 485936502283) ^ 161978834094 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 485936502283) ^ 69419500326 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 485936502283) ^ 44176045662 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 485936502283) ^ 5854656654 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 485936502283) ^ 115038 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_739468230701 : Nat.Prime 739468230701 := by
  apply lucas_primality 739468230701 (2 : ZMod 739468230701)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (2897, 1), (2552531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (2897, 1), (2552531, 1)] : List FactorBlock).map factorBlockValue).prod) = 739468230701 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_5
      · exact prime_sixtyBF_2897
      · exact prime_sixtyBF_2552531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 739468230701) ^ 369734115350 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 739468230701) ^ 147893646140 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 739468230701) ^ 255253100 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 739468230701) ^ 289700 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_865673748763 : Nat.Prime 865673748763 := by
  apply lucas_primality 865673748763 (2 : ZMod 865673748763)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (144278958127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (144278958127, 1)] : List FactorBlock).map factorBlockValue).prod) = 865673748763 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_144278958127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 865673748763) ^ 432836874381 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 865673748763) ^ 288557916254 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 865673748763) ^ 6 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_1144339913207 : Nat.Prime 1144339913207 := by
  apply lucas_primality 1144339913207 (5 : ZMod 1144339913207)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (73, 1), (1119706373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (73, 1), (1119706373, 1)] : List FactorBlock).map factorBlockValue).prod) = 1144339913207 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_7
      · exact prime_sixtyBF_73
      · exact prime_sixtyBF_1119706373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1144339913207) ^ 572169956603 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1144339913207) ^ 163477130458 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1144339913207) ^ 15675889222 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1144339913207) ^ 1022 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_1235478372859 : Nat.Prime 1235478372859 := by
  apply lucas_primality 1235478372859 (3 : ZMod 1235478372859)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (7626409709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (7626409709, 1)] : List FactorBlock).map factorBlockValue).prod) = 1235478372859 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_7626409709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1235478372859) ^ 617739186429 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1235478372859) ^ 411826124286 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1235478372859) ^ 162 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_1368547096879 : Nat.Prime 1368547096879 := by
  apply lucas_primality 1368547096879 (3 : ZMod 1368547096879)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (13, 1), (283, 1), (6888683, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (13, 1), (283, 1), (6888683, 1)] : List FactorBlock).map factorBlockValue).prod) = 1368547096879 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_13
      · exact prime_sixtyBF_283
      · exact prime_sixtyBF_6888683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1368547096879) ^ 684273548439 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1368547096879) ^ 456182365626 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1368547096879) ^ 105272853606 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1368547096879) ^ 4835855466 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1368547096879) ^ 198666 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_1601049093541 : Nat.Prime 1601049093541 := by
  apply lucas_primality 1601049093541 (2 : ZMod 1601049093541)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (13, 1), (1783, 1), (1151221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (13, 1), (1783, 1), (1151221, 1)] : List FactorBlock).map factorBlockValue).prod) = 1601049093541 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_5
      · exact prime_sixtyBF_13
      · exact prime_sixtyBF_1783
      · exact prime_sixtyBF_1151221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1601049093541) ^ 800524546770 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1601049093541) ^ 533683031180 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1601049093541) ^ 320209818708 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1601049093541) ^ 123157622580 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1601049093541) ^ 897952380 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1601049093541) ^ 1390740 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_1664084771201 : Nat.Prime 1664084771201 := by
  apply lucas_primality 1664084771201 (3 : ZMod 1664084771201)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (5, 2), (967, 1), (537773, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (5, 2), (967, 1), (537773, 1)] : List FactorBlock).map factorBlockValue).prod) = 1664084771201 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_5
      · exact prime_sixtyBF_967
      · exact prime_sixtyBF_537773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1664084771201) ^ 832042385600 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1664084771201) ^ 332816954240 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1664084771201) ^ 1720873600 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1664084771201) ^ 3094400 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_2200688914661 : Nat.Prime 2200688914661 := by
  apply lucas_primality 2200688914661 (2 : ZMod 2200688914661)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (110034445733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (110034445733, 1)] : List FactorBlock).map factorBlockValue).prod) = 2200688914661 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_5
      · exact prime_sixtyBF_110034445733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2200688914661) ^ 1100344457330 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2200688914661) ^ 440137782932 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2200688914661) ^ 20 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_2855827233613 : Nat.Prime 2855827233613 := by
  apply lucas_primality 2855827233613 (2 : ZMod 2855827233613)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (79328534267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (79328534267, 1)] : List FactorBlock).map factorBlockValue).prod) = 2855827233613 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_79328534267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2855827233613) ^ 1427913616806 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2855827233613) ^ 951942411204 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2855827233613) ^ 36 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_3003394833937 : Nat.Prime 3003394833937 := by
  apply lucas_primality 3003394833937 (5 : ZMod 3003394833937)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (7, 1), (2979558367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (7, 1), (2979558367, 1)] : List FactorBlock).map factorBlockValue).prod) = 3003394833937 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_7
      · exact prime_sixtyBF_2979558367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 3003394833937) ^ 1501697416968 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 3003394833937) ^ 1001131611312 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 3003394833937) ^ 429056404848 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 3003394833937) ^ 1008 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_4154316837089 : Nat.Prime 4154316837089 := by
  apply lucas_primality 4154316837089 (3 : ZMod 4154316837089)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (11, 1), (11802036469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (11, 1), (11802036469, 1)] : List FactorBlock).map factorBlockValue).prod) = 4154316837089 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_11
      · exact prime_sixtyBF_11802036469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 4154316837089) ^ 2077158418544 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 4154316837089) ^ 377665167008 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 4154316837089) ^ 352 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_4287847625947 : Nat.Prime 4287847625947 := by
  apply lucas_primality 4287847625947 (2 : ZMod 4287847625947)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (17, 1), (14012573941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (17, 1), (14012573941, 1)] : List FactorBlock).map factorBlockValue).prod) = 4287847625947 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_17
      · exact prime_sixtyBF_14012573941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4287847625947) ^ 2143923812973 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 4287847625947) ^ 1429282541982 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 4287847625947) ^ 252226330938 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 4287847625947) ^ 306 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_4609386585577 : Nat.Prime 4609386585577 := by
  apply lucas_primality 4609386585577 (5 : ZMod 4609386585577)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (21339752711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (21339752711, 1)] : List FactorBlock).map factorBlockValue).prod) = 4609386585577 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_21339752711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 4609386585577) ^ 2304693292788 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 4609386585577) ^ 1536462195192 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 4609386585577) ^ 216 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_4854462744893 : Nat.Prime 4854462744893 := by
  apply lucas_primality 4854462744893 (2 : ZMod 4854462744893)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (13463, 1), (3919327, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (13463, 1), (3919327, 1)] : List FactorBlock).map factorBlockValue).prod) = 4854462744893 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_23
      · exact prime_sixtyBF_13463
      · exact prime_sixtyBF_3919327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4854462744893) ^ 2427231372446 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 4854462744893) ^ 211063597604 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 4854462744893) ^ 360578084 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 4854462744893) ^ 1238596 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_5915745845609 : Nat.Prime 5915745845609 := by
  apply lucas_primality 5915745845609 (3 : ZMod 5915745845609)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (739468230701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (739468230701, 1)] : List FactorBlock).map factorBlockValue).prod) = 5915745845609 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_739468230701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 5915745845609) ^ 2957872922804 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 5915745845609) ^ 8 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_6477677170709 : Nat.Prime 6477677170709 := by
  apply lucas_primality 6477677170709 (2 : ZMod 6477677170709)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (61, 1), (26547857257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (61, 1), (26547857257, 1)] : List FactorBlock).map factorBlockValue).prod) = 6477677170709 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_61
      · exact prime_sixtyBF_26547857257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 6477677170709) ^ 3238838585354 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 6477677170709) ^ 106191429028 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 6477677170709) ^ 244 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_6855126944131 : Nat.Prime 6855126944131 := by
  apply lucas_primality 6855126944131 (3 : ZMod 6855126944131)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (31, 1), (569, 1), (4318163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (31, 1), (569, 1), (4318163, 1)] : List FactorBlock).map factorBlockValue).prod) = 6855126944131 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_5
      · exact prime_sixtyBF_31
      · exact prime_sixtyBF_569
      · exact prime_sixtyBF_4318163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 6855126944131) ^ 3427563472065 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 6855126944131) ^ 2285042314710 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 6855126944131) ^ 1371025388826 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 6855126944131) ^ 221133127230 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 6855126944131) ^ 12047674770 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 6855126944131) ^ 1587510 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_8308633674179 : Nat.Prime 8308633674179 := by
  apply lucas_primality 8308633674179 (2 : ZMod 8308633674179)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (4154316837089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (4154316837089, 1)] : List FactorBlock).map factorBlockValue).prod) = 8308633674179 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_4154316837089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 8308633674179) ^ 4154316837089 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 8308633674179) ^ 2 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_8987750617009 : Nat.Prime 8987750617009 := by
  apply lucas_primality 8987750617009 (7 : ZMod 8987750617009)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (79, 1), (2370187399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (79, 1), (2370187399, 1)] : List FactorBlock).map factorBlockValue).prod) = 8987750617009 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_79
      · exact prime_sixtyBF_2370187399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 8987750617009) ^ 4493875308504 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (7 : ZMod 8987750617009) ^ 2995916872336 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (7 : ZMod 8987750617009) ^ 113768995152 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (7 : ZMod 8987750617009) ^ 3792 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_9703301150371 : Nat.Prime 9703301150371 := by
  apply lucas_primality 9703301150371 (2 : ZMod 9703301150371)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (17, 1), (8069, 1), (2357923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (17, 1), (8069, 1), (2357923, 1)] : List FactorBlock).map factorBlockValue).prod) = 9703301150371 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_5
      · exact prime_sixtyBF_17
      · exact prime_sixtyBF_8069
      · exact prime_sixtyBF_2357923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9703301150371) ^ 4851650575185 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 9703301150371) ^ 3234433716790 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 9703301150371) ^ 1940660230074 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 9703301150371) ^ 570782420610 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 9703301150371) ^ 1202540730 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 9703301150371) ^ 4115190 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_13154394068591 : Nat.Prime 13154394068591 := by
  apply lucas_primality 13154394068591 (19 : ZMod 13154394068591)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (43, 1), (431, 1), (70978223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (43, 1), (431, 1), (70978223, 1)] : List FactorBlock).map factorBlockValue).prod) = 13154394068591 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_5
      · exact prime_sixtyBF_43
      · exact prime_sixtyBF_431
      · exact prime_sixtyBF_70978223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 13154394068591) ^ 6577197034295 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (19 : ZMod 13154394068591) ^ 2630878813718 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (19 : ZMod 13154394068591) ^ 305916141130 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (19 : ZMod 13154394068591) ^ 30520635890 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (19 : ZMod 13154394068591) ^ 185330 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_13421985960151 : Nat.Prime 13421985960151 := by
  apply lucas_primality 13421985960151 (6 : ZMod 13421985960151)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (251, 1), (118831217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (251, 1), (118831217, 1)] : List FactorBlock).map factorBlockValue).prod) = 13421985960151 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_5
      · exact prime_sixtyBF_251
      · exact prime_sixtyBF_118831217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 13421985960151) ^ 6710992980075 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (6 : ZMod 13421985960151) ^ 4473995320050 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (6 : ZMod 13421985960151) ^ 2684397192030 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (6 : ZMod 13421985960151) ^ 53474047650 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (6 : ZMod 13421985960151) ^ 112950 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_15307466660653 : Nat.Prime 15307466660653 := by
  apply lucas_primality 15307466660653 (6 : ZMod 15307466660653)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (23, 1), (31859, 1), (1740853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (23, 1), (31859, 1), (1740853, 1)] : List FactorBlock).map factorBlockValue).prod) = 15307466660653 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_23
      · exact prime_sixtyBF_31859
      · exact prime_sixtyBF_1740853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 15307466660653) ^ 7653733330326 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (6 : ZMod 15307466660653) ^ 5102488886884 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (6 : ZMod 15307466660653) ^ 665542028724 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (6 : ZMod 15307466660653) ^ 480475428 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (6 : ZMod 15307466660653) ^ 8793084 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_16663375651001 : Nat.Prime 16663375651001 := by
  apply lucas_primality 16663375651001 (3 : ZMod 16663375651001)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 3), (13, 1), (4027, 1), (318301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 3), (13, 1), (4027, 1), (318301, 1)] : List FactorBlock).map factorBlockValue).prod) = 16663375651001 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_5
      · exact prime_sixtyBF_13
      · exact prime_sixtyBF_4027
      · exact prime_sixtyBF_318301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 16663375651001) ^ 8331687825500 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 16663375651001) ^ 3332675130200 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 16663375651001) ^ 1281798127000 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 16663375651001) ^ 4137913000 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 16663375651001) ^ 52351000 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_18267836827321 : Nat.Prime 18267836827321 := by
  apply lucas_primality 18267836827321 (23 : ZMod 18267836827321)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 7), (5, 1), (208823009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 7), (5, 1), (208823009, 1)] : List FactorBlock).map factorBlockValue).prod) = 18267836827321 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_5
      · exact prime_sixtyBF_208823009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (23 : ZMod 18267836827321) ^ 9133918413660 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (23 : ZMod 18267836827321) ^ 6089278942440 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (23 : ZMod 18267836827321) ^ 3653567365464 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (23 : ZMod 18267836827321) ^ 87480 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_24015316055543 : Nat.Prime 24015316055543 := by
  apply lucas_primality 24015316055543 (5 : ZMod 24015316055543)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (17, 1), (1721, 1), (58631429, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (17, 1), (1721, 1), (58631429, 1)] : List FactorBlock).map factorBlockValue).prod) = 24015316055543 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_7
      · exact prime_sixtyBF_17
      · exact prime_sixtyBF_1721
      · exact prime_sixtyBF_58631429
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 24015316055543) ^ 12007658027771 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 24015316055543) ^ 3430759436506 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 24015316055543) ^ 1412665650326 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 24015316055543) ^ 13954280102 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 24015316055543) ^ 409598 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_26308788137183 : Nat.Prime 26308788137183 := by
  apply lucas_primality 26308788137183 (5 : ZMod 26308788137183)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13154394068591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13154394068591, 1)] : List FactorBlock).map factorBlockValue).prod) = 26308788137183 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_13154394068591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 26308788137183) ^ 13154394068591 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 26308788137183) ^ 2 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_28818883683739 : Nat.Prime 28818883683739 := by
  apply lucas_primality 28818883683739 (3 : ZMod 28818883683739)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (1601049093541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (1601049093541, 1)] : List FactorBlock).map factorBlockValue).prod) = 28818883683739 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_1601049093541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 28818883683739) ^ 14409441841869 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 28818883683739) ^ 9606294561246 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 28818883683739) ^ 18 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_35379036197581 : Nat.Prime 35379036197581 := by
  apply lucas_primality 35379036197581 (7 : ZMod 35379036197581)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (31, 1), (53, 1), (358886551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (31, 1), (53, 1), (358886551, 1)] : List FactorBlock).map factorBlockValue).prod) = 35379036197581 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_5
      · exact prime_sixtyBF_31
      · exact prime_sixtyBF_53
      · exact prime_sixtyBF_358886551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 35379036197581) ^ 17689518098790 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (7 : ZMod 35379036197581) ^ 11793012065860 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (7 : ZMod 35379036197581) ^ 7075807239516 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (7 : ZMod 35379036197581) ^ 1141259232180 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (7 : ZMod 35379036197581) ^ 667528984860 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (7 : ZMod 35379036197581) ^ 98580 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_35541499385591 : Nat.Prime 35541499385591 := by
  apply lucas_primality 35541499385591 (11 : ZMod 35541499385591)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (53, 1), (9311, 1), (654743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (53, 1), (9311, 1), (654743, 1)] : List FactorBlock).map factorBlockValue).prod) = 35541499385591 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_5
      · exact prime_sixtyBF_11
      · exact prime_sixtyBF_53
      · exact prime_sixtyBF_9311
      · exact prime_sixtyBF_654743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 35541499385591) ^ 17770749692795 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (11 : ZMod 35541499385591) ^ 7108299877118 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (11 : ZMod 35541499385591) ^ 3231045398690 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (11 : ZMod 35541499385591) ^ 670594328030 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (11 : ZMod 35541499385591) ^ 3817151690 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (11 : ZMod 35541499385591) ^ 54283130 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_35778504001061 : Nat.Prime 35778504001061 := by
  apply lucas_primality 35778504001061 (2 : ZMod 35778504001061)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (47, 1), (1619, 1), (23509721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (47, 1), (1619, 1), (23509721, 1)] : List FactorBlock).map factorBlockValue).prod) = 35778504001061 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_5
      · exact prime_sixtyBF_47
      · exact prime_sixtyBF_1619
      · exact prime_sixtyBF_23509721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 35778504001061) ^ 17889252000530 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 35778504001061) ^ 7155700800212 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 35778504001061) ^ 761244765980 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 35778504001061) ^ 22099137740 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 35778504001061) ^ 1521860 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_35874960865283 : Nat.Prime 35874960865283 := by
  apply lucas_primality 35874960865283 (2 : ZMod 35874960865283)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 1), (1327, 1), (175549579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 1), (1327, 1), (175549579, 1)] : List FactorBlock).map factorBlockValue).prod) = 35874960865283 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_7
      · exact prime_sixtyBF_11
      · exact prime_sixtyBF_1327
      · exact prime_sixtyBF_175549579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 35874960865283) ^ 17937480432641 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 35874960865283) ^ 5124994409326 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 35874960865283) ^ 3261360078662 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 35874960865283) ^ 27034635166 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 35874960865283) ^ 204358 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_41682848479901 : Nat.Prime 41682848479901 := by
  apply lucas_primality 41682848479901 (2 : ZMod 41682848479901)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (43, 2), (1831, 1), (123121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (43, 2), (1831, 1), (123121, 1)] : List FactorBlock).map factorBlockValue).prod) = 41682848479901 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_5
      · exact prime_sixtyBF_43
      · exact prime_sixtyBF_1831
      · exact prime_sixtyBF_123121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 41682848479901) ^ 20841424239950 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 41682848479901) ^ 8336569695980 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 41682848479901) ^ 969368569300 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 41682848479901) ^ 22765072900 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 41682848479901) ^ 338551900 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_44521797530773 : Nat.Prime 44521797530773 := by
  apply lucas_primality 44521797530773 (5 : ZMod 44521797530773)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (17, 1), (37, 1), (1966163113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (17, 1), (37, 1), (1966163113, 1)] : List FactorBlock).map factorBlockValue).prod) = 44521797530773 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_17
      · exact prime_sixtyBF_37
      · exact prime_sixtyBF_1966163113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 44521797530773) ^ 22260898765386 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 44521797530773) ^ 14840599176924 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 44521797530773) ^ 2618929266516 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 44521797530773) ^ 1203291825156 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 44521797530773) ^ 22644 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_51306136940519 : Nat.Prime 51306136940519 := by
  apply lucas_primality 51306136940519 (13 : ZMod 51306136940519)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (883, 1), (7229, 1), (4018837, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (883, 1), (7229, 1), (4018837, 1)] : List FactorBlock).map factorBlockValue).prod) = 51306136940519 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_883
      · exact prime_sixtyBF_7229
      · exact prime_sixtyBF_4018837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 51306136940519) ^ 25653068470259 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (13 : ZMod 51306136940519) ^ 58104345346 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (13 : ZMod 51306136940519) ^ 7097266142 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (13 : ZMod 51306136940519) ^ 12766414 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_62508145368301 : Nat.Prime 62508145368301 := by
  apply lucas_primality 62508145368301 (21 : ZMod 62508145368301)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (208360484561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (208360484561, 1)] : List FactorBlock).map factorBlockValue).prod) = 62508145368301 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_5
      · exact prime_sixtyBF_208360484561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (21 : ZMod 62508145368301) ^ 31254072684150 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (21 : ZMod 62508145368301) ^ 20836048456100 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (21 : ZMod 62508145368301) ^ 12501629073660 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (21 : ZMod 62508145368301) ^ 300 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_70988950147309 : Nat.Prime 70988950147309 := by
  apply lucas_primality 70988950147309 (6 : ZMod 70988950147309)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5915745845609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5915745845609, 1)] : List FactorBlock).map factorBlockValue).prod) = 70988950147309 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_5915745845609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 70988950147309) ^ 35494475073654 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (6 : ZMod 70988950147309) ^ 23662983382436 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (6 : ZMod 70988950147309) ^ 12 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_83365696959803 : Nat.Prime 83365696959803 := by
  apply lucas_primality 83365696959803 (2 : ZMod 83365696959803)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41682848479901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41682848479901, 1)] : List FactorBlock).map factorBlockValue).prod) = 83365696959803 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_41682848479901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 83365696959803) ^ 41682848479901 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 83365696959803) ^ 2 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_102908343022729 : Nat.Prime 102908343022729 := by
  apply lucas_primality 102908343022729 (19 : ZMod 102908343022729)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (4287847625947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (4287847625947, 1)] : List FactorBlock).map factorBlockValue).prod) = 102908343022729 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_4287847625947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (19 : ZMod 102908343022729) ^ 51454171511364 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (19 : ZMod 102908343022729) ^ 34302781007576 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (19 : ZMod 102908343022729) ^ 24 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_133814603470189 : Nat.Prime 133814603470189 := by
  apply lucas_primality 133814603470189 (10 : ZMod 133814603470189)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (211, 1), (2781545761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (211, 1), (2781545761, 1)] : List FactorBlock).map factorBlockValue).prod) = 133814603470189 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_19
      · exact prime_sixtyBF_211
      · exact prime_sixtyBF_2781545761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 133814603470189) ^ 66907301735094 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (10 : ZMod 133814603470189) ^ 44604867823396 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (10 : ZMod 133814603470189) ^ 7042873866852 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (10 : ZMod 133814603470189) ^ 634192433508 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (10 : ZMod 133814603470189) ^ 48108 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_163954156190633 : Nat.Prime 163954156190633 := by
  apply lucas_primality 163954156190633 (3 : ZMod 163954156190633)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (277, 1), (73986532577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (277, 1), (73986532577, 1)] : List FactorBlock).map factorBlockValue).prod) = 163954156190633 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_277
      · exact prime_sixtyBF_73986532577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 163954156190633) ^ 81977078095316 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 163954156190633) ^ 591892260616 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 163954156190633) ^ 2216 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_175323563038783 : Nat.Prime 175323563038783 := by
  apply lucas_primality 175323563038783 (11 : ZMod 175323563038783)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (3449, 1), (2824064351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (3449, 1), (2824064351, 1)] : List FactorBlock).map factorBlockValue).prod) = 175323563038783 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_3449
      · exact prime_sixtyBF_2824064351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 175323563038783) ^ 87661781519391 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (11 : ZMod 175323563038783) ^ 58441187679594 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (11 : ZMod 175323563038783) ^ 50833158318 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (11 : ZMod 175323563038783) ^ 62082 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_202726720646011 : Nat.Prime 202726720646011 := by
  apply lucas_primality 202726720646011 (2 : ZMod 202726720646011)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (11, 1), (47, 1), (32831, 1), (132707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (11, 1), (47, 1), (32831, 1), (132707, 1)] : List FactorBlock).map factorBlockValue).prod) = 202726720646011 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_5
      · exact prime_sixtyBF_11
      · exact prime_sixtyBF_47
      · exact prime_sixtyBF_32831
      · exact prime_sixtyBF_132707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 202726720646011) ^ 101363360323005 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 202726720646011) ^ 67575573548670 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 202726720646011) ^ 40545344129202 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 202726720646011) ^ 18429701876910 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 202726720646011) ^ 4313334481830 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 202726720646011) ^ 6174856710 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 202726720646011) ^ 1527626430 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_211529867337343 : Nat.Prime 211529867337343 := by
  apply lucas_primality 211529867337343 (6 : ZMod 211529867337343)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (853, 1), (13776857323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (853, 1), (13776857323, 1)] : List FactorBlock).map factorBlockValue).prod) = 211529867337343 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_853
      · exact prime_sixtyBF_13776857323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 211529867337343) ^ 105764933668671 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (6 : ZMod 211529867337343) ^ 70509955779114 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (6 : ZMod 211529867337343) ^ 247983431814 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (6 : ZMod 211529867337343) ^ 15354 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_250721256913807 : Nat.Prime 250721256913807 := by
  apply lucas_primality 250721256913807 (5 : ZMod 250721256913807)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (1017353, 1), (5867731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (1017353, 1), (5867731, 1)] : List FactorBlock).map factorBlockValue).prod) = 250721256913807 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_7
      · exact prime_sixtyBF_1017353
      · exact prime_sixtyBF_5867731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 250721256913807) ^ 125360628456903 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 250721256913807) ^ 83573752304602 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 250721256913807) ^ 35817322416258 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 250721256913807) ^ 246444702 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 250721256913807) ^ 42728826 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_397629806780177 : Nat.Prime 397629806780177 := by
  apply lucas_primality 397629806780177 (3 : ZMod 397629806780177)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (17, 1), (58231, 1), (25104743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (17, 1), (58231, 1), (25104743, 1)] : List FactorBlock).map factorBlockValue).prod) = 397629806780177 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_17
      · exact prime_sixtyBF_58231
      · exact prime_sixtyBF_25104743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 397629806780177) ^ 198814903390088 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 397629806780177) ^ 23389988634128 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 397629806780177) ^ 6828490096 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 397629806780177) ^ 15838832 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_515828230792397 : Nat.Prime 515828230792397 := by
  apply lucas_primality 515828230792397 (2 : ZMod 515828230792397)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (271, 1), (475856301469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (271, 1), (475856301469, 1)] : List FactorBlock).map factorBlockValue).prod) = 515828230792397 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_271
      · exact prime_sixtyBF_475856301469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 515828230792397) ^ 257914115396198 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 515828230792397) ^ 1903425205876 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 515828230792397) ^ 1084 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_534604280440787 : Nat.Prime 534604280440787 := by
  apply lucas_primality 534604280440787 (2 : ZMod 534604280440787)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (89, 1), (3003394833937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (89, 1), (3003394833937, 1)] : List FactorBlock).map factorBlockValue).prod) = 534604280440787 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_89
      · exact prime_sixtyBF_3003394833937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 534604280440787) ^ 267302140220393 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 534604280440787) ^ 6006789667874 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 534604280440787) ^ 178 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_683858140393721 : Nat.Prime 683858140393721 := by
  apply lucas_primality 683858140393721 (3 : ZMod 683858140393721)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (3461, 1), (4939743863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (3461, 1), (4939743863, 1)] : List FactorBlock).map factorBlockValue).prod) = 683858140393721 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_5
      · exact prime_sixtyBF_3461
      · exact prime_sixtyBF_4939743863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 683858140393721) ^ 341929070196860 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 683858140393721) ^ 136771628078744 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 683858140393721) ^ 197589754520 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 683858140393721) ^ 138440 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_1188000472793611 : Nat.Prime 1188000472793611 := by
  apply lucas_primality 1188000472793611 (2 : ZMod 1188000472793611)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (59, 1), (95883815399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (59, 1), (95883815399, 1)] : List FactorBlock).map factorBlockValue).prod) = 1188000472793611 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_5
      · exact prime_sixtyBF_7
      · exact prime_sixtyBF_59
      · exact prime_sixtyBF_95883815399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1188000472793611) ^ 594000236396805 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1188000472793611) ^ 396000157597870 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1188000472793611) ^ 237600094558722 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1188000472793611) ^ 169714353256230 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1188000472793611) ^ 20135601233790 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1188000472793611) ^ 12390 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_1562034063778961 : Nat.Prime 1562034063778961 := by
  apply lucas_primality 1562034063778961 (3 : ZMod 1562034063778961)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (17, 1), (10883, 1), (105536567, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (17, 1), (10883, 1), (105536567, 1)] : List FactorBlock).map factorBlockValue).prod) = 1562034063778961 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_5
      · exact prime_sixtyBF_17
      · exact prime_sixtyBF_10883
      · exact prime_sixtyBF_105536567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1562034063778961) ^ 781017031889480 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1562034063778961) ^ 312406812755792 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1562034063778961) ^ 91884356692880 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1562034063778961) ^ 143529731120 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1562034063778961) ^ 14800880 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_1707525348400409 : Nat.Prime 1707525348400409 := by
  apply lucas_primality 1707525348400409 (3 : ZMod 1707525348400409)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (274019, 1), (778926529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (274019, 1), (778926529, 1)] : List FactorBlock).map factorBlockValue).prod) = 1707525348400409 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_274019
      · exact prime_sixtyBF_778926529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1707525348400409) ^ 853762674200204 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1707525348400409) ^ 6231412232 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1707525348400409) ^ 2192152 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_2103882756465397 : Nat.Prime 2103882756465397 := by
  apply lucas_primality 2103882756465397 (2 : ZMod 2103882756465397)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (175323563038783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (175323563038783, 1)] : List FactorBlock).map factorBlockValue).prod) = 2103882756465397 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_175323563038783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2103882756465397) ^ 1051941378232698 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2103882756465397) ^ 701294252155132 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2103882756465397) ^ 12 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_2848694436861731 : Nat.Prime 2848694436861731 := by
  apply lucas_primality 2848694436861731 (2 : ZMod 2848694436861731)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (197, 1), (25841, 1), (55959049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (197, 1), (25841, 1), (55959049, 1)] : List FactorBlock).map factorBlockValue).prod) = 2848694436861731 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_5
      · exact prime_sixtyBF_197
      · exact prime_sixtyBF_25841
      · exact prime_sixtyBF_55959049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2848694436861731) ^ 1424347218430865 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2848694436861731) ^ 569738887372346 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2848694436861731) ^ 14460377852090 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2848694436861731) ^ 110239326530 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2848694436861731) ^ 50906770 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_2953782198081733 : Nat.Prime 2953782198081733 := by
  apply lucas_primality 2953782198081733 (2 : ZMod 2953782198081733)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (223, 1), (557, 1), (3307, 1), (599243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (223, 1), (557, 1), (3307, 1), (599243, 1)] : List FactorBlock).map factorBlockValue).prod) = 2953782198081733 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_223
      · exact prime_sixtyBF_557
      · exact prime_sixtyBF_3307
      · exact prime_sixtyBF_599243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2953782198081733) ^ 1476891099040866 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2953782198081733) ^ 984594066027244 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2953782198081733) ^ 13245660081084 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2953782198081733) ^ 5303020104276 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2953782198081733) ^ 893190867276 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2953782198081733) ^ 4929189324 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_3676137361692577 : Nat.Prime 3676137361692577 := by
  apply lucas_primality 3676137361692577 (10 : ZMod 3676137361692577)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (11, 2), (29, 1), (443, 1), (24633913, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (11, 2), (29, 1), (443, 1), (24633913, 1)] : List FactorBlock).map factorBlockValue).prod) = 3676137361692577 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_11
      · exact prime_sixtyBF_29
      · exact prime_sixtyBF_443
      · exact prime_sixtyBF_24633913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 3676137361692577) ^ 1838068680846288 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (10 : ZMod 3676137361692577) ^ 1225379120564192 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (10 : ZMod 3676137361692577) ^ 334194305608416 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (10 : ZMod 3676137361692577) ^ 126763357299744 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (10 : ZMod 3676137361692577) ^ 8298278468832 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (10 : ZMod 3676137361692577) ^ 149230752 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_5976169114846219 : Nat.Prime 5976169114846219 := by
  apply lucas_primality 5976169114846219 (2 : ZMod 5976169114846219)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (223, 1), (1021, 1), (16993, 1), (257437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (223, 1), (1021, 1), (16993, 1), (257437, 1)] : List FactorBlock).map factorBlockValue).prod) = 5976169114846219 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_223
      · exact prime_sixtyBF_1021
      · exact prime_sixtyBF_16993
      · exact prime_sixtyBF_257437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5976169114846219) ^ 2988084557423109 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 5976169114846219) ^ 1992056371615406 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 5976169114846219) ^ 26798964640566 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 5976169114846219) ^ 5853250847058 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 5976169114846219) ^ 351684170826 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 5976169114846219) ^ 23214103314 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_16038128413223611 : Nat.Prime 16038128413223611 := by
  apply lucas_primality 16038128413223611 (3 : ZMod 16038128413223611)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (534604280440787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (534604280440787, 1)] : List FactorBlock).map factorBlockValue).prod) = 16038128413223611 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_5
      · exact prime_sixtyBF_534604280440787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 16038128413223611) ^ 8019064206611805 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 16038128413223611) ^ 5346042804407870 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 16038128413223611) ^ 3207625682644722 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 16038128413223611) ^ 30 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_23321731798334737 : Nat.Prime 23321731798334737 := by
  apply lucas_primality 23321731798334737 (7 : ZMod 23321731798334737)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 4), (13, 1), (23, 1), (35323, 1), (1703833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 4), (13, 1), (23, 1), (35323, 1), (1703833, 1)] : List FactorBlock).map factorBlockValue).prod) = 23321731798334737 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_13
      · exact prime_sixtyBF_23
      · exact prime_sixtyBF_35323
      · exact prime_sixtyBF_1703833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 23321731798334737) ^ 11660865899167368 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (7 : ZMod 23321731798334737) ^ 7773910599444912 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (7 : ZMod 23321731798334737) ^ 1793979369102672 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (7 : ZMod 23321731798334737) ^ 1013988339058032 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (7 : ZMod 23321731798334737) ^ 660242102832 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (7 : ZMod 23321731798334737) ^ 13687803792 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_30003149875144493 : Nat.Prime 30003149875144493 := by
  apply lucas_primality 30003149875144493 (2 : ZMod 30003149875144493)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3652367, 1), (2053678469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3652367, 1), (2053678469, 1)] : List FactorBlock).map factorBlockValue).prod) = 30003149875144493 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3652367
      · exact prime_sixtyBF_2053678469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 30003149875144493) ^ 15001574937572246 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 30003149875144493) ^ 8214713876 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 30003149875144493) ^ 14609468 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_32501111509238233 : Nat.Prime 32501111509238233 := by
  apply lucas_primality 32501111509238233 (10 : ZMod 32501111509238233)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (43, 1), (47, 1), (89, 1), (28111, 1), (38261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (43, 1), (47, 1), (89, 1), (28111, 1), (38261, 1)] : List FactorBlock).map factorBlockValue).prod) = 32501111509238233 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_7
      · exact prime_sixtyBF_43
      · exact prime_sixtyBF_47
      · exact prime_sixtyBF_89
      · exact prime_sixtyBF_28111
      · exact prime_sixtyBF_38261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 32501111509238233) ^ 16250555754619116 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (10 : ZMod 32501111509238233) ^ 10833703836412744 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (10 : ZMod 32501111509238233) ^ 4643015929891176 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (10 : ZMod 32501111509238233) ^ 755839802540424 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (10 : ZMod 32501111509238233) ^ 691513010834856 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (10 : ZMod 32501111509238233) ^ 365181028193688 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (10 : ZMod 32501111509238233) ^ 1156170591912 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (10 : ZMod 32501111509238233) ^ 849457973112 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_34867581525411757 : Nat.Prime 34867581525411757 := by
  apply lucas_primality 34867581525411757 (2 : ZMod 34867581525411757)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (3896861, 1), (67784903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (3896861, 1), (67784903, 1)] : List FactorBlock).map factorBlockValue).prod) = 34867581525411757 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_11
      · exact prime_sixtyBF_3896861
      · exact prime_sixtyBF_67784903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 34867581525411757) ^ 17433790762705878 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 34867581525411757) ^ 11622527175137252 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 34867581525411757) ^ 3169780138673796 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 34867581525411757) ^ 8947607196 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 34867581525411757) ^ 514385652 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_43143154818873199 : Nat.Prime 43143154818873199 := by
  apply lucas_primality 43143154818873199 (6 : ZMod 43143154818873199)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (91303, 1), (78754540411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (91303, 1), (78754540411, 1)] : List FactorBlock).map factorBlockValue).prod) = 43143154818873199 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_91303
      · exact prime_sixtyBF_78754540411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 43143154818873199) ^ 21571577409436599 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (6 : ZMod 43143154818873199) ^ 14381051606291066 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (6 : ZMod 43143154818873199) ^ 472527242466 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (6 : ZMod 43143154818873199) ^ 547818 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_47467597773629893 : Nat.Prime 47467597773629893 := by
  apply lucas_primality 47467597773629893 (2 : ZMod 47467597773629893)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (47, 1), (673, 1), (14741, 1), (8483521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (47, 1), (673, 1), (14741, 1), (8483521, 1)] : List FactorBlock).map factorBlockValue).prod) = 47467597773629893 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_47
      · exact prime_sixtyBF_673
      · exact prime_sixtyBF_14741
      · exact prime_sixtyBF_8483521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 47467597773629893) ^ 23733798886814946 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 47467597773629893) ^ 15822532591209964 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 47467597773629893) ^ 1009948888800636 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 47467597773629893) ^ 70531348846404 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 47467597773629893) ^ 3220107033012 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 47467597773629893) ^ 5595270852 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_56293573765019543 : Nat.Prime 56293573765019543 := by
  apply lucas_primality 56293573765019543 (5 : ZMod 56293573765019543)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (101, 1), (1117, 1), (35641521709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (101, 1), (1117, 1), (35641521709, 1)] : List FactorBlock).map factorBlockValue).prod) = 56293573765019543 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_7
      · exact prime_sixtyBF_101
      · exact prime_sixtyBF_1117
      · exact prime_sixtyBF_35641521709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 56293573765019543) ^ 28146786882509771 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 56293573765019543) ^ 8041939109288506 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 56293573765019543) ^ 557362116485342 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 56293573765019543) ^ 50397111696526 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 56293573765019543) ^ 1579438 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_135215033261379667 : Nat.Prime 135215033261379667 := by
  apply lucas_primality 135215033261379667 (5 : ZMod 135215033261379667)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (71, 1), (6477677170709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (71, 1), (6477677170709, 1)] : List FactorBlock).map factorBlockValue).prod) = 135215033261379667 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_7
      · exact prime_sixtyBF_71
      · exact prime_sixtyBF_6477677170709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 135215033261379667) ^ 67607516630689833 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 135215033261379667) ^ 45071677753793222 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 135215033261379667) ^ 19316433323054238 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 135215033261379667) ^ 1904437088188446 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 135215033261379667) ^ 20874 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_188057165046209281 : Nat.Prime 188057165046209281 := by
  apply lucas_primality 188057165046209281 (41 : ZMod 188057165046209281)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 3), (5, 1), (607, 1), (827, 1), (10839817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 3), (5, 1), (607, 1), (827, 1), (10839817, 1)] : List FactorBlock).map factorBlockValue).prod) = 188057165046209281 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_5
      · exact prime_sixtyBF_607
      · exact prime_sixtyBF_827
      · exact prime_sixtyBF_10839817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (41 : ZMod 188057165046209281) ^ 94028582523104640 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (41 : ZMod 188057165046209281) ^ 62685721682069760 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (41 : ZMod 188057165046209281) ^ 37611433009241856 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (41 : ZMod 188057165046209281) ^ 309814110455040 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (41 : ZMod 188057165046209281) ^ 227396813840640 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (41 : ZMod 188057165046209281) ^ 17348739840 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_229680702994695853 : Nat.Prime 229680702994695853 := by
  apply lucas_primality 229680702994695853 (5 : ZMod 229680702994695853)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (541, 1), (35379036197581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (541, 1), (35379036197581, 1)] : List FactorBlock).map factorBlockValue).prod) = 229680702994695853 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_541
      · exact prime_sixtyBF_35379036197581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 229680702994695853) ^ 114840351497347926 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 229680702994695853) ^ 76560234331565284 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 229680702994695853) ^ 424548434370972 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 229680702994695853) ^ 6492 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_303771542379342187 : Nat.Prime 303771542379342187 := by
  apply lucas_primality 303771542379342187 (3 : ZMod 303771542379342187)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (409, 1), (1607, 1), (10729, 1), (7179553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (409, 1), (1607, 1), (10729, 1), (7179553, 1)] : List FactorBlock).map factorBlockValue).prod) = 303771542379342187 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_409
      · exact prime_sixtyBF_1607
      · exact prime_sixtyBF_10729
      · exact prime_sixtyBF_7179553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 303771542379342187) ^ 151885771189671093 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 303771542379342187) ^ 101257180793114062 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 303771542379342187) ^ 742717707528954 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 303771542379342187) ^ 189030206832198 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 303771542379342187) ^ 28313127260634 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 303771542379342187) ^ 42310648362 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_369377599805201023 : Nat.Prime 369377599805201023 := by
  apply lucas_primality 369377599805201023 (6 : ZMod 369377599805201023)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (89, 1), (9839449, 1), (10042931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (89, 1), (9839449, 1), (10042931, 1)] : List FactorBlock).map factorBlockValue).prod) = 369377599805201023 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_7
      · exact prime_sixtyBF_89
      · exact prime_sixtyBF_9839449
      · exact prime_sixtyBF_10042931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 369377599805201023) ^ 184688799902600511 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (6 : ZMod 369377599805201023) ^ 123125866601733674 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (6 : ZMod 369377599805201023) ^ 52768228543600146 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (6 : ZMod 369377599805201023) ^ 4150310110170798 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (6 : ZMod 369377599805201023) ^ 37540476078 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (6 : ZMod 369377599805201023) ^ 36779860362 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_482855730763388897 : Nat.Prime 482855730763388897 := by
  apply lucas_primality 482855730763388897 (3 : ZMod 482855730763388897)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (691, 1), (132263, 1), (165101491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (691, 1), (132263, 1), (165101491, 1)] : List FactorBlock).map factorBlockValue).prod) = 482855730763388897 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_691
      · exact prime_sixtyBF_132263
      · exact prime_sixtyBF_165101491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 482855730763388897) ^ 241427865381694448 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 482855730763388897) ^ 698778192132256 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 482855730763388897) ^ 3650724168992 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 482855730763388897) ^ 2924599456 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_1092802598795165213 : Nat.Prime 1092802598795165213 := by
  apply lucas_primality 1092802598795165213 (2 : ZMod 1092802598795165213)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (229, 1), (20599, 1), (57916206493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (229, 1), (20599, 1), (57916206493, 1)] : List FactorBlock).map factorBlockValue).prod) = 1092802598795165213 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_229
      · exact prime_sixtyBF_20599
      · exact prime_sixtyBF_57916206493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1092802598795165213) ^ 546401299397582606 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1092802598795165213) ^ 4772063750197228 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1092802598795165213) ^ 53051245147588 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1092802598795165213) ^ 18868684 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_1424019066914993077 : Nat.Prime 1424019066914993077 := by
  apply lucas_primality 1424019066914993077 (2 : ZMod 1424019066914993077)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (11, 1), (17, 1), (211529867337343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (11, 1), (17, 1), (211529867337343, 1)] : List FactorBlock).map factorBlockValue).prod) = 1424019066914993077 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_11
      · exact prime_sixtyBF_17
      · exact prime_sixtyBF_211529867337343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1424019066914993077) ^ 712009533457496538 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1424019066914993077) ^ 474673022304997692 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1424019066914993077) ^ 129456278810453916 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1424019066914993077) ^ 83765827465587828 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1424019066914993077) ^ 6732 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_1843979874874032799 : Nat.Prime 1843979874874032799 := by
  apply lucas_primality 1843979874874032799 (3 : ZMod 1843979874874032799)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (7, 1), (23, 1), (52583, 1), (1344528233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (7, 1), (23, 1), (52583, 1), (1344528233, 1)] : List FactorBlock).map factorBlockValue).prod) = 1843979874874032799 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_7
      · exact prime_sixtyBF_23
      · exact prime_sixtyBF_52583
      · exact prime_sixtyBF_1344528233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1843979874874032799) ^ 921989937437016399 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1843979874874032799) ^ 614659958291344266 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1843979874874032799) ^ 263425696410576114 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1843979874874032799) ^ 80173038038001426 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1843979874874032799) ^ 35067985373106 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1843979874874032799) ^ 1371469806 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_1936982803160385881 : Nat.Prime 1936982803160385881 := by
  apply lucas_primality 1936982803160385881 (6 : ZMod 1936982803160385881)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (626261, 1), (77323304627, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (626261, 1), (77323304627, 1)] : List FactorBlock).map factorBlockValue).prod) = 1936982803160385881 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_5
      · exact prime_sixtyBF_626261
      · exact prime_sixtyBF_77323304627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 1936982803160385881) ^ 968491401580192940 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (6 : ZMod 1936982803160385881) ^ 387396560632077176 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (6 : ZMod 1936982803160385881) ^ 3092932185080 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (6 : ZMod 1936982803160385881) ^ 25050440 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_2324372311347287389 : Nat.Prime 2324372311347287389 := by
  apply lucas_primality 2324372311347287389 (2 : ZMod 2324372311347287389)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (263, 1), (372709, 1), (179641277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (263, 1), (372709, 1), (179641277, 1)] : List FactorBlock).map factorBlockValue).prod) = 2324372311347287389 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_11
      · exact prime_sixtyBF_263
      · exact prime_sixtyBF_372709
      · exact prime_sixtyBF_179641277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2324372311347287389) ^ 1162186155673643694 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2324372311347287389) ^ 774790770449095796 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2324372311347287389) ^ 211306573758844308 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2324372311347287389) ^ 8837917533639876 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2324372311347287389) ^ 6236426572332 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2324372311347287389) ^ 12938965644 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_2867867703521123791 : Nat.Prime 2867867703521123791 := by
  apply lucas_primality 2867867703521123791 (3 : ZMod 2867867703521123791)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (5233, 1), (18267836827321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (5233, 1), (18267836827321, 1)] : List FactorBlock).map factorBlockValue).prod) = 2867867703521123791 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_5
      · exact prime_sixtyBF_5233
      · exact prime_sixtyBF_18267836827321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2867867703521123791) ^ 1433933851760561895 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 2867867703521123791) ^ 955955901173707930 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 2867867703521123791) ^ 573573540704224758 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 2867867703521123791) ^ 548035104819630 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 2867867703521123791) ^ 156990 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_4093927908341190527 : Nat.Prime 4093927908341190527 := by
  apply lucas_primality 4093927908341190527 (5 : ZMod 4093927908341190527)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (942509, 1), (94427143709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (942509, 1), (94427143709, 1)] : List FactorBlock).map factorBlockValue).prod) = 4093927908341190527 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_23
      · exact prime_sixtyBF_942509
      · exact prime_sixtyBF_94427143709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 4093927908341190527) ^ 2046963954170595263 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 4093927908341190527) ^ 177996865580051762 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 4093927908341190527) ^ 4343648610614 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 4093927908341190527) ^ 43355414 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_5831981517342537989 : Nat.Prime 5831981517342537989 := by
  apply lucas_primality 5831981517342537989 (2 : ZMod 5831981517342537989)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (59, 1), (1483, 1), (16663375651001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (59, 1), (1483, 1), (16663375651001, 1)] : List FactorBlock).map factorBlockValue).prod) = 5831981517342537989 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_59
      · exact prime_sixtyBF_1483
      · exact prime_sixtyBF_16663375651001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5831981517342537989) ^ 2915990758671268994 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 5831981517342537989) ^ 98847144361737932 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 5831981517342537989) ^ 3932556653636236 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 5831981517342537989) ^ 349988 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_6694851809492770321 : Nat.Prime 6694851809492770321 := by
  apply lucas_primality 6694851809492770321 (7 : ZMod 6694851809492770321)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (5, 1), (4181867, 1), (741168581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (5, 1), (4181867, 1), (741168581, 1)] : List FactorBlock).map factorBlockValue).prod) = 6694851809492770321 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_5
      · exact prime_sixtyBF_4181867
      · exact prime_sixtyBF_741168581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 6694851809492770321) ^ 3347425904746385160 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (7 : ZMod 6694851809492770321) ^ 2231617269830923440 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (7 : ZMod 6694851809492770321) ^ 1338970361898554064 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (7 : ZMod 6694851809492770321) ^ 1600924134960 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (7 : ZMod 6694851809492770321) ^ 9032832720 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_15513859191818442967 : Nat.Prime 15513859191818442967 := by
  apply lucas_primality 15513859191818442967 (5 : ZMod 15513859191818442967)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (369377599805201023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (369377599805201023, 1)] : List FactorBlock).map factorBlockValue).prod) = 15513859191818442967 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_7
      · exact prime_sixtyBF_369377599805201023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 15513859191818442967) ^ 7756929595909221483 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 15513859191818442967) ^ 5171286397272814322 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 15513859191818442967) ^ 2216265598831206138 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 15513859191818442967) ^ 42 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_15543715043628378773 : Nat.Prime 15543715043628378773 := by
  apply lucas_primality 15543715043628378773 (2 : ZMod 15543715043628378773)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (1409, 1), (250721256913807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (1409, 1), (250721256913807, 1)] : List FactorBlock).map factorBlockValue).prod) = 15543715043628378773 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_11
      · exact prime_sixtyBF_1409
      · exact prime_sixtyBF_250721256913807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 15543715043628378773) ^ 7771857521814189386 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 15543715043628378773) ^ 1413065003966216252 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 15543715043628378773) ^ 11031735304207508 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 15543715043628378773) ^ 61996 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_18431024013846647851 : Nat.Prime 18431024013846647851 := by
  apply lucas_primality 18431024013846647851 (3 : ZMod 18431024013846647851)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (263, 1), (281, 1), (670951, 1), (2478023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (263, 1), (281, 1), (670951, 1), (2478023, 1)] : List FactorBlock).map factorBlockValue).prod) = 18431024013846647851 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_5
      · exact prime_sixtyBF_263
      · exact prime_sixtyBF_281
      · exact prime_sixtyBF_670951
      · exact prime_sixtyBF_2478023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 18431024013846647851) ^ 9215512006923323925 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 18431024013846647851) ^ 6143674671282215950 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 18431024013846647851) ^ 3686204802769329570 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 18431024013846647851) ^ 70079939216146950 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 18431024013846647851) ^ 65590832789489850 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 18431024013846647851) ^ 27470000065350 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 18431024013846647851) ^ 7437793762950 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_20611688813809581533 : Nat.Prime 20611688813809581533 := by
  apply lucas_primality 20611688813809581533 (3 : ZMod 20611688813809581533)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (59, 1), (3433, 1), (10427, 1), (221807237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (59, 1), (3433, 1), (10427, 1), (221807237, 1)] : List FactorBlock).map factorBlockValue).prod) = 20611688813809581533 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_11
      · exact prime_sixtyBF_59
      · exact prime_sixtyBF_3433
      · exact prime_sixtyBF_10427
      · exact prime_sixtyBF_221807237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 20611688813809581533) ^ 10305844406904790766 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 20611688813809581533) ^ 1873789892164507412 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 20611688813809581533) ^ 349350657861179348 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 20611688813809581533) ^ 6003987420276604 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 20611688813809581533) ^ 1976761179036116 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 20611688813809581533) ^ 92926133036 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_29160255200269631371 : Nat.Prime 29160255200269631371 := by
  apply lucas_primality 29160255200269631371 (3 : ZMod 29160255200269631371)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (386629037, 1), (2514059767, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (386629037, 1), (2514059767, 1)] : List FactorBlock).map factorBlockValue).prod) = 29160255200269631371 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_5
      · exact prime_sixtyBF_386629037
      · exact prime_sixtyBF_2514059767
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 29160255200269631371) ^ 14580127600134815685 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 29160255200269631371) ^ 9720085066756543790 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 29160255200269631371) ^ 5832051040053926274 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 29160255200269631371) ^ 75421793010 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 29160255200269631371) ^ 11598871110 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_31087430087256757547 : Nat.Prime 31087430087256757547 := by
  apply lucas_primality 31087430087256757547 (2 : ZMod 31087430087256757547)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (15543715043628378773, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (15543715043628378773, 1)] : List FactorBlock).map factorBlockValue).prod) = 31087430087256757547 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_15543715043628378773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 31087430087256757547) ^ 15543715043628378773 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 31087430087256757547) ^ 2 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_37024726263431316541 : Nat.Prime 37024726263431316541 := by
  apply lucas_primality 37024726263431316541 (2 : ZMod 37024726263431316541)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (13, 1), (47467597773629893, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (13, 1), (47467597773629893, 1)] : List FactorBlock).map factorBlockValue).prod) = 37024726263431316541 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_5
      · exact prime_sixtyBF_13
      · exact prime_sixtyBF_47467597773629893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 37024726263431316541) ^ 18512363131715658270 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 37024726263431316541) ^ 12341575421143772180 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 37024726263431316541) ^ 7404945252686263308 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 37024726263431316541) ^ 2848055866417793580 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 37024726263431316541) ^ 780 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_37071277321118646079 : Nat.Prime 37071277321118646079 := by
  apply lucas_primality 37071277321118646079 (3 : ZMod 37071277321118646079)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (71, 1), (73, 1), (40099, 1), (900860633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (71, 1), (73, 1), (40099, 1), (900860633, 1)] : List FactorBlock).map factorBlockValue).prod) = 37071277321118646079 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_11
      · exact prime_sixtyBF_71
      · exact prime_sixtyBF_73
      · exact prime_sixtyBF_40099
      · exact prime_sixtyBF_900860633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 37071277321118646079) ^ 18535638660559323039 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 37071277321118646079) ^ 12357092440372882026 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 37071277321118646079) ^ 3370116120101695098 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 37071277321118646079) ^ 522130666494628818 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 37071277321118646079) ^ 507825716727652686 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 37071277321118646079) ^ 924493810846122 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 37071277321118646079) ^ 41150957166 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_81007346502748314931 : Nat.Prime 81007346502748314931 := by
  apply lucas_primality 81007346502748314931 (2 : ZMod 81007346502748314931)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (17, 1), (1187, 1), (133814603470189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (17, 1), (1187, 1), (133814603470189, 1)] : List FactorBlock).map factorBlockValue).prod) = 81007346502748314931 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_5
      · exact prime_sixtyBF_17
      · exact prime_sixtyBF_1187
      · exact prime_sixtyBF_133814603470189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 81007346502748314931) ^ 40503673251374157465 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 81007346502748314931) ^ 27002448834249438310 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 81007346502748314931) ^ 16201469300549662986 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 81007346502748314931) ^ 4765138029573430290 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 81007346502748314931) ^ 68245447769796390 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 81007346502748314931) ^ 605370 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_92400040548585484609 : Nat.Prime 92400040548585484609 := by
  apply lucas_primality 92400040548585484609 (7 : ZMod 92400040548585484609)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (7699, 1), (62508145368301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (7699, 1), (62508145368301, 1)] : List FactorBlock).map factorBlockValue).prod) = 92400040548585484609 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_7699
      · exact prime_sixtyBF_62508145368301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 92400040548585484609) ^ 46200020274292742304 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (7 : ZMod 92400040548585484609) ^ 30800013516195161536 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (7 : ZMod 92400040548585484609) ^ 12001563910713792 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (7 : ZMod 92400040548585484609) ^ 1478208 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_105909531356455716343 : Nat.Prime 105909531356455716343 := by
  apply lucas_primality 105909531356455716343 (3 : ZMod 105909531356455716343)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2574947, 1), (6855126944131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2574947, 1), (6855126944131, 1)] : List FactorBlock).map factorBlockValue).prod) = 105909531356455716343 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_2574947
      · exact prime_sixtyBF_6855126944131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 105909531356455716343) ^ 52954765678227858171 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 105909531356455716343) ^ 35303177118818572114 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 105909531356455716343) ^ 41130761664786 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 105909531356455716343) ^ 15449682 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_210387523943141401349 : Nat.Prime 210387523943141401349 := by
  apply lucas_primality 210387523943141401349 (2 : ZMod 210387523943141401349)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (229, 1), (229680702994695853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (229, 1), (229680702994695853, 1)] : List FactorBlock).map factorBlockValue).prod) = 210387523943141401349 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_229
      · exact prime_sixtyBF_229680702994695853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 210387523943141401349) ^ 105193761971570700674 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 210387523943141401349) ^ 918722811978783412 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 210387523943141401349) ^ 916 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_225872981898766650991 : Nat.Prime 225872981898766650991 := by
  apply lucas_primality 225872981898766650991 (3 : ZMod 225872981898766650991)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (881, 1), (2848694436861731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (881, 1), (2848694436861731, 1)] : List FactorBlock).map factorBlockValue).prod) = 225872981898766650991 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_5
      · exact prime_sixtyBF_881
      · exact prime_sixtyBF_2848694436861731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 225872981898766650991) ^ 112936490949383325495 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 225872981898766650991) ^ 75290993966255550330 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 225872981898766650991) ^ 45174596379753330198 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 225872981898766650991) ^ 256382499317555790 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 225872981898766650991) ^ 79290 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_467365062766619190829 : Nat.Prime 467365062766619190829 := by
  apply lucas_primality 467365062766619190829 (6 : ZMod 467365062766619190829)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1117, 1), (34867581525411757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1117, 1), (34867581525411757, 1)] : List FactorBlock).map factorBlockValue).prod) = 467365062766619190829 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_1117
      · exact prime_sixtyBF_34867581525411757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 467365062766619190829) ^ 233682531383309595414 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (6 : ZMod 467365062766619190829) ^ 155788354255539730276 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (6 : ZMod 467365062766619190829) ^ 418410978304941084 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (6 : ZMod 467365062766619190829) ^ 13404 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_832019020246988845541 : Nat.Prime 832019020246988845541 := by
  apply lucas_primality 832019020246988845541 (3 : ZMod 832019020246988845541)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (739, 1), (56293573765019543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (739, 1), (56293573765019543, 1)] : List FactorBlock).map factorBlockValue).prod) = 832019020246988845541 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_5
      · exact prime_sixtyBF_739
      · exact prime_sixtyBF_56293573765019543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 832019020246988845541) ^ 416009510123494422770 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 832019020246988845541) ^ 166403804049397769108 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 832019020246988845541) ^ 1125871475300390860 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 832019020246988845541) ^ 14780 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_1492320900985198295147 : Nat.Prime 1492320900985198295147 := by
  apply lucas_primality 1492320900985198295147 (2 : ZMod 1492320900985198295147)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1051, 1), (19843, 1), (35778504001061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1051, 1), (19843, 1), (35778504001061, 1)] : List FactorBlock).map factorBlockValue).prod) = 1492320900985198295147 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_1051
      · exact prime_sixtyBF_19843
      · exact prime_sixtyBF_35778504001061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1492320900985198295147) ^ 746160450492599147573 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1492320900985198295147) ^ 1419905709786106846 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1492320900985198295147) ^ 75206415410230222 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1492320900985198295147) ^ 41709986 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_1494481506409299771637 : Nat.Prime 1494481506409299771637 := by
  apply lucas_primality 1494481506409299771637 (5 : ZMod 1494481506409299771637)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (13, 1), (389, 1), (599783, 1), (5865758159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (13, 1), (389, 1), (599783, 1), (5865758159, 1)] : List FactorBlock).map factorBlockValue).prod) = 1494481506409299771637 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_7
      · exact prime_sixtyBF_13
      · exact prime_sixtyBF_389
      · exact prime_sixtyBF_599783
      · exact prime_sixtyBF_5865758159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1494481506409299771637) ^ 747240753204649885818 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1494481506409299771637) ^ 498160502136433257212 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1494481506409299771637) ^ 213497358058471395948 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1494481506409299771637) ^ 114960115877638443972 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1494481506409299771637) ^ 3841854772260410724 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1494481506409299771637) ^ 2491703676845292 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1494481506409299771637) ^ 254780621004 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_1637925539288993603527 : Nat.Prime 1637925539288993603527 := by
  apply lucas_primality 1637925539288993603527 (3 : ZMod 1637925539288993603527)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (877, 1), (6067, 1), (51306136940519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (877, 1), (6067, 1), (51306136940519, 1)] : List FactorBlock).map factorBlockValue).prod) = 1637925539288993603527 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_877
      · exact prime_sixtyBF_6067
      · exact prime_sixtyBF_51306136940519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1637925539288993603527) ^ 818962769644496801763 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1637925539288993603527) ^ 545975179762997867842 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1637925539288993603527) ^ 1867645996908772638 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1637925539288993603527) ^ 269972892581010978 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1637925539288993603527) ^ 31924554 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_1906899653568562109341 : Nat.Prime 1906899653568562109341 := by
  apply lucas_primality 1906899653568562109341 (2 : ZMod 1906899653568562109341)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (13, 2), (188057165046209281, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (13, 2), (188057165046209281, 1)] : List FactorBlock).map factorBlockValue).prod) = 1906899653568562109341 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_5
      · exact prime_sixtyBF_13
      · exact prime_sixtyBF_188057165046209281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1906899653568562109341) ^ 953449826784281054670 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1906899653568562109341) ^ 635633217856187369780 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1906899653568562109341) ^ 381379930713712421868 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1906899653568562109341) ^ 146684588736043239180 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1906899653568562109341) ^ 10140 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_2356120533006385347557 : Nat.Prime 2356120533006385347557 := by
  apply lucas_primality 2356120533006385347557 (2 : ZMod 2356120533006385347557)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (101, 1), (5831981517342537989, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (101, 1), (5831981517342537989, 1)] : List FactorBlock).map factorBlockValue).prod) = 2356120533006385347557 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_101
      · exact prime_sixtyBF_5831981517342537989
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2356120533006385347557) ^ 1178060266503192673778 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2356120533006385347557) ^ 23327926069370151956 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2356120533006385347557) ^ 404 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_3301541053026890057003 : Nat.Prime 3301541053026890057003 := by
  apply lucas_primality 3301541053026890057003 (2 : ZMod 3301541053026890057003)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (188249, 1), (515828230792397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (188249, 1), (515828230792397, 1)] : List FactorBlock).map factorBlockValue).prod) = 3301541053026890057003 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_17
      · exact prime_sixtyBF_188249
      · exact prime_sixtyBF_515828230792397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3301541053026890057003) ^ 1650770526513445028501 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 3301541053026890057003) ^ 194208297236875885706 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 3301541053026890057003) ^ 17538159846941498 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 3301541053026890057003) ^ 6400466 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_3719617620598198702543 : Nat.Prime 3719617620598198702543 := by
  apply lucas_primality 3719617620598198702543 (3 : ZMod 3719617620598198702543)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (29, 1), (1231, 1), (5087, 1), (179670036731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (29, 1), (1231, 1), (5087, 1), (179670036731, 1)] : List FactorBlock).map factorBlockValue).prod) = 3719617620598198702543 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_19
      · exact prime_sixtyBF_29
      · exact prime_sixtyBF_1231
      · exact prime_sixtyBF_5087
      · exact prime_sixtyBF_179670036731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3719617620598198702543) ^ 1859808810299099351271 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 3719617620598198702543) ^ 1239872540199399567514 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 3719617620598198702543) ^ 195769348452536773818 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 3719617620598198702543) ^ 128262676572351679398 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 3719617620598198702543) ^ 3021622762468073682 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 3719617620598198702543) ^ 731200633103636466 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 3719617620598198702543) ^ 20702492682 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_6603082106053780114007 : Nat.Prime 6603082106053780114007 := by
  apply lucas_primality 6603082106053780114007 (5 : ZMod 6603082106053780114007)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3301541053026890057003, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3301541053026890057003, 1)] : List FactorBlock).map factorBlockValue).prod) = 6603082106053780114007 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3301541053026890057003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 6603082106053780114007) ^ 3301541053026890057003 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 6603082106053780114007) ^ 2 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_8697713680549786290863 : Nat.Prime 8697713680549786290863 := by
  apply lucas_primality 8697713680549786290863 (5 : ZMod 8697713680549786290863)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7459, 1), (20231, 1), (28818883683739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7459, 1), (20231, 1), (28818883683739, 1)] : List FactorBlock).map factorBlockValue).prod) = 8697713680549786290863 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_7459
      · exact prime_sixtyBF_20231
      · exact prime_sixtyBF_28818883683739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 8697713680549786290863) ^ 4348856840274893145431 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 8697713680549786290863) ^ 1166069671611447418 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 8697713680549786290863) ^ 429920106794018402 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 8697713680549786290863) ^ 301806058 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_9013904614487703594707 : Nat.Prime 9013904614487703594707 := by
  apply lucas_primality 9013904614487703594707 (2 : ZMod 9013904614487703594707)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (3881, 1), (8526173, 1), (19457504483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (3881, 1), (8526173, 1), (19457504483, 1)] : List FactorBlock).map factorBlockValue).prod) = 9013904614487703594707 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_7
      · exact prime_sixtyBF_3881
      · exact prime_sixtyBF_8526173
      · exact prime_sixtyBF_19457504483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9013904614487703594707) ^ 4506952307243851797353 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 9013904614487703594707) ^ 1287700659212529084958 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 9013904614487703594707) ^ 2322572691184669826 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 9013904614487703594707) ^ 1057204048579322 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 9013904614487703594707) ^ 463261083782 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_21408453961441290775583 : Nat.Prime 21408453961441290775583 := by
  apply lucas_primality 21408453961441290775583 (5 : ZMod 21408453961441290775583)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (65287927, 1), (163954156190633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (65287927, 1), (163954156190633, 1)] : List FactorBlock).map factorBlockValue).prod) = 21408453961441290775583 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_65287927
      · exact prime_sixtyBF_163954156190633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 21408453961441290775583) ^ 10704226980720645387791 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 21408453961441290775583) ^ 327908312381266 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 21408453961441290775583) ^ 130575854 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_30248054402724838720147 : Nat.Prime 30248054402724838720147 := by
  apply lucas_primality 30248054402724838720147 (2 : ZMod 30248054402724838720147)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (6109799, 1), (35874960865283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (6109799, 1), (35874960865283, 1)] : List FactorBlock).map factorBlockValue).prod) = 30248054402724838720147 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_23
      · exact prime_sixtyBF_6109799
      · exact prime_sixtyBF_35874960865283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 30248054402724838720147) ^ 15124027201362419360073 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 30248054402724838720147) ^ 10082684800908279573382 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 30248054402724838720147) ^ 1315132800118471248702 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 30248054402724838720147) ^ 4950744599409054 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 30248054402724838720147) ^ 843152262 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_74387675580793747110349 : Nat.Prime 74387675580793747110349 := by
  apply lucas_primality 74387675580793747110349 (2 : ZMod 74387675580793747110349)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (203279, 1), (391249, 1), (77942437999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (203279, 1), (391249, 1), (77942437999, 1)] : List FactorBlock).map factorBlockValue).prod) = 74387675580793747110349 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_203279
      · exact prime_sixtyBF_391249
      · exact prime_sixtyBF_77942437999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 74387675580793747110349) ^ 37193837790396873555174 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 74387675580793747110349) ^ 24795891860264582370116 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 74387675580793747110349) ^ 365938811096049012 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 74387675580793747110349) ^ 190128730247984652 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 74387675580793747110349) ^ 954392465652 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_212681918760682924377889 : Nat.Prime 212681918760682924377889 := by
  apply lucas_primality 212681918760682924377889 (31 : ZMod 212681918760682924377889)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (7, 1), (20675593, 1), (15307466660653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (7, 1), (20675593, 1), (15307466660653, 1)] : List FactorBlock).map factorBlockValue).prod) = 212681918760682924377889 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_7
      · exact prime_sixtyBF_20675593
      · exact prime_sixtyBF_15307466660653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (31 : ZMod 212681918760682924377889) ^ 106340959380341462188944 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (31 : ZMod 212681918760682924377889) ^ 70893972920227641459296 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (31 : ZMod 212681918760682924377889) ^ 30383131251526132053984 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (31 : ZMod 212681918760682924377889) ^ 10286617595958816 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (31 : ZMod 212681918760682924377889) ^ 13893998496 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_513021624535653437457469 : Nat.Prime 513021624535653437457469 := by
  apply lucas_primality 513021624535653437457469 (7 : ZMod 513021624535653437457469)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (3329, 1), (51349, 1), (83365696959803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (3329, 1), (51349, 1), (83365696959803, 1)] : List FactorBlock).map factorBlockValue).prod) = 513021624535653437457469 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_3329
      · exact prime_sixtyBF_51349
      · exact prime_sixtyBF_83365696959803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 513021624535653437457469) ^ 256510812267826718728734 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (7 : ZMod 513021624535653437457469) ^ 171007208178551145819156 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (7 : ZMod 513021624535653437457469) ^ 154106826234801272892 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (7 : ZMod 513021624535653437457469) ^ 9990878586450630732 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (7 : ZMod 513021624535653437457469) ^ 6153869556 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_1008932312769092229201253 : Nat.Prime 1008932312769092229201253 := by
  apply lucas_primality 1008932312769092229201253 (2 : ZMod 1008932312769092229201253)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (59, 1), (97, 1), (3371, 1), (11071, 1), (44279, 1), (8890243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (59, 1), (97, 1), (3371, 1), (11071, 1), (44279, 1), (8890243, 1)] : List FactorBlock).map factorBlockValue).prod) = 1008932312769092229201253 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_59
      · exact prime_sixtyBF_97
      · exact prime_sixtyBF_3371
      · exact prime_sixtyBF_11071
      · exact prime_sixtyBF_44279
      · exact prime_sixtyBF_8890243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1008932312769092229201253) ^ 504466156384546114600626 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1008932312769092229201253) ^ 336310770923030743067084 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1008932312769092229201253) ^ 17100547674052410664428 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1008932312769092229201253) ^ 10401364049165899270116 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1008932312769092229201253) ^ 299297630604892384812 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1008932312769092229201253) ^ 91132897910675840412 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1008932312769092229201253) ^ 22785797167259699388 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1008932312769092229201253) ^ 113487596769749964 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_1016333501148623652511343 : Nat.Prime 1016333501148623652511343 := by
  apply lucas_primality 1016333501148623652511343 (5 : ZMod 1016333501148623652511343)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (617333, 1), (22278941, 1), (5278301201, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (617333, 1), (22278941, 1), (5278301201, 1)] : List FactorBlock).map factorBlockValue).prod) = 1016333501148623652511343 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_7
      · exact prime_sixtyBF_617333
      · exact prime_sixtyBF_22278941
      · exact prime_sixtyBF_5278301201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1016333501148623652511343) ^ 508166750574311826255671 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1016333501148623652511343) ^ 145190500164089093215906 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1016333501148623652511343) ^ 1646329454522313974 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1016333501148623652511343) ^ 45618573214437062 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1016333501148623652511343) ^ 192549356780942 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_1315091083540402974614047 : Nat.Prime 1315091083540402974614047 := by
  apply lucas_primality 1315091083540402974614047 (3 : ZMod 1315091083540402974614047)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (26356633, 1), (1188000472793611, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (26356633, 1), (1188000472793611, 1)] : List FactorBlock).map factorBlockValue).prod) = 1315091083540402974614047 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_7
      · exact prime_sixtyBF_26356633
      · exact prime_sixtyBF_1188000472793611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1315091083540402974614047) ^ 657545541770201487307023 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1315091083540402974614047) ^ 438363694513467658204682 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1315091083540402974614047) ^ 187870154791486139230578 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1315091083540402974614047) ^ 49896019857331662 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 1315091083540402974614047) ^ 1106978586 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_1374888805794653185461133 : Nat.Prime 1374888805794653185461133 := by
  apply lucas_primality 1374888805794653185461133 (5 : ZMod 1374888805794653185461133)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (109, 1), (92461, 1), (268883, 1), (4697809387, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (109, 1), (92461, 1), (268883, 1), (4697809387, 1)] : List FactorBlock).map factorBlockValue).prod) = 1374888805794653185461133 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_109
      · exact prime_sixtyBF_92461
      · exact prime_sixtyBF_268883
      · exact prime_sixtyBF_4697809387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1374888805794653185461133) ^ 687444402897326592730566 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1374888805794653185461133) ^ 458296268598217728487044 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1374888805794653185461133) ^ 12613658768758286105148 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1374888805794653185461133) ^ 14869932250296375612 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1374888805794653185461133) ^ 5113334817726123204 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 1374888805794653185461133) ^ 292665941193636 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_2467597072604770461289237 : Nat.Prime 2467597072604770461289237 := by
  apply lucas_primality 2467597072604770461289237 (5 : ZMod 2467597072604770461289237)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (4766297, 1), (43143154818873199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (4766297, 1), (43143154818873199, 1)] : List FactorBlock).map factorBlockValue).prod) = 2467597072604770461289237 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_4766297
      · exact prime_sixtyBF_43143154818873199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2467597072604770461289237) ^ 1233798536302385230644618 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 2467597072604770461289237) ^ 822532357534923487096412 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 2467597072604770461289237) ^ 517717857826478388 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 2467597072604770461289237) ^ 57195564 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_2577804093544928281513253 : Nat.Prime 2577804093544928281513253 := by
  apply lucas_primality 2577804093544928281513253 (2 : ZMod 2577804093544928281513253)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (173, 1), (12263, 1), (303771542379342187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (173, 1), (12263, 1), (303771542379342187, 1)] : List FactorBlock).map factorBlockValue).prod) = 2577804093544928281513253 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_173
      · exact prime_sixtyBF_12263
      · exact prime_sixtyBF_303771542379342187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2577804093544928281513253) ^ 1288902046772464140756626 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2577804093544928281513253) ^ 14900601696791492956724 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2577804093544928281513253) ^ 210209907326504793404 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 2577804093544928281513253) ^ 8485996 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_38364528418696233883548781 : Nat.Prime 38364528418696233883548781 := by
  apply lucas_primality 38364528418696233883548781 (2 : ZMod 38364528418696233883548781)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (17, 1), (47, 1), (61, 1), (96013, 1), (1108201, 1), (123297259, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (17, 1), (47, 1), (61, 1), (96013, 1), (1108201, 1), (123297259, 1)] : List FactorBlock).map factorBlockValue).prod) = 38364528418696233883548781 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_5
      · exact prime_sixtyBF_17
      · exact prime_sixtyBF_47
      · exact prime_sixtyBF_61
      · exact prime_sixtyBF_96013
      · exact prime_sixtyBF_1108201
      · exact prime_sixtyBF_123297259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 38364528418696233883548781) ^ 19182264209348116941774390 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 38364528418696233883548781) ^ 12788176139565411294516260 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 38364528418696233883548781) ^ 7672905683739246776709756 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 38364528418696233883548781) ^ 2256736965805660816679340 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 38364528418696233883548781) ^ 816266562099919869862740 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 38364528418696233883548781) ^ 628926695388462850549980 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 38364528418696233883548781) ^ 399576395057921676060 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 38364528418696233883548781) ^ 34618745533252752780 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 38364528418696233883548781) ^ 311154755019300420 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_78905465012424178476842821 : Nat.Prime 78905465012424178476842821 := by
  apply lucas_primality 78905465012424178476842821 (2 : ZMod 78905465012424178476842821)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (1315091083540402974614047, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (1315091083540402974614047, 1)] : List FactorBlock).map factorBlockValue).prod) = 78905465012424178476842821 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_5
      · exact prime_sixtyBF_1315091083540402974614047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 78905465012424178476842821) ^ 39452732506212089238421410 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 78905465012424178476842821) ^ 26301821670808059492280940 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 78905465012424178476842821) ^ 15781093002484835695368564 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 78905465012424178476842821) ^ 60 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_121883183928126007647219409 : Nat.Prime 121883183928126007647219409 := by
  apply lucas_primality 121883183928126007647219409 (11 : ZMod 121883183928126007647219409)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (139, 1), (17239, 1), (22143217, 1), (47855842603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (139, 1), (17239, 1), (22143217, 1), (47855842603, 1)] : List FactorBlock).map factorBlockValue).prod) = 121883183928126007647219409 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_139
      · exact prime_sixtyBF_17239
      · exact prime_sixtyBF_22143217
      · exact prime_sixtyBF_47855842603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 121883183928126007647219409) ^ 60941591964063003823609704 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (11 : ZMod 121883183928126007647219409) ^ 40627727976042002549073136 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (11 : ZMod 121883183928126007647219409) ^ 876857438331841781634672 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (11 : ZMod 121883183928126007647219409) ^ 7070200355480364733872 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (11 : ZMod 121883183928126007647219409) ^ 5504312400864156624 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (11 : ZMod 121883183928126007647219409) ^ 2546881995981936 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_127582757277282979227844777 : Nat.Prime 127582757277282979227844777 := by
  apply lucas_primality 127582757277282979227844777 (13 : ZMod 127582757277282979227844777)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (97, 1), (17239, 1), (22143217, 1), (47855842603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (97, 1), (17239, 1), (22143217, 1), (47855842603, 1)] : List FactorBlock).map factorBlockValue).prod) = 127582757277282979227844777 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_97
      · exact prime_sixtyBF_17239
      · exact prime_sixtyBF_22143217
      · exact prime_sixtyBF_47855842603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 127582757277282979227844777) ^ 63791378638641489613922388 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (13 : ZMod 127582757277282979227844777) ^ 42527585759094326409281592 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (13 : ZMod 127582757277282979227844777) ^ 1315286157497762672452008 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (13 : ZMod 127582757277282979227844777) ^ 7400821235412899775384 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (13 : ZMod 127582757277282979227844777) ^ 5761708304501689128 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (13 : ZMod 127582757277282979227844777) ^ 2665980794355192 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_184249384535504770001770639 : Nat.Prime 184249384535504770001770639 := by
  apply lucas_primality 184249384535504770001770639 (3 : ZMod 184249384535504770001770639)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (47, 1), (101, 1), (145299083, 1), (44521797530773, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (47, 1), (101, 1), (145299083, 1), (44521797530773, 1)] : List FactorBlock).map factorBlockValue).prod) = 184249384535504770001770639 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_47
      · exact prime_sixtyBF_101
      · exact prime_sixtyBF_145299083
      · exact prime_sixtyBF_44521797530773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 184249384535504770001770639) ^ 92124692267752385000885319 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 184249384535504770001770639) ^ 61416461511834923333923546 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 184249384535504770001770639) ^ 3920199670968186595782354 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 184249384535504770001770639) ^ 1824251332034700693086838 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 184249384535504770001770639) ^ 1268069837271476586 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 184249384535504770001770639) ^ 4138408482006 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_417270664977466685004009977 : Nat.Prime 417270664977466685004009977 := by
  apply lucas_primality 417270664977466685004009977 (3 : ZMod 417270664977466685004009977)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (47729419, 1), (1092802598795165213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (47729419, 1), (1092802598795165213, 1)] : List FactorBlock).map factorBlockValue).prod) = 417270664977466685004009977 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_47729419
      · exact prime_sixtyBF_1092802598795165213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 417270664977466685004009977) ^ 208635332488733342502004988 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 417270664977466685004009977) ^ 8742420790361321704 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 417270664977466685004009977) ^ 381835352 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_541496282795185774432684703 : Nat.Prime 541496282795185774432684703 := by
  apply lucas_primality 541496282795185774432684703 (5 : ZMod 541496282795185774432684703)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (325411, 1), (832019020246988845541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (325411, 1), (832019020246988845541, 1)] : List FactorBlock).map factorBlockValue).prod) = 541496282795185774432684703 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_325411
      · exact prime_sixtyBF_832019020246988845541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 541496282795185774432684703) ^ 270748141397592887216342351 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 541496282795185774432684703) ^ 1664038040493977691082 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (5 : ZMod 541496282795185774432684703) ^ 650822 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_545661638816687203466782277 : Nat.Prime 545661638816687203466782277 := by
  apply lucas_primality 545661638816687203466782277 (2 : ZMod 545661638816687203466782277)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (20405767, 1), (644963491, 1), (10365144877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (20405767, 1), (644963491, 1), (10365144877, 1)] : List FactorBlock).map factorBlockValue).prod) = 545661638816687203466782277 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_20405767
      · exact prime_sixtyBF_644963491
      · exact prime_sixtyBF_10365144877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 545661638816687203466782277) ^ 272830819408343601733391138 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 545661638816687203466782277) ^ 26740560098362742428 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 545661638816687203466782277) ^ 846034925125222636 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 545661638816687203466782277) ^ 52643898883410388 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_606290709796319114963091419 : Nat.Prime 606290709796319114963091419 := by
  apply lucas_primality 606290709796319114963091419 (2 : ZMod 606290709796319114963091419)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (865661, 1), (18431024013846647851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (865661, 1), (18431024013846647851, 1)] : List FactorBlock).map factorBlockValue).prod) = 606290709796319114963091419 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_19
      · exact prime_sixtyBF_865661
      · exact prime_sixtyBF_18431024013846647851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 606290709796319114963091419) ^ 303145354898159557481545709 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 606290709796319114963091419) ^ 31910037357701006050689022 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 606290709796319114963091419) ^ 700378912526172618338 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 606290709796319114963091419) ^ 32895118 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_762752828453433725276147269 : Nat.Prime 762752828453433725276147269 := by
  apply lucas_primality 762752828453433725276147269 (6 : ZMod 762752828453433725276147269)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (7, 1), (1008932312769092229201253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (7, 1), (1008932312769092229201253, 1)] : List FactorBlock).map factorBlockValue).prod) = 762752828453433725276147269 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_7
      · exact prime_sixtyBF_1008932312769092229201253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 762752828453433725276147269) ^ 381376414226716862638073634 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (6 : ZMod 762752828453433725276147269) ^ 254250942817811241758715756 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (6 : ZMod 762752828453433725276147269) ^ 108964689779061960753735324 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (6 : ZMod 762752828453433725276147269) ^ 756 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_1576355845470429698904037691 : Nat.Prime 1576355845470429698904037691 := by
  apply lucas_primality 1576355845470429698904037691 (2 : ZMod 1576355845470429698904037691)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (23, 1), (29, 1), (61, 1), (2087, 1), (6011, 1), (1325083, 1), (33295711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (23, 1), (29, 1), (61, 1), (2087, 1), (6011, 1), (1325083, 1), (33295711, 1)] : List FactorBlock).map factorBlockValue).prod) = 1576355845470429698904037691 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_5
      · exact prime_sixtyBF_7
      · exact prime_sixtyBF_23
      · exact prime_sixtyBF_29
      · exact prime_sixtyBF_61
      · exact prime_sixtyBF_2087
      · exact prime_sixtyBF_6011
      · exact prime_sixtyBF_1325083
      · exact prime_sixtyBF_33295711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1576355845470429698904037691) ^ 788177922735214849452018845 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1576355845470429698904037691) ^ 315271169094085939780807538 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1576355845470429698904037691) ^ 225193692210061385557719670 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1576355845470429698904037691) ^ 68537210672627378213219030 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1576355845470429698904037691) ^ 54357098119669989617380610 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1576355845470429698904037691) ^ 25841899106072618014820290 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1576355845470429698904037691) ^ 755321440091245663106870 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1576355845470429698904037691) ^ 262245191394182282299790 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1576355845470429698904037691) ^ 1189628004789458244430 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1576355845470429698904037691) ^ 47344111242148566790 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_1917189541788360444613018811 : Nat.Prime 1917189541788360444613018811 := by
  apply lucas_primality 1917189541788360444613018811 (2 : ZMod 1917189541788360444613018811)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (848791, 1), (225872981898766650991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (848791, 1), (225872981898766650991, 1)] : List FactorBlock).map factorBlockValue).prod) = 1917189541788360444613018811 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_5
      · exact prime_sixtyBF_848791
      · exact prime_sixtyBF_225872981898766650991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1917189541788360444613018811) ^ 958594770894180222306509405 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1917189541788360444613018811) ^ 383437908357672088922603762 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1917189541788360444613018811) ^ 2258729818987666509910 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 1917189541788360444613018811) ^ 8487910 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_2026743229890552470019477031 : Nat.Prime 2026743229890552470019477031 := by
  apply lucas_primality 2026743229890552470019477031 (17 : ZMod 2026743229890552470019477031)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (23, 1), (29, 1), (61, 1), (2087, 1), (6011, 1), (1325083, 1), (33295711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (23, 1), (29, 1), (61, 1), (2087, 1), (6011, 1), (1325083, 1), (33295711, 1)] : List FactorBlock).map factorBlockValue).prod) = 2026743229890552470019477031 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_5
      · exact prime_sixtyBF_23
      · exact prime_sixtyBF_29
      · exact prime_sixtyBF_61
      · exact prime_sixtyBF_2087
      · exact prime_sixtyBF_6011
      · exact prime_sixtyBF_1325083
      · exact prime_sixtyBF_33295711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 2026743229890552470019477031) ^ 1013371614945276235009738515 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (17 : ZMod 2026743229890552470019477031) ^ 675581076630184156673159010 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (17 : ZMod 2026743229890552470019477031) ^ 405348645978110494003895406 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (17 : ZMod 2026743229890552470019477031) ^ 88119270864806629131281610 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (17 : ZMod 2026743229890552470019477031) ^ 69887697582432843793775070 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (17 : ZMod 2026743229890552470019477031) ^ 33225298850664794590483230 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (17 : ZMod 2026743229890552470019477031) ^ 971127565831601566851690 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (17 : ZMod 2026743229890552470019477031) ^ 337172388935377220099730 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (17 : ZMod 2026743229890552470019477031) ^ 1529521720443589171410 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (17 : ZMod 2026743229890552470019477031) ^ 60871000168476728730 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_3377905383150920783365795049 : Nat.Prime 3377905383150920783365795049 := by
  apply lucas_primality 3377905383150920783365795049 (3 : ZMod 3377905383150920783365795049)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (751, 1), (29789, 1), (574363039, 1), (32860574161, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (751, 1), (29789, 1), (574363039, 1), (32860574161, 1)] : List FactorBlock).map factorBlockValue).prod) = 3377905383150920783365795049 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_751
      · exact prime_sixtyBF_29789
      · exact prime_sixtyBF_574363039
      · exact prime_sixtyBF_32860574161
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3377905383150920783365795049) ^ 1688952691575460391682897524 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 3377905383150920783365795049) ^ 4497876675300826609009048 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 3377905383150920783365795049) ^ 113394386624288186356232 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 3377905383150920783365795049) ^ 5881132931241630232 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 3377905383150920783365795049) ^ 102795081017176168 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_5456616388166872034667822773 : Nat.Prime 5456616388166872034667822773 := by
  apply lucas_primality 5456616388166872034667822773 (2 : ZMod 5456616388166872034667822773)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (53, 1), (7615039, 1), (482855730763388897, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (53, 1), (7615039, 1), (482855730763388897, 1)] : List FactorBlock).map factorBlockValue).prod) = 5456616388166872034667822773 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_7
      · exact prime_sixtyBF_53
      · exact prime_sixtyBF_7615039
      · exact prime_sixtyBF_482855730763388897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5456616388166872034667822773) ^ 2728308194083436017333911386 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 5456616388166872034667822773) ^ 779516626880981719238260396 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 5456616388166872034667822773) ^ 102955026191827774239015524 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 5456616388166872034667822773) ^ 716557904452869123148 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 5456616388166872034667822773) ^ 11300717876 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_7881779227352148494520188449 : Nat.Prime 7881779227352148494520188449 := by
  apply lucas_primality 7881779227352148494520188449 (13 : ZMod 7881779227352148494520188449)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (35322167, 1), (2324372311347287389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (35322167, 1), (2324372311347287389, 1)] : List FactorBlock).map factorBlockValue).prod) = 7881779227352148494520188449 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_3
      · exact prime_sixtyBF_35322167
      · exact prime_sixtyBF_2324372311347287389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 7881779227352148494520188449) ^ 3940889613676074247260094224 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (13 : ZMod 7881779227352148494520188449) ^ 2627259742450716164840062816 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (13 : ZMod 7881779227352148494520188449) ^ 223139741889339589344 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (13 : ZMod 7881779227352148494520188449) ^ 3390928032 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_8867001630771167056335212009 : Nat.Prime 8867001630771167056335212009 := by
  apply lucas_primality 8867001630771167056335212009 (13 : ZMod 8867001630771167056335212009)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (10243, 1), (8033939, 1), (26986489, 1), (71299531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (10243, 1), (8033939, 1), (26986489, 1), (71299531, 1)] : List FactorBlock).map factorBlockValue).prod) = 8867001630771167056335212009 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_7
      · exact prime_sixtyBF_10243
      · exact prime_sixtyBF_8033939
      · exact prime_sixtyBF_26986489
      · exact prime_sixtyBF_71299531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 8867001630771167056335212009) ^ 4433500815385583528167606004 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (13 : ZMod 8867001630771167056335212009) ^ 1266714518681595293762173144 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (13 : ZMod 8867001630771167056335212009) ^ 865664515354014161508856 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (13 : ZMod 8867001630771167056335212009) ^ 1103692924575499895672 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (13 : ZMod 8867001630771167056335212009) ^ 328571887612766783272 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (13 : ZMod 8867001630771167056335212009) ^ 124362692242269686968 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_23645337682056445483560565337 : Nat.Prime 23645337682056445483560565337 := by
  apply lucas_primality 23645337682056445483560565337 (3 : ZMod 23645337682056445483560565337)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (751, 1), (29789, 1), (574363039, 1), (32860574161, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (751, 1), (29789, 1), (574363039, 1), (32860574161, 1)] : List FactorBlock).map factorBlockValue).prod) = 23645337682056445483560565337 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_7
      · exact prime_sixtyBF_751
      · exact prime_sixtyBF_29789
      · exact prime_sixtyBF_574363039
      · exact prime_sixtyBF_32860574161
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 23645337682056445483560565337) ^ 11822668841028222741780282668 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 23645337682056445483560565337) ^ 3377905383150920783365795048 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 23645337682056445483560565337) ^ 31485136727105786263063336 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 23645337682056445483560565337) ^ 793760706370017304493624 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 23645337682056445483560565337) ^ 41167930518691411624 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 23645337682056445483560565337) ^ 719565567120233176 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_35468006523084668225340848033 : Nat.Prime 35468006523084668225340848033 := by
  apply lucas_primality 35468006523084668225340848033 (3 : ZMod 35468006523084668225340848033)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (7, 1), (10243, 1), (8033939, 1), (26986489, 1), (71299531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (7, 1), (10243, 1), (8033939, 1), (26986489, 1), (71299531, 1)] : List FactorBlock).map factorBlockValue).prod) = 35468006523084668225340848033 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_7
      · exact prime_sixtyBF_10243
      · exact prime_sixtyBF_8033939
      · exact prime_sixtyBF_26986489
      · exact prime_sixtyBF_71299531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 35468006523084668225340848033) ^ 17734003261542334112670424016 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 35468006523084668225340848033) ^ 5066858074726381175048692576 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 35468006523084668225340848033) ^ 3462658061416056646035424 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 35468006523084668225340848033) ^ 4414771698301999582688 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 35468006523084668225340848033) ^ 1314287550451067133088 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 35468006523084668225340848033) ^ 497450768969078747872 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_70936013046169336450681696067 : Nat.Prime 70936013046169336450681696067 := by
  apply lucas_primality 70936013046169336450681696067 (2 : ZMod 70936013046169336450681696067)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (35468006523084668225340848033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (35468006523084668225340848033, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696067 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_35468006523084668225340848033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 70936013046169336450681696067) ^ 35468006523084668225340848033 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (2 : ZMod 70936013046169336450681696067) ^ 2 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem prime_sixtyBF_70936013046169336450681696097 : Nat.Prime 70936013046169336450681696097 := by
  apply lucas_primality 70936013046169336450681696097 (3 : ZMod 70936013046169336450681696097)
  · rw [← sixtyBFFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (19, 2), (23, 1), (163, 1), (1637925539288993603527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (19, 2), (23, 1), (163, 1), (1637925539288993603527, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696097 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyBF_2
      · exact prime_sixtyBF_19
      · exact prime_sixtyBF_23
      · exact prime_sixtyBF_163
      · exact prime_sixtyBF_1637925539288993603527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 70936013046169336450681696097) ^ 35468006523084668225340848048 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 70936013046169336450681696097) ^ 3733474370851017707930615584 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 70936013046169336450681696097) ^ 3084174480268232019594856352 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 70936013046169336450681696097) ^ 435190264086928444482709792 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide
    · change (3 : ZMod 70936013046169336450681696097) ^ 43308448 ≠ 1
      rw [← sixtyBFFastPow_eq_pow]
      decide

private theorem phi_sixtyBF_70936013046169336450681696000 : Nat.totient 70936013046169336450681696000 = 28358068700559041630208000000 := by
  rw [← show ((([(2, 8), (5, 3), (1741, 1), (761443, 1), (26809681, 1), (62371901, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696000 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_2, prime_sixtyBF_5, prime_sixtyBF_1741, prime_sixtyBF_761443, prime_sixtyBF_26809681, prime_sixtyBF_62371901]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696001 : Nat.totient 70936013046169336450681696001 = 55988332402516569848165990400 := by
  rw [← show ((([(7, 1), (19, 1), (41, 1), (269, 1), (70715233, 1), (683858140393721, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696001 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_7, prime_sixtyBF_19, prime_sixtyBF_41, prime_sixtyBF_269, prime_sixtyBF_70715233, prime_sixtyBF_683858140393721]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696002 : Nat.totient 70936013046169336450681696002 = 23642587904444856177189625872 := by
  rw [← show ((([(2, 1), (3, 1), (8599, 1), (1374888805794653185461133, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696002 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_2, prime_sixtyBF_3, prime_sixtyBF_8599, prime_sixtyBF_1374888805794653185461133]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696003 : Nat.totient 70936013046169336450681696003 = 69314689656997241492691339840 := by
  rw [← show ((([(59, 1), (223, 2), (653, 1), (37024726263431316541, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696003 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_59, prime_sixtyBF_223, prime_sixtyBF_653, prime_sixtyBF_37024726263431316541]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696004 : Nat.totient 70936013046169336450681696004 = 30837917808662878289977038240 := by
  rw [← show ((([(2, 2), (11, 1), (23, 1), (8059, 1), (8697713680549786290863, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696004 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_2, prime_sixtyBF_11, prime_sixtyBF_23, prime_sixtyBF_8059, prime_sixtyBF_8697713680549786290863]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696005 : Nat.totient 70936013046169336450681696005 = 35471111045347959815885635584 := by
  rw [← show ((([(3, 4), (5, 1), (17, 1), (313, 1), (1597, 1), (20611688813809581533, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696005 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_3, prime_sixtyBF_5, prime_sixtyBF_17, prime_sixtyBF_313, prime_sixtyBF_1597, prime_sixtyBF_20611688813809581533]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696006 : Nat.totient 70936013046169336450681696006 = 34602684670617420178099397280 := by
  rw [← show ((([(2, 1), (47, 1), (317, 1), (29387, 1), (81007346502748314931, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696006 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_2, prime_sixtyBF_47, prime_sixtyBF_317, prime_sixtyBF_29387, prime_sixtyBF_81007346502748314931]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696007 : Nat.totient 70936013046169336450681696007 = 69018823504380976006068677160 := by
  rw [← show ((([(37, 1), (1917189541788360444613018811, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696007 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_37, prime_sixtyBF_1917189541788360444613018811]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696008 : Nat.totient 70936013046169336450681696008 = 20239765542626580720253440000 := by
  rw [← show ((([(2, 3), (3, 1), (7, 1), (751, 1), (29789, 1), (574363039, 1), (32860574161, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696008 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_2, prime_sixtyBF_3, prime_sixtyBF_7, prime_sixtyBF_751, prime_sixtyBF_29789, prime_sixtyBF_574363039, prime_sixtyBF_32860574161]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696009 : Nat.totient 70936013046169336450681696009 = 70559603118655893815131530000 := by
  rw [← show ((([(271, 1), (619, 1), (147451, 1), (2867867703521123791, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696009 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_271, prime_sixtyBF_619, prime_sixtyBF_147451, prime_sixtyBF_2867867703521123791]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696010 : Nat.totient 70936013046169336450681696010 = 26191758663200985766405549248 := by
  rw [← show ((([(2, 1), (5, 1), (13, 1), (545661638816687203466782277, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696010 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_2, prime_sixtyBF_5, prime_sixtyBF_13, prime_sixtyBF_545661638816687203466782277]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696011 : Nat.totient 70936013046169336450681696011 = 47290675364112890967121130672 := by
  rw [← show ((([(3, 1), (23645337682056445483560565337, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696011 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_3, prime_sixtyBF_23645337682056445483560565337]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696012 : Nat.totient 70936013046169336450681696012 = 35212841008530102266885158176 := by
  rw [← show ((([(2, 2), (139, 1), (127582757277282979227844777, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696012 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_2, prime_sixtyBF_139, prime_sixtyBF_127582757277282979227844777]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696013 : Nat.totient 70936013046169336450681696013 = 70849741985892808428030900480 := by
  rw [← show ((([(881, 1), (14767, 1), (74323, 1), (37236119, 1), (1970202887, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696013 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_881, prime_sixtyBF_14767, prime_sixtyBF_74323, prime_sixtyBF_37236119, prime_sixtyBF_1970202887]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696014 : Nat.totient 70936013046169336450681696014 = 23645209231332676835814807360 := by
  rw [← show ((([(2, 1), (3, 2), (184081, 1), (21408453961441290775583, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696014 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_2, prime_sixtyBF_3, prime_sixtyBF_184081, prime_sixtyBF_21408453961441290775583]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696015 : Nat.totient 70936013046169336450681696015 = 44219852288521144800424953120 := by
  rw [← show ((([(5, 1), (7, 1), (11, 1), (184249384535504770001770639, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696015 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_5, prime_sixtyBF_7, prime_sixtyBF_11, prime_sixtyBF_184249384535504770001770639]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696016 : Nat.totient 70936013046169336450681696016 = 35468005675808417373360227616 := by
  rw [← show ((([(2, 4), (41861207, 1), (105909531356455716343, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696016 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_2, prime_sixtyBF_41861207, prime_sixtyBF_105909531356455716343]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696017 : Nat.totient 70936013046169336450681696017 = 45765169707206023516568836080 := by
  rw [← show ((([(3, 1), (31, 1), (762752828453433725276147269, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696017 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_3, prime_sixtyBF_31, prime_sixtyBF_762752828453433725276147269]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696018 : Nat.totient 70936013046169336450681696018 = 35428868188411401323719433136 := by
  rw [← show ((([(2, 1), (907, 1), (1054853, 1), (37071277321118646079, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696018 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_2, prime_sixtyBF_907, prime_sixtyBF_1054853, prime_sixtyBF_37071277321118646079]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696019 : Nat.totient 70936013046169336450681696019 = 70936013046166358653167558744 := by
  rw [← show ((([(24015316055543, 1), (2953782198081733, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696019 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_24015316055543, prime_sixtyBF_2953782198081733]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696020 : Nat.totient 70936013046169336450681696020 = 17652649911206502675322414080 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (19, 1), (67, 1), (31849, 1), (29160255200269631371, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696020 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_2, prime_sixtyBF_3, prime_sixtyBF_5, prime_sixtyBF_19, prime_sixtyBF_67, prime_sixtyBF_31849, prime_sixtyBF_29160255200269631371]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696021 : Nat.totient 70936013046169336450681696021 = 67972459916062370377073046528 := by
  rw [← show ((([(29, 1), (193, 1), (419, 1), (30248054402724838720147, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696021 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_29, prime_sixtyBF_193, prime_sixtyBF_419, prime_sixtyBF_30248054402724838720147]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696022 : Nat.totient 70936013046169336450681696022 = 28612844705045106077274064896 := by
  rw [← show ((([(2, 1), (7, 1), (17, 1), (47593199, 1), (98067923, 1), (63858386897, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696022 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_2, prime_sixtyBF_7, prime_sixtyBF_17, prime_sixtyBF_47593199, prime_sixtyBF_98067923, prime_sixtyBF_63858386897]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696023 : Nat.totient 70936013046169336450681696023 = 43652931105334976277342582096 := by
  rw [← show ((([(3, 2), (13, 1), (606290709796319114963091419, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696023 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_3, prime_sixtyBF_13, prime_sixtyBF_606290709796319114963091419]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696024 : Nat.totient 70936013046169336450681696024 = 35468006522991379777333924992 := by
  rw [← show ((([(2, 3), (380203396019, 1), (23321731798334737, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696024 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_2, prime_sixtyBF_380203396019, prime_sixtyBF_23321731798334737]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696025 : Nat.totient 70936013046169336450681696025 = 56748807890322280557119206400 := by
  rw [← show ((([(5, 2), (23665997, 1), (382076273, 1), (313799243861, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696025 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_5, prime_sixtyBF_23665997, prime_sixtyBF_382076273, prime_sixtyBF_313799243861]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696026 : Nat.totient 70936013046169336450681696026 = 20975911042563057615207264000 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1), (43, 1), (1381, 1), (4421, 1), (4093927908341190527, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696026 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_2, prime_sixtyBF_3, prime_sixtyBF_11, prime_sixtyBF_43, prime_sixtyBF_1381, prime_sixtyBF_4421, prime_sixtyBF_4093927908341190527]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696027 : Nat.totient 70936013046169336450681696027 = 67789850264576305325729280000 := by
  rw [← show ((([(23, 1), (1367, 1), (5897, 1), (82351, 1), (2134961, 1), (2176108141, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696027 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_23, prime_sixtyBF_1367, prime_sixtyBF_5897, prime_sixtyBF_82351, prime_sixtyBF_2134961, prime_sixtyBF_2176108141]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696028 : Nat.totient 70936013046169336450681696028 = 35465973856082370978035790432 := by
  rw [← show ((([(2, 2), (17449, 1), (1016333501148623652511343, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696028 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_2, prime_sixtyBF_17449, prime_sixtyBF_1016333501148623652511343]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696029 : Nat.totient 70936013046169336450681696029 = 40534864597811049400389540576 := by
  rw [← show ((([(3, 1), (7, 1), (3377905383150920783365795049, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696029 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_3, prime_sixtyBF_7, prime_sixtyBF_3377905383150920783365795049]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696030 : Nat.totient 70936013046169336450681696030 = 28374405210719803352982370240 := by
  rw [← show ((([(2, 1), (5, 1), (3662191163, 1), (1936982803160385881, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696030 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_2, prime_sixtyBF_5, prime_sixtyBF_3662191163, prime_sixtyBF_1936982803160385881]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696031 : Nat.totient 70936013046169336450681696031 = 70772188535652754925099930880 := by
  rw [← show ((([(433, 1), (4609386585577, 1), (35541499385591, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696031 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_433, prime_sixtyBF_4609386585577, prime_sixtyBF_35541499385591]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696032 : Nat.totient 70936013046169336450681696032 = 23645337012637219805369013504 := by
  rw [← show ((([(2, 5), (3, 3), (35322167, 1), (2324372311347287389, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696032 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_2, prime_sixtyBF_3, prime_sixtyBF_35322167, prime_sixtyBF_2324372311347287389]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696033 : Nat.totient 70936013046169336450681696033 = 70871061580381039707920736000 := by
  rw [← show ((([(1093, 1), (1385507, 1), (3087650833, 1), (15170842751, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696033 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_1093, prime_sixtyBF_1385507, prime_sixtyBF_3087650833, prime_sixtyBF_15170842751]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696034 : Nat.totient 70936013046169336450681696034 = 35116838141070365554291695600 := by
  rw [← show ((([(2, 1), (101, 1), (58761453143, 1), (5976169114846219, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696034 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_2, prime_sixtyBF_101, prime_sixtyBF_58761453143, prime_sixtyBF_5976169114846219]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696035 : Nat.totient 70936013046169336450681696035 = 37827737378868622708614123648 := by
  rw [← show ((([(3, 1), (5, 1), (7877, 1), (485936502283, 1), (1235478372859, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696035 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_3, prime_sixtyBF_5, prime_sixtyBF_7877, prime_sixtyBF_485936502283, prime_sixtyBF_1235478372859]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696036 : Nat.totient 70936013046169336450681696036 = 27533111960247944183213543424 := by
  rw [← show ((([(2, 2), (7, 1), (13, 1), (53, 1), (7615039, 1), (482855730763388897, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696036 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_2, prime_sixtyBF_7, prime_sixtyBF_13, prime_sixtyBF_53, prime_sixtyBF_7615039, prime_sixtyBF_482855730763388897]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696037 : Nat.totient 70936013046169336450681696037 = 64487265518430133814964812400 := by
  rw [← show ((([(11, 1), (3381787, 1), (1906899653568562109341, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696037 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_11, prime_sixtyBF_3381787, prime_sixtyBF_1906899653568562109341]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696038 : Nat.totient 70936013046169336450681696038 = 23401571314200193468266126336 := by
  rw [← show ((([(2, 1), (3, 1), (97, 1), (121883183928126007647219409, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696038 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_2, prime_sixtyBF_3, prime_sixtyBF_97, prime_sixtyBF_121883183928126007647219409]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696039 : Nat.totient 70936013046169336450681696039 = 62538780208095302570914397184 := by
  rw [← show ((([(17, 1), (19, 1), (89, 1), (2467597072604770461289237, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696039 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_17, prime_sixtyBF_19, prime_sixtyBF_89, prime_sixtyBF_2467597072604770461289237]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696040 : Nat.totient 70936013046169336450681696040 = 28013643406090875893607346176 := by
  rw [← show ((([(2, 3), (5, 1), (127, 1), (367, 1), (463, 1), (1067547697, 1), (76978371599, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696040 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_2, prime_sixtyBF_5, prime_sixtyBF_127, prime_sixtyBF_367, prime_sixtyBF_463, prime_sixtyBF_1067547697, prime_sixtyBF_76978371599]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696041 : Nat.totient 70936013046169336450681696041 = 47290675364112890967121130688 := by
  rw [← show ((([(3, 2), (7881779227352148494520188449, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696041 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_3, prime_sixtyBF_7881779227352148494520188449]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696042 : Nat.totient 70936013046169336450681696042 = 34596561817113355447369228800 := by
  rw [← show ((([(2, 1), (41, 1), (5431, 1), (17722382539, 1), (8987750617009, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696042 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_2, prime_sixtyBF_41, prime_sixtyBF_5431, prime_sixtyBF_17722382539, prime_sixtyBF_8987750617009]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696043 : Nat.totient 70936013046169336450681696043 = 60450825212241122289345886080 := by
  rw [← show ((([(7, 2), (173, 1), (4538041, 1), (1843979874874032799, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696043 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_7, prime_sixtyBF_173, prime_sixtyBF_4538041, prime_sixtyBF_1843979874874032799]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696044 : Nat.totient 70936013046169336450681696044 = 22840367579903855392379781120 := by
  rw [← show ((([(2, 2), (3, 1), (37, 1), (199, 1), (457, 1), (109537, 1), (16038128413223611, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696044 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_2, prime_sixtyBF_3, prime_sixtyBF_37, prime_sixtyBF_199, prime_sixtyBF_457, prime_sixtyBF_109537, prime_sixtyBF_16038128413223611]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696045 : Nat.totient 70936013046169336450681696045 = 56658143844760044634887840000 := by
  rw [← show ((([(5, 1), (701, 1), (6163, 1), (109451, 1), (30003149875144493, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696045 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_5, prime_sixtyBF_701, prime_sixtyBF_6163, prime_sixtyBF_109451, prime_sixtyBF_30003149875144493]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696046 : Nat.totient 70936013046169336450681696046 = 35464738485952611524130541344 := by
  rw [← show ((([(2, 1), (10853, 1), (1144339913207, 1), (2855827233613, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696046 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_2, prime_sixtyBF_10853, prime_sixtyBF_1144339913207, prime_sixtyBF_2855827233613]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696047 : Nat.totient 70936013046169336450681696047 = 47290657336303661991708694872 := by
  rw [← show ((([(3, 1), (2623207, 1), (9013904614487703594707, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696047 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_3, prime_sixtyBF_2623207, prime_sixtyBF_9013904614487703594707]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696048 : Nat.totient 70936013046169336450681696048 = 31029203432767923511736995200 := by
  rw [← show ((([(2, 4), (11, 2), (31, 1), (179, 1), (6603082106053780114007, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696048 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_2, prime_sixtyBF_11, prime_sixtyBF_31, prime_sixtyBF_179, prime_sixtyBF_6603082106053780114007]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696049 : Nat.totient 70936013046169336450681696049 = 65479396658002464416013873264 := by
  rw [← show ((([(13, 1), (5456616388166872034667822773, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696049 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_13, prime_sixtyBF_5456616388166872034667822773]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696050 : Nat.totient 70936013046169336450681696050 = 14719202150790465089879040000 := by
  rw [← show ((([(2, 1), (3, 2), (5, 2), (7, 1), (23, 1), (29, 1), (61, 1), (2087, 1), (6011, 1), (1325083, 1), (33295711, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696050 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_2, prime_sixtyBF_3, prime_sixtyBF_5, prime_sixtyBF_7, prime_sixtyBF_23, prime_sixtyBF_29, prime_sixtyBF_61, prime_sixtyBF_2087, prime_sixtyBF_6011, prime_sixtyBF_1325083, prime_sixtyBF_33295711]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696051 : Nat.totient 70936013046169336450681696051 = 69958930927415610582386321472 := by
  rw [← show ((([(73, 1), (13063, 1), (74387675580793747110349, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696051 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_73, prime_sixtyBF_13063, prime_sixtyBF_74387675580793747110349]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696052 : Nat.totient 70936013046169336450681696052 = 35465637092426356661170917696 := by
  rw [← show ((([(2, 2), (14969, 1), (865673748763, 1), (1368547096879, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696052 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_2, prime_sixtyBF_14969, prime_sixtyBF_865673748763, prime_sixtyBF_1368547096879]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696053 : Nat.totient 70936013046169336450681696053 = 46283680091964373189783217856 := by
  rw [← show ((([(3, 1), (47, 1), (57119, 1), (124072723, 1), (70988950147309, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696053 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_3, prime_sixtyBF_47, prime_sixtyBF_57119, prime_sixtyBF_124072723, prime_sixtyBF_70988950147309]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696054 : Nat.totient 70936013046169336450681696054 = 35465428718991123297059321016 := by
  rw [← show ((([(2, 1), (13759, 1), (2577804093544928281513253, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696054 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_2, prime_sixtyBF_13759, prime_sixtyBF_2577804093544928281513253]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696055 : Nat.totient 70936013046169336450681696055 = 56748810436928605824617058496 := by
  rw [← show ((([(5, 1), (8308633674179, 1), (1707525348400409, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696055 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_5, prime_sixtyBF_8308633674179, prime_sixtyBF_1707525348400409]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696056 : Nat.totient 70936013046169336450681696056 = 22254408535861825144675381248 := by
  rw [← show ((([(2, 3), (3, 1), (17, 1), (826393, 1), (210387523943141401349, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696056 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_2, prime_sixtyBF_3, prime_sixtyBF_17, prime_sixtyBF_826393, prime_sixtyBF_210387523943141401349]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696057 : Nat.totient 70936013046169336450681696057 = 60797443066712215980199977600 := by
  rw [← show ((([(7, 1), (12553, 1), (5970301, 1), (135215033261379667, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696057 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_7, prime_sixtyBF_12553, prime_sixtyBF_5970301, prime_sixtyBF_135215033261379667]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696058 : Nat.totient 70936013046169336450681696058 = 33487542993368620679198400000 := by
  rw [← show ((([(2, 1), (19, 1), (461, 1), (821, 1), (367470361, 1), (13421985960151, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696058 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_2, prime_sixtyBF_19, prime_sixtyBF_461, prime_sixtyBF_821, prime_sixtyBF_367470361, prime_sixtyBF_13421985960151]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696059 : Nat.totient 70936013046169336450681696059 = 42953240312907523407358260480 := by
  rw [← show ((([(3, 3), (11, 1), (1123, 1), (212681918760682924377889, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696059 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_3, prime_sixtyBF_11, prime_sixtyBF_1123, prime_sixtyBF_212681918760682924377889]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696060 : Nat.totient 70936013046169336450681696060 = 28020718554304417577696183040 := by
  rw [← show ((([(2, 2), (5, 1), (83, 1), (2371, 1), (8566543, 1), (2103882756465397, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696060 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_2, prime_sixtyBF_5, prime_sixtyBF_83, prime_sixtyBF_2371, prime_sixtyBF_8566543, prime_sixtyBF_2103882756465397]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696061 : Nat.totient 70936013046169336450681696061 = 70935932513818504087838644608 := by
  rw [← show ((([(919427, 1), (20987359, 1), (3676137361692577, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696061 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_919427, prime_sixtyBF_20987359, prime_sixtyBF_3676137361692577]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696062 : Nat.totient 70936013046169336450681696062 = 21456523652805947555525975040 := by
  rw [← show ((([(2, 1), (3, 1), (13, 1), (59, 1), (12150031, 1), (837527069, 1), (1514760329, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696062 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_2, prime_sixtyBF_3, prime_sixtyBF_13, prime_sixtyBF_59, prime_sixtyBF_12150031, prime_sixtyBF_837527069, prime_sixtyBF_1514760329]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696063 : Nat.totient 70936013046169336450681696063 = 70639200953735648326591072000 := by
  rw [← show ((([(239, 1), (8155451, 1), (3069282977, 1), (11857249571, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696063 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_239, prime_sixtyBF_8155451, prime_sixtyBF_3069282977, prime_sixtyBF_11857249571]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696064 : Nat.totient 70936013046169336450681696064 = 30398175119246878196451348480 := by
  rw [← show ((([(2, 6), (7, 1), (10243, 1), (8033939, 1), (26986489, 1), (71299531, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696064 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_2, prime_sixtyBF_7, prime_sixtyBF_10243, prime_sixtyBF_8033939, prime_sixtyBF_26986489, prime_sixtyBF_71299531]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696065 : Nat.totient 70936013046169336450681696065 = 37576609400916448999482859520 := by
  rw [← show ((([(3, 1), (5, 1), (149, 1), (18593, 1), (351640271, 1), (4854462744893, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696065 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_3, prime_sixtyBF_5, prime_sixtyBF_149, prime_sixtyBF_18593, prime_sixtyBF_351640271, prime_sixtyBF_4854462744893]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696066 : Nat.totient 70936013046169336450681696066 = 35468006523084668225340848032 := by
  rw [← show ((([(2, 1), (35468006523084668225340848033, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696066 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_2, prime_sixtyBF_35468006523084668225340848033]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696067 : Nat.totient 70936013046169336450681696067 = 70936013046169336450681696066 := by
  rw [← show ((([(70936013046169336450681696067, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696067 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_70936013046169336450681696067]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696068 : Nat.totient 70936013046169336450681696068 = 23310325615709333563752237120 := by
  rw [← show ((([(2, 2), (3, 2), (71, 1), (11779, 1), (2356120533006385347557, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696068 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_2, prime_sixtyBF_3, prime_sixtyBF_71, prime_sixtyBF_11779, prime_sixtyBF_2356120533006385347557]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696069 : Nat.totient 70936013046169336450681696069 = 69286338324165398393689096680 := by
  rw [← show ((([(43, 2), (38364528418696233883548781, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696069 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_43, prime_sixtyBF_38364528418696233883548781]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696070 : Nat.totient 70936013046169336450681696070 = 25794913778009905105534003200 := by
  rw [← show ((([(2, 1), (5, 1), (11, 1), (452854081, 1), (1424019066914993077, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696070 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_2, prime_sixtyBF_5, prime_sixtyBF_11, prime_sixtyBF_452854081, prime_sixtyBF_1424019066914993077]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696071 : Nat.totient 70936013046169336450681696071 = 40533742425303741936884728320 := by
  rw [← show ((([(3, 1), (7, 1), (36587, 1), (2840681, 1), (32501111509238233, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696071 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_3, prime_sixtyBF_7, prime_sixtyBF_36587, prime_sixtyBF_2840681, prime_sixtyBF_32501111509238233]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696072 : Nat.totient 70936013046169336450681696072 = 35468006523084668225340848032 := by
  rw [← show ((([(2, 3), (8867001630771167056335212009, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696072 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_2, prime_sixtyBF_8867001630771167056335212009]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696073 : Nat.totient 70936013046169336450681696073 = 63052161739616307349757952000 := by
  rw [← show ((([(17, 2), (23, 2), (79, 1), (2278831, 1), (25537217, 1), (100925401, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696073 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_17, prime_sixtyBF_23, prime_sixtyBF_79, prime_sixtyBF_2278831, prime_sixtyBF_25537217, prime_sixtyBF_100925401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696074 : Nat.totient 70936013046169336450681696074 = 23161788459980813468693892096 := by
  rw [← show ((([(2, 1), (3, 1), (107, 1), (109, 1), (487, 1), (5234767, 1), (397629806780177, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696074 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_2, prime_sixtyBF_3, prime_sixtyBF_107, prime_sixtyBF_109, prime_sixtyBF_487, prime_sixtyBF_5234767, prime_sixtyBF_397629806780177]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696075 : Nat.totient 70936013046169336450681696075 = 52362057451376020306677811200 := by
  rw [← show ((([(5, 2), (13, 1), (2441, 1), (3398715337, 1), (26308788137183, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696075 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_5, prime_sixtyBF_13, prime_sixtyBF_2441, prime_sixtyBF_3398715337, prime_sixtyBF_26308788137183]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696076 : Nat.totient 70936013046169336450681696076 = 35465230850914156136453913600 := by
  rw [← show ((([(2, 2), (13681, 1), (193619, 1), (6694851809492770321, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696076 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_2, prime_sixtyBF_13681, prime_sixtyBF_193619, prime_sixtyBF_6694851809492770321]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696077 : Nat.totient 70936013046169336450681696077 = 44464393772416597413376293120 := by
  rw [← show ((([(3, 2), (19, 1), (137, 1), (4327, 1), (72118003, 1), (9703301150371, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696077 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_3, prime_sixtyBF_19, prime_sixtyBF_137, prime_sixtyBF_4327, prime_sixtyBF_72118003, prime_sixtyBF_9703301150371]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696078 : Nat.totient 70936013046169336450681696078 = 30396235868363172875281568640 := by
  rw [← show ((([(2, 1), (7, 1), (7307, 1), (40459, 1), (41919061, 1), (408858416389, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696078 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_2, prime_sixtyBF_7, prime_sixtyBF_7307, prime_sixtyBF_40459, prime_sixtyBF_41919061, prime_sixtyBF_408858416389]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696079 : Nat.totient 70936013046169336450681696079 = 66280590610436309920547968800 := by
  rw [← show ((([(29, 1), (31, 1), (78905465012424178476842821, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696079 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_29, prime_sixtyBF_31, prime_sixtyBF_78905465012424178476842821]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696080 : Nat.totient 70936013046169336450681696080 = 18832321421453093346056601600 := by
  rw [← show ((([(2, 4), (3, 1), (5, 1), (227, 1), (30553, 1), (25609457, 1), (1664084771201, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696080 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_2, prime_sixtyBF_3, prime_sixtyBF_5, prime_sixtyBF_227, prime_sixtyBF_30553, prime_sixtyBF_25609457, prime_sixtyBF_1664084771201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696081 : Nat.totient 70936013046169336450681696081 = 62350181194605214658794352640 := by
  rw [← show ((([(11, 1), (37, 1), (347, 1), (467, 1), (839, 1), (12457, 1), (102908343022729, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696081 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_11, prime_sixtyBF_37, prime_sixtyBF_347, prime_sixtyBF_467, prime_sixtyBF_839, prime_sixtyBF_12457, prime_sixtyBF_102908343022729]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696082 : Nat.totient 70936013046169336450681696082 = 35467933344085119847027893120 := by
  rw [← show ((([(2, 1), (580711, 1), (4098793, 1), (10357973, 1), (1438619579, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696082 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_2, prime_sixtyBF_580711, prime_sixtyBF_4098793, prime_sixtyBF_10357973, prime_sixtyBF_1438619579]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696083 : Nat.totient 70936013046169336450681696083 = 46136946688261465282746154560 := by
  rw [← show ((([(3, 1), (41, 1), (155047, 1), (3719617620598198702543, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696083 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_3, prime_sixtyBF_41, prime_sixtyBF_155047, prime_sixtyBF_3719617620598198702543]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696084 : Nat.totient 70936013046169336450681696084 = 35468005588354542692026577088 := by
  rw [← show ((([(2, 2), (37944649, 1), (467365062766619190829, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696084 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_2, prime_sixtyBF_37944649, prime_sixtyBF_467365062766619190829]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696085 : Nat.totient 70936013046169336450681696085 = 48641837517373259280467448720 := by
  rw [← show ((([(5, 1), (7, 1), (2026743229890552470019477031, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696085 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_5, prime_sixtyBF_7, prime_sixtyBF_2026743229890552470019477031]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696086 : Nat.totient 70936013046169336450681696086 = 23591213581232516544503418240 := by
  rw [← show ((([(2, 1), (3, 5), (479, 1), (4957, 1), (4243657991, 1), (14485573637, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696086 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_2, prime_sixtyBF_3, prime_sixtyBF_479, prime_sixtyBF_4957, prime_sixtyBF_4243657991, prime_sixtyBF_14485573637]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696087 : Nat.totient 70936013046169336450681696087 = 69870667539769518165703859856 := by
  rw [← show ((([(67, 2), (10589, 1), (1492320900985198295147, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696087 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_67, prime_sixtyBF_10589, prime_sixtyBF_1492320900985198295147]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696088 : Nat.totient 70936013046169336450681696088 = 32651637394356808297401802752 := by
  rw [← show ((([(2, 3), (13, 1), (379, 1), (19477, 1), (92400040548585484609, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696088 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_2, prime_sixtyBF_13, prime_sixtyBF_379, prime_sixtyBF_19477, prime_sixtyBF_92400040548585484609]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696089 : Nat.totient 70936013046169336450681696089 = 46398398470429071139788686400 := by
  rw [← show ((([(3, 1), (53, 1), (2200688914661, 1), (202726720646011, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696089 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_3, prime_sixtyBF_53, prime_sixtyBF_2200688914661, prime_sixtyBF_202726720646011]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696090 : Nat.totient 70936013046169336450681696090 = 26705322558557867840256638464 := by
  rw [← show ((([(2, 1), (5, 1), (17, 1), (417270664977466685004009977, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696090 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_2, prime_sixtyBF_5, prime_sixtyBF_17, prime_sixtyBF_417270664977466685004009977]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696091 : Nat.totient 70936013046169336450681696091 = 70460861811814563754159484640 := by
  rw [← show ((([(229, 1), (431, 1), (46327, 1), (15513859191818442967, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696091 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_229, prime_sixtyBF_431, prime_sixtyBF_46327, prime_sixtyBF_15513859191818442967]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696092 : Nat.totient 70936013046169336450681696092 = 18421528626915268892391244800 := by
  rw [← show ((([(2, 2), (3, 1), (7, 3), (11, 1), (6709, 1), (28621, 1), (927439, 1), (8797732927, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696092 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_2, prime_sixtyBF_3, prime_sixtyBF_7, prime_sixtyBF_11, prime_sixtyBF_6709, prime_sixtyBF_28621, prime_sixtyBF_927439, prime_sixtyBF_8797732927]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696093 : Nat.totient 70936013046169336450681696093 = 70394516763374150676249011260 := by
  rw [← show ((([(131, 1), (541496282795185774432684703, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696093 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_131, prime_sixtyBF_541496282795185774432684703]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696094 : Nat.totient 70936013046169336450681696094 = 35468006491997238136943179000 := by
  rw [← show ((([(2, 1), (1140911501, 1), (31087430087256757547, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696094 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_2, prime_sixtyBF_1140911501, prime_sixtyBF_31087430087256757547]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696095 : Nat.totient 70936013046169336450681696095 = 37832540291290312773696904560 := by
  rw [← show ((([(3, 2), (5, 1), (1576355845470429698904037691, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696095 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_3, prime_sixtyBF_5, prime_sixtyBF_1576355845470429698904037691]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696096 : Nat.totient 70936013046169336450681696096 = 31943164555726125366633585408 := by
  rw [← show ((([(2, 5), (19, 2), (23, 1), (163, 1), (1637925539288993603527, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696096 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_2, prime_sixtyBF_19, prime_sixtyBF_23, prime_sixtyBF_163, prime_sixtyBF_1637925539288993603527]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696097 : Nat.totient 70936013046169336450681696097 = 70936013046169336450681696096 := by
  rw [← show ((([(70936013046169336450681696097, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696097 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_70936013046169336450681696097]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696098 : Nat.totient 70936013046169336450681696098 = 23415771296475091607252256000 := by
  rw [← show ((([(2, 1), (3, 1), (103, 1), (73483155901, 1), (1562034063778961, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696098 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_2, prime_sixtyBF_3, prime_sixtyBF_103, prime_sixtyBF_73483155901, prime_sixtyBF_1562034063778961]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696099 : Nat.totient 70936013046169336450681696099 = 60799218766969360179959447616 := by
  rw [← show ((([(7, 1), (19753, 1), (513021624535653437457469, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696099 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_7, prime_sixtyBF_19753, prime_sixtyBF_513021624535653437457469]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyBF_70936013046169336450681696100 : Nat.totient 70936013046169336450681696100 = 27767944623166840732923803520 := by
  rw [← show ((([(2, 2), (5, 2), (47, 1), (10099, 1), (1494481506409299771637, 1)] : List FactorBlock).map factorBlockValue).prod) = 70936013046169336450681696100 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyBF_2, prime_sixtyBF_5, prime_sixtyBF_47, prime_sixtyBF_10099, prime_sixtyBF_1494481506409299771637]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64SixtyBF : certifiedKill 1 70936013046169336450681695999 100 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_sixtyBF_70936013046169336450681696000, phi_sixtyBF_70936013046169336450681696001, phi_sixtyBF_70936013046169336450681696002,
    phi_sixtyBF_70936013046169336450681696003, phi_sixtyBF_70936013046169336450681696004, phi_sixtyBF_70936013046169336450681696005,
    phi_sixtyBF_70936013046169336450681696006, phi_sixtyBF_70936013046169336450681696007, phi_sixtyBF_70936013046169336450681696008,
    phi_sixtyBF_70936013046169336450681696009, phi_sixtyBF_70936013046169336450681696010, phi_sixtyBF_70936013046169336450681696011,
    phi_sixtyBF_70936013046169336450681696012, phi_sixtyBF_70936013046169336450681696013, phi_sixtyBF_70936013046169336450681696014,
    phi_sixtyBF_70936013046169336450681696015, phi_sixtyBF_70936013046169336450681696016, phi_sixtyBF_70936013046169336450681696017,
    phi_sixtyBF_70936013046169336450681696018, phi_sixtyBF_70936013046169336450681696019, phi_sixtyBF_70936013046169336450681696020,
    phi_sixtyBF_70936013046169336450681696021, phi_sixtyBF_70936013046169336450681696022, phi_sixtyBF_70936013046169336450681696023,
    phi_sixtyBF_70936013046169336450681696024, phi_sixtyBF_70936013046169336450681696025, phi_sixtyBF_70936013046169336450681696026,
    phi_sixtyBF_70936013046169336450681696027, phi_sixtyBF_70936013046169336450681696028, phi_sixtyBF_70936013046169336450681696029,
    phi_sixtyBF_70936013046169336450681696030, phi_sixtyBF_70936013046169336450681696031, phi_sixtyBF_70936013046169336450681696032,
    phi_sixtyBF_70936013046169336450681696033, phi_sixtyBF_70936013046169336450681696034, phi_sixtyBF_70936013046169336450681696035,
    phi_sixtyBF_70936013046169336450681696036, phi_sixtyBF_70936013046169336450681696037, phi_sixtyBF_70936013046169336450681696038,
    phi_sixtyBF_70936013046169336450681696039, phi_sixtyBF_70936013046169336450681696040, phi_sixtyBF_70936013046169336450681696041,
    phi_sixtyBF_70936013046169336450681696042, phi_sixtyBF_70936013046169336450681696043, phi_sixtyBF_70936013046169336450681696044,
    phi_sixtyBF_70936013046169336450681696045, phi_sixtyBF_70936013046169336450681696046, phi_sixtyBF_70936013046169336450681696047,
    phi_sixtyBF_70936013046169336450681696048, phi_sixtyBF_70936013046169336450681696049, phi_sixtyBF_70936013046169336450681696050,
    phi_sixtyBF_70936013046169336450681696051, phi_sixtyBF_70936013046169336450681696052, phi_sixtyBF_70936013046169336450681696053,
    phi_sixtyBF_70936013046169336450681696054, phi_sixtyBF_70936013046169336450681696055, phi_sixtyBF_70936013046169336450681696056,
    phi_sixtyBF_70936013046169336450681696057, phi_sixtyBF_70936013046169336450681696058, phi_sixtyBF_70936013046169336450681696059,
    phi_sixtyBF_70936013046169336450681696060, phi_sixtyBF_70936013046169336450681696061, phi_sixtyBF_70936013046169336450681696062,
    phi_sixtyBF_70936013046169336450681696063, phi_sixtyBF_70936013046169336450681696064, phi_sixtyBF_70936013046169336450681696065,
    phi_sixtyBF_70936013046169336450681696066, phi_sixtyBF_70936013046169336450681696067, phi_sixtyBF_70936013046169336450681696068,
    phi_sixtyBF_70936013046169336450681696069, phi_sixtyBF_70936013046169336450681696070, phi_sixtyBF_70936013046169336450681696071,
    phi_sixtyBF_70936013046169336450681696072, phi_sixtyBF_70936013046169336450681696073, phi_sixtyBF_70936013046169336450681696074,
    phi_sixtyBF_70936013046169336450681696075, phi_sixtyBF_70936013046169336450681696076, phi_sixtyBF_70936013046169336450681696077,
    phi_sixtyBF_70936013046169336450681696078, phi_sixtyBF_70936013046169336450681696079, phi_sixtyBF_70936013046169336450681696080,
    phi_sixtyBF_70936013046169336450681696081, phi_sixtyBF_70936013046169336450681696082, phi_sixtyBF_70936013046169336450681696083,
    phi_sixtyBF_70936013046169336450681696084, phi_sixtyBF_70936013046169336450681696085, phi_sixtyBF_70936013046169336450681696086,
    phi_sixtyBF_70936013046169336450681696087, phi_sixtyBF_70936013046169336450681696088, phi_sixtyBF_70936013046169336450681696089,
    phi_sixtyBF_70936013046169336450681696090, phi_sixtyBF_70936013046169336450681696091, phi_sixtyBF_70936013046169336450681696092,
    phi_sixtyBF_70936013046169336450681696093, phi_sixtyBF_70936013046169336450681696094, phi_sixtyBF_70936013046169336450681696095,
    phi_sixtyBF_70936013046169336450681696096, phi_sixtyBF_70936013046169336450681696097, phi_sixtyBF_70936013046169336450681696098,
    phi_sixtyBF_70936013046169336450681696099, phi_sixtyBF_70936013046169336450681696100
  ]

end TotientTailPeriodKiller
end Erdos249257
