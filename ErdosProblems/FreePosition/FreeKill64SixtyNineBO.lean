import Erdos249257.DiagonalPincerCertificatesT64

-- Explicit full-window certificate for the earliest successful 69P sweep coordinate.
namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def sixtyNineBOFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem sixtyNineBOFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) :
    sixtyNineBOFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [sixtyNineBOFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [sixtyNineBOFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then sixtyNineBOFastPow a n * sixtyNineBOFastPow a n * a
        else sixtyNineBOFastPow a n * sixtyNineBOFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_sixtyNineBO_2 : Nat.Prime 2 := by norm_num

private theorem prime_sixtyNineBO_3 : Nat.Prime 3 := by norm_num

private theorem prime_sixtyNineBO_5 : Nat.Prime 5 := by norm_num

private theorem prime_sixtyNineBO_7 : Nat.Prime 7 := by norm_num

private theorem prime_sixtyNineBO_11 : Nat.Prime 11 := by norm_num

private theorem prime_sixtyNineBO_13 : Nat.Prime 13 := by norm_num

private theorem prime_sixtyNineBO_17 : Nat.Prime 17 := by norm_num

private theorem prime_sixtyNineBO_19 : Nat.Prime 19 := by norm_num

private theorem prime_sixtyNineBO_23 : Nat.Prime 23 := by norm_num

private theorem prime_sixtyNineBO_29 : Nat.Prime 29 := by norm_num

private theorem prime_sixtyNineBO_31 : Nat.Prime 31 := by norm_num

private theorem prime_sixtyNineBO_37 : Nat.Prime 37 := by norm_num

private theorem prime_sixtyNineBO_41 : Nat.Prime 41 := by norm_num

private theorem prime_sixtyNineBO_43 : Nat.Prime 43 := by norm_num

private theorem prime_sixtyNineBO_47 : Nat.Prime 47 := by norm_num

private theorem prime_sixtyNineBO_53 : Nat.Prime 53 := by norm_num

private theorem prime_sixtyNineBO_59 : Nat.Prime 59 := by norm_num

private theorem prime_sixtyNineBO_61 : Nat.Prime 61 := by norm_num

private theorem prime_sixtyNineBO_67 : Nat.Prime 67 := by norm_num

private theorem prime_sixtyNineBO_71 : Nat.Prime 71 := by norm_num

private theorem prime_sixtyNineBO_73 : Nat.Prime 73 := by norm_num

private theorem prime_sixtyNineBO_79 : Nat.Prime 79 := by norm_num

private theorem prime_sixtyNineBO_83 : Nat.Prime 83 := by norm_num

private theorem prime_sixtyNineBO_89 : Nat.Prime 89 := by norm_num

private theorem prime_sixtyNineBO_97 : Nat.Prime 97 := by norm_num

private theorem prime_sixtyNineBO_101 : Nat.Prime 101 := by norm_num

private theorem prime_sixtyNineBO_103 : Nat.Prime 103 := by norm_num

private theorem prime_sixtyNineBO_107 : Nat.Prime 107 := by norm_num

private theorem prime_sixtyNineBO_109 : Nat.Prime 109 := by norm_num

private theorem prime_sixtyNineBO_113 : Nat.Prime 113 := by norm_num

private theorem prime_sixtyNineBO_127 : Nat.Prime 127 := by norm_num

private theorem prime_sixtyNineBO_131 : Nat.Prime 131 := by norm_num

private theorem prime_sixtyNineBO_137 : Nat.Prime 137 := by norm_num

private theorem prime_sixtyNineBO_139 : Nat.Prime 139 := by norm_num

private theorem prime_sixtyNineBO_149 : Nat.Prime 149 := by norm_num

private theorem prime_sixtyNineBO_151 : Nat.Prime 151 := by norm_num

private theorem prime_sixtyNineBO_157 : Nat.Prime 157 := by norm_num

private theorem prime_sixtyNineBO_163 : Nat.Prime 163 := by norm_num

private theorem prime_sixtyNineBO_167 : Nat.Prime 167 := by norm_num

private theorem prime_sixtyNineBO_173 : Nat.Prime 173 := by norm_num

private theorem prime_sixtyNineBO_179 : Nat.Prime 179 := by norm_num

private theorem prime_sixtyNineBO_181 : Nat.Prime 181 := by norm_num

private theorem prime_sixtyNineBO_191 : Nat.Prime 191 := by norm_num

private theorem prime_sixtyNineBO_193 : Nat.Prime 193 := by norm_num

private theorem prime_sixtyNineBO_197 : Nat.Prime 197 := by norm_num

private theorem prime_sixtyNineBO_199 : Nat.Prime 199 := by norm_num

private theorem prime_sixtyNineBO_211 : Nat.Prime 211 := by norm_num

private theorem prime_sixtyNineBO_223 : Nat.Prime 223 := by norm_num

private theorem prime_sixtyNineBO_227 : Nat.Prime 227 := by norm_num

private theorem prime_sixtyNineBO_229 : Nat.Prime 229 := by norm_num

private theorem prime_sixtyNineBO_233 : Nat.Prime 233 := by norm_num

private theorem prime_sixtyNineBO_251 : Nat.Prime 251 := by norm_num

private theorem prime_sixtyNineBO_257 : Nat.Prime 257 := by norm_num

private theorem prime_sixtyNineBO_263 : Nat.Prime 263 := by norm_num

private theorem prime_sixtyNineBO_269 : Nat.Prime 269 := by norm_num

private theorem prime_sixtyNineBO_271 : Nat.Prime 271 := by norm_num

private theorem prime_sixtyNineBO_277 : Nat.Prime 277 := by norm_num

private theorem prime_sixtyNineBO_281 : Nat.Prime 281 := by norm_num

private theorem prime_sixtyNineBO_283 : Nat.Prime 283 := by norm_num

private theorem prime_sixtyNineBO_293 : Nat.Prime 293 := by norm_num

private theorem prime_sixtyNineBO_307 : Nat.Prime 307 := by norm_num

private theorem prime_sixtyNineBO_311 : Nat.Prime 311 := by norm_num

private theorem prime_sixtyNineBO_317 : Nat.Prime 317 := by norm_num

private theorem prime_sixtyNineBO_331 : Nat.Prime 331 := by norm_num

private theorem prime_sixtyNineBO_337 : Nat.Prime 337 := by norm_num

private theorem prime_sixtyNineBO_349 : Nat.Prime 349 := by norm_num

private theorem prime_sixtyNineBO_353 : Nat.Prime 353 := by norm_num

private theorem prime_sixtyNineBO_359 : Nat.Prime 359 := by norm_num

private theorem prime_sixtyNineBO_367 : Nat.Prime 367 := by norm_num

private theorem prime_sixtyNineBO_379 : Nat.Prime 379 := by norm_num

private theorem prime_sixtyNineBO_383 : Nat.Prime 383 := by norm_num

private theorem prime_sixtyNineBO_389 : Nat.Prime 389 := by norm_num

private theorem prime_sixtyNineBO_397 : Nat.Prime 397 := by norm_num

private theorem prime_sixtyNineBO_401 : Nat.Prime 401 := by norm_num

private theorem prime_sixtyNineBO_409 : Nat.Prime 409 := by norm_num

private theorem prime_sixtyNineBO_421 : Nat.Prime 421 := by norm_num

private theorem prime_sixtyNineBO_431 : Nat.Prime 431 := by norm_num

private theorem prime_sixtyNineBO_433 : Nat.Prime 433 := by norm_num

private theorem prime_sixtyNineBO_443 : Nat.Prime 443 := by norm_num

private theorem prime_sixtyNineBO_449 : Nat.Prime 449 := by norm_num

private theorem prime_sixtyNineBO_461 : Nat.Prime 461 := by norm_num

private theorem prime_sixtyNineBO_463 : Nat.Prime 463 := by norm_num

private theorem prime_sixtyNineBO_467 : Nat.Prime 467 := by norm_num

private theorem prime_sixtyNineBO_479 : Nat.Prime 479 := by norm_num

private theorem prime_sixtyNineBO_487 : Nat.Prime 487 := by norm_num

private theorem prime_sixtyNineBO_491 : Nat.Prime 491 := by norm_num

private theorem prime_sixtyNineBO_499 : Nat.Prime 499 := by norm_num

private theorem prime_sixtyNineBO_521 : Nat.Prime 521 := by norm_num

private theorem prime_sixtyNineBO_523 : Nat.Prime 523 := by norm_num

private theorem prime_sixtyNineBO_541 : Nat.Prime 541 := by norm_num

private theorem prime_sixtyNineBO_547 : Nat.Prime 547 := by norm_num

private theorem prime_sixtyNineBO_571 : Nat.Prime 571 := by norm_num

private theorem prime_sixtyNineBO_587 : Nat.Prime 587 := by norm_num

private theorem prime_sixtyNineBO_607 : Nat.Prime 607 := by norm_num

private theorem prime_sixtyNineBO_617 : Nat.Prime 617 := by norm_num

private theorem prime_sixtyNineBO_619 : Nat.Prime 619 := by norm_num

private theorem prime_sixtyNineBO_631 : Nat.Prime 631 := by norm_num

private theorem prime_sixtyNineBO_643 : Nat.Prime 643 := by norm_num

private theorem prime_sixtyNineBO_647 : Nat.Prime 647 := by norm_num

private theorem prime_sixtyNineBO_653 : Nat.Prime 653 := by norm_num

private theorem prime_sixtyNineBO_661 : Nat.Prime 661 := by norm_num

private theorem prime_sixtyNineBO_677 : Nat.Prime 677 := by norm_num

private theorem prime_sixtyNineBO_691 : Nat.Prime 691 := by norm_num

private theorem prime_sixtyNineBO_709 : Nat.Prime 709 := by norm_num

private theorem prime_sixtyNineBO_761 : Nat.Prime 761 := by norm_num

private theorem prime_sixtyNineBO_797 : Nat.Prime 797 := by norm_num

private theorem prime_sixtyNineBO_809 : Nat.Prime 809 := by norm_num

private theorem prime_sixtyNineBO_811 : Nat.Prime 811 := by norm_num

private theorem prime_sixtyNineBO_821 : Nat.Prime 821 := by norm_num

private theorem prime_sixtyNineBO_823 : Nat.Prime 823 := by norm_num

private theorem prime_sixtyNineBO_883 : Nat.Prime 883 := by norm_num

private theorem prime_sixtyNineBO_907 : Nat.Prime 907 := by norm_num

private theorem prime_sixtyNineBO_911 : Nat.Prime 911 := by norm_num

private theorem prime_sixtyNineBO_919 : Nat.Prime 919 := by norm_num

private theorem prime_sixtyNineBO_929 : Nat.Prime 929 := by norm_num

private theorem prime_sixtyNineBO_941 : Nat.Prime 941 := by norm_num

private theorem prime_sixtyNineBO_967 : Nat.Prime 967 := by norm_num

private theorem prime_sixtyNineBO_1013 : Nat.Prime 1013 := by norm_num

private theorem prime_sixtyNineBO_1019 : Nat.Prime 1019 := by norm_num

private theorem prime_sixtyNineBO_1021 : Nat.Prime 1021 := by norm_num

private theorem prime_sixtyNineBO_1049 : Nat.Prime 1049 := by norm_num

private theorem prime_sixtyNineBO_1069 : Nat.Prime 1069 := by norm_num

private theorem prime_sixtyNineBO_1117 : Nat.Prime 1117 := by norm_num

private theorem prime_sixtyNineBO_1123 : Nat.Prime 1123 := by norm_num

private theorem prime_sixtyNineBO_1151 : Nat.Prime 1151 := by norm_num

private theorem prime_sixtyNineBO_1163 : Nat.Prime 1163 := by norm_num

private theorem prime_sixtyNineBO_1181 : Nat.Prime 1181 := by norm_num

private theorem prime_sixtyNineBO_1213 : Nat.Prime 1213 := by norm_num

private theorem prime_sixtyNineBO_1223 : Nat.Prime 1223 := by norm_num

private theorem prime_sixtyNineBO_1231 : Nat.Prime 1231 := by norm_num

private theorem prime_sixtyNineBO_1291 : Nat.Prime 1291 := by norm_num

private theorem prime_sixtyNineBO_1301 : Nat.Prime 1301 := by norm_num

private theorem prime_sixtyNineBO_1381 : Nat.Prime 1381 := by norm_num

private theorem prime_sixtyNineBO_1451 : Nat.Prime 1451 := by norm_num

private theorem prime_sixtyNineBO_1481 : Nat.Prime 1481 := by norm_num

private theorem prime_sixtyNineBO_1483 : Nat.Prime 1483 := by norm_num

private theorem prime_sixtyNineBO_1531 : Nat.Prime 1531 := by norm_num

private theorem prime_sixtyNineBO_1597 : Nat.Prime 1597 := by norm_num

private theorem prime_sixtyNineBO_1607 : Nat.Prime 1607 := by norm_num

private theorem prime_sixtyNineBO_1667 : Nat.Prime 1667 := by norm_num

private theorem prime_sixtyNineBO_1669 : Nat.Prime 1669 := by norm_num

private theorem prime_sixtyNineBO_1693 : Nat.Prime 1693 := by norm_num

private theorem prime_sixtyNineBO_1699 : Nat.Prime 1699 := by norm_num

private theorem prime_sixtyNineBO_1741 : Nat.Prime 1741 := by norm_num

private theorem prime_sixtyNineBO_1753 : Nat.Prime 1753 := by norm_num

private theorem prime_sixtyNineBO_1759 : Nat.Prime 1759 := by norm_num

private theorem prime_sixtyNineBO_1783 : Nat.Prime 1783 := by norm_num

private theorem prime_sixtyNineBO_1831 : Nat.Prime 1831 := by norm_num

private theorem prime_sixtyNineBO_1847 : Nat.Prime 1847 := by norm_num

private theorem prime_sixtyNineBO_1871 : Nat.Prime 1871 := by norm_num

private theorem prime_sixtyNineBO_1877 : Nat.Prime 1877 := by norm_num

private theorem prime_sixtyNineBO_1907 : Nat.Prime 1907 := by norm_num

private theorem prime_sixtyNineBO_1913 : Nat.Prime 1913 := by norm_num

private theorem prime_sixtyNineBO_1933 : Nat.Prime 1933 := by norm_num

private theorem prime_sixtyNineBO_1973 : Nat.Prime 1973 := by norm_num

private theorem prime_sixtyNineBO_1999 : Nat.Prime 1999 := by norm_num

private theorem prime_sixtyNineBO_2027 : Nat.Prime 2027 := by norm_num

private theorem prime_sixtyNineBO_2069 : Nat.Prime 2069 := by norm_num

private theorem prime_sixtyNineBO_2081 : Nat.Prime 2081 := by norm_num

private theorem prime_sixtyNineBO_2087 : Nat.Prime 2087 := by norm_num

private theorem prime_sixtyNineBO_2141 : Nat.Prime 2141 := by norm_num

private theorem prime_sixtyNineBO_2251 : Nat.Prime 2251 := by norm_num

private theorem prime_sixtyNineBO_2267 : Nat.Prime 2267 := by norm_num

private theorem prime_sixtyNineBO_2293 : Nat.Prime 2293 := by norm_num

private theorem prime_sixtyNineBO_2297 : Nat.Prime 2297 := by norm_num

private theorem prime_sixtyNineBO_2371 : Nat.Prime 2371 := by norm_num

private theorem prime_sixtyNineBO_2381 : Nat.Prime 2381 := by norm_num

private theorem prime_sixtyNineBO_2399 : Nat.Prime 2399 := by norm_num

private theorem prime_sixtyNineBO_2549 : Nat.Prime 2549 := by norm_num

private theorem prime_sixtyNineBO_2609 : Nat.Prime 2609 := by norm_num

private theorem prime_sixtyNineBO_2677 : Nat.Prime 2677 := by norm_num

private theorem prime_sixtyNineBO_2801 : Nat.Prime 2801 := by norm_num

private theorem prime_sixtyNineBO_2819 : Nat.Prime 2819 := by norm_num

private theorem prime_sixtyNineBO_2851 : Nat.Prime 2851 := by norm_num

private theorem prime_sixtyNineBO_2909 : Nat.Prime 2909 := by norm_num

private theorem prime_sixtyNineBO_2939 : Nat.Prime 2939 := by norm_num

private theorem prime_sixtyNineBO_2957 : Nat.Prime 2957 := by norm_num

private theorem prime_sixtyNineBO_2963 : Nat.Prime 2963 := by norm_num

private theorem prime_sixtyNineBO_3037 : Nat.Prime 3037 := by norm_num

private theorem prime_sixtyNineBO_3089 : Nat.Prime 3089 := by norm_num

private theorem prime_sixtyNineBO_3119 : Nat.Prime 3119 := by norm_num

private theorem prime_sixtyNineBO_3253 : Nat.Prime 3253 := by norm_num

private theorem prime_sixtyNineBO_3391 : Nat.Prime 3391 := by norm_num

private theorem prime_sixtyNineBO_3407 : Nat.Prime 3407 := by norm_num

private theorem prime_sixtyNineBO_3499 : Nat.Prime 3499 := by norm_num

private theorem prime_sixtyNineBO_3607 : Nat.Prime 3607 := by norm_num

private theorem prime_sixtyNineBO_3623 : Nat.Prime 3623 := by norm_num

private theorem prime_sixtyNineBO_3697 : Nat.Prime 3697 := by norm_num

private theorem prime_sixtyNineBO_3701 : Nat.Prime 3701 := by norm_num

private theorem prime_sixtyNineBO_3719 : Nat.Prime 3719 := by norm_num

private theorem prime_sixtyNineBO_3797 : Nat.Prime 3797 := by norm_num

private theorem prime_sixtyNineBO_3821 : Nat.Prime 3821 := by norm_num

private theorem prime_sixtyNineBO_3847 : Nat.Prime 3847 := by norm_num

private theorem prime_sixtyNineBO_3889 : Nat.Prime 3889 := by norm_num

private theorem prime_sixtyNineBO_3911 : Nat.Prime 3911 := by norm_num

private theorem prime_sixtyNineBO_4007 : Nat.Prime 4007 := by norm_num

private theorem prime_sixtyNineBO_4111 : Nat.Prime 4111 := by norm_num

private theorem prime_sixtyNineBO_4139 : Nat.Prime 4139 := by norm_num

private theorem prime_sixtyNineBO_4157 : Nat.Prime 4157 := by norm_num

private theorem prime_sixtyNineBO_4283 : Nat.Prime 4283 := by norm_num

private theorem prime_sixtyNineBO_4289 : Nat.Prime 4289 := by norm_num

private theorem prime_sixtyNineBO_4451 : Nat.Prime 4451 := by norm_num

private theorem prime_sixtyNineBO_4567 : Nat.Prime 4567 := by norm_num

private theorem prime_sixtyNineBO_4583 : Nat.Prime 4583 := by norm_num

private theorem prime_sixtyNineBO_4649 : Nat.Prime 4649 := by norm_num

private theorem prime_sixtyNineBO_4657 : Nat.Prime 4657 := by norm_num

private theorem prime_sixtyNineBO_4721 : Nat.Prime 4721 := by norm_num

private theorem prime_sixtyNineBO_4937 : Nat.Prime 4937 := by norm_num

private theorem prime_sixtyNineBO_5009 : Nat.Prime 5009 := by norm_num

private theorem prime_sixtyNineBO_5113 : Nat.Prime 5113 := by norm_num

private theorem prime_sixtyNineBO_5209 : Nat.Prime 5209 := by norm_num

private theorem prime_sixtyNineBO_5347 : Nat.Prime 5347 := by norm_num

private theorem prime_sixtyNineBO_5531 : Nat.Prime 5531 := by norm_num

private theorem prime_sixtyNineBO_5639 : Nat.Prime 5639 := by norm_num

private theorem prime_sixtyNineBO_5849 : Nat.Prime 5849 := by norm_num

private theorem prime_sixtyNineBO_6043 : Nat.Prime 6043 := by norm_num

private theorem prime_sixtyNineBO_6073 : Nat.Prime 6073 := by norm_num

private theorem prime_sixtyNineBO_6079 : Nat.Prime 6079 := by norm_num

private theorem prime_sixtyNineBO_6143 : Nat.Prime 6143 := by norm_num

private theorem prime_sixtyNineBO_6229 : Nat.Prime 6229 := by norm_num

private theorem prime_sixtyNineBO_6547 : Nat.Prime 6547 := by norm_num

private theorem prime_sixtyNineBO_6551 : Nat.Prime 6551 := by norm_num

private theorem prime_sixtyNineBO_6673 : Nat.Prime 6673 := by norm_num

private theorem prime_sixtyNineBO_6763 : Nat.Prime 6763 := by norm_num

private theorem prime_sixtyNineBO_6907 : Nat.Prime 6907 := by norm_num

private theorem prime_sixtyNineBO_6977 : Nat.Prime 6977 := by norm_num

private theorem prime_sixtyNineBO_7027 : Nat.Prime 7027 := by norm_num

private theorem prime_sixtyNineBO_7039 : Nat.Prime 7039 := by norm_num

private theorem prime_sixtyNineBO_7057 : Nat.Prime 7057 := by norm_num

private theorem prime_sixtyNineBO_7069 : Nat.Prime 7069 := by norm_num

private theorem prime_sixtyNineBO_7349 : Nat.Prime 7349 := by norm_num

private theorem prime_sixtyNineBO_7481 : Nat.Prime 7481 := by norm_num

private theorem prime_sixtyNineBO_7507 : Nat.Prime 7507 := by norm_num

private theorem prime_sixtyNineBO_7517 : Nat.Prime 7517 := by norm_num

private theorem prime_sixtyNineBO_7589 : Nat.Prime 7589 := by norm_num

private theorem prime_sixtyNineBO_7607 : Nat.Prime 7607 := by norm_num

private theorem prime_sixtyNineBO_7649 : Nat.Prime 7649 := by norm_num

private theorem prime_sixtyNineBO_7933 : Nat.Prime 7933 := by norm_num

private theorem prime_sixtyNineBO_8039 : Nat.Prime 8039 := by norm_num

private theorem prime_sixtyNineBO_8291 : Nat.Prime 8291 := by norm_num

private theorem prime_sixtyNineBO_8837 : Nat.Prime 8837 := by norm_num

private theorem prime_sixtyNineBO_9001 : Nat.Prime 9001 := by norm_num

private theorem prime_sixtyNineBO_9521 : Nat.Prime 9521 := by norm_num

private theorem prime_sixtyNineBO_9539 : Nat.Prime 9539 := by norm_num

private theorem prime_sixtyNineBO_9901 : Nat.Prime 9901 := by norm_num

private theorem prime_sixtyNineBO_10847 : Nat.Prime 10847 := by norm_num

private theorem prime_sixtyNineBO_11527 : Nat.Prime 11527 := by norm_num

private theorem prime_sixtyNineBO_12289 : Nat.Prime 12289 := by norm_num

private theorem prime_sixtyNineBO_12973 : Nat.Prime 12973 := by norm_num

private theorem prime_sixtyNineBO_13217 : Nat.Prime 13217 := by norm_num

private theorem prime_sixtyNineBO_13487 : Nat.Prime 13487 := by norm_num

private theorem prime_sixtyNineBO_13691 : Nat.Prime 13691 := by norm_num

private theorem prime_sixtyNineBO_13751 : Nat.Prime 13751 := by norm_num

private theorem prime_sixtyNineBO_14011 : Nat.Prime 14011 := by norm_num

private theorem prime_sixtyNineBO_14083 : Nat.Prime 14083 := by norm_num

private theorem prime_sixtyNineBO_14249 : Nat.Prime 14249 := by norm_num

private theorem prime_sixtyNineBO_14387 : Nat.Prime 14387 := by norm_num

private theorem prime_sixtyNineBO_14407 : Nat.Prime 14407 := by norm_num

private theorem prime_sixtyNineBO_15329 : Nat.Prime 15329 := by norm_num

private theorem prime_sixtyNineBO_16223 : Nat.Prime 16223 := by norm_num

private theorem prime_sixtyNineBO_16433 : Nat.Prime 16433 := by norm_num

private theorem prime_sixtyNineBO_18521 : Nat.Prime 18521 := by norm_num

private theorem prime_sixtyNineBO_18917 : Nat.Prime 18917 := by norm_num

private theorem prime_sixtyNineBO_19751 : Nat.Prime 19751 := by norm_num

private theorem prime_sixtyNineBO_20399 : Nat.Prime 20399 := by norm_num

private theorem prime_sixtyNineBO_21937 : Nat.Prime 21937 := by norm_num

private theorem prime_sixtyNineBO_22543 : Nat.Prime 22543 := by norm_num

private theorem prime_sixtyNineBO_22679 : Nat.Prime 22679 := by norm_num

private theorem prime_sixtyNineBO_23209 : Nat.Prime 23209 := by norm_num

private theorem prime_sixtyNineBO_23929 : Nat.Prime 23929 := by norm_num

private theorem prime_sixtyNineBO_24781 : Nat.Prime 24781 := by norm_num

private theorem prime_sixtyNineBO_25747 : Nat.Prime 25747 := by norm_num

private theorem prime_sixtyNineBO_26267 : Nat.Prime 26267 := by norm_num

private theorem prime_sixtyNineBO_26687 : Nat.Prime 26687 := by norm_num

private theorem prime_sixtyNineBO_29311 : Nat.Prime 29311 := by norm_num

private theorem prime_sixtyNineBO_29429 : Nat.Prime 29429 := by norm_num

private theorem prime_sixtyNineBO_29611 : Nat.Prime 29611 := by norm_num

private theorem prime_sixtyNineBO_29741 : Nat.Prime 29741 := by norm_num

private theorem prime_sixtyNineBO_31481 : Nat.Prime 31481 := by norm_num

private theorem prime_sixtyNineBO_35897 : Nat.Prime 35897 := by norm_num

private theorem prime_sixtyNineBO_38561 : Nat.Prime 38561 := by norm_num

private theorem prime_sixtyNineBO_38711 : Nat.Prime 38711 := by norm_num

private theorem prime_sixtyNineBO_41131 : Nat.Prime 41131 := by norm_num

private theorem prime_sixtyNineBO_42701 : Nat.Prime 42701 := by norm_num

private theorem prime_sixtyNineBO_44963 : Nat.Prime 44963 := by norm_num

private theorem prime_sixtyNineBO_45763 : Nat.Prime 45763 := by norm_num

private theorem prime_sixtyNineBO_48049 : Nat.Prime 48049 := by norm_num

private theorem prime_sixtyNineBO_48311 : Nat.Prime 48311 := by norm_num

private theorem prime_sixtyNineBO_49211 : Nat.Prime 49211 := by norm_num

private theorem prime_sixtyNineBO_49391 : Nat.Prime 49391 := by norm_num

private theorem prime_sixtyNineBO_50527 : Nat.Prime 50527 := by norm_num

private theorem prime_sixtyNineBO_51169 : Nat.Prime 51169 := by norm_num

private theorem prime_sixtyNineBO_51419 : Nat.Prime 51419 := by norm_num

private theorem prime_sixtyNineBO_53551 : Nat.Prime 53551 := by norm_num

private theorem prime_sixtyNineBO_55639 : Nat.Prime 55639 := by norm_num

private theorem prime_sixtyNineBO_59699 : Nat.Prime 59699 := by norm_num

private theorem prime_sixtyNineBO_60757 : Nat.Prime 60757 := by norm_num

private theorem prime_sixtyNineBO_63803 : Nat.Prime 63803 := by norm_num

private theorem prime_sixtyNineBO_66809 : Nat.Prime 66809 := by norm_num

private theorem prime_sixtyNineBO_67121 : Nat.Prime 67121 := by norm_num

private theorem prime_sixtyNineBO_67763 : Nat.Prime 67763 := by norm_num

private theorem prime_sixtyNineBO_69263 : Nat.Prime 69263 := by norm_num

private theorem prime_sixtyNineBO_70321 : Nat.Prime 70321 := by norm_num

private theorem prime_sixtyNineBO_70639 : Nat.Prime 70639 := by norm_num

private theorem prime_sixtyNineBO_73849 : Nat.Prime 73849 := by norm_num

private theorem prime_sixtyNineBO_78607 : Nat.Prime 78607 := by norm_num

private theorem prime_sixtyNineBO_87613 : Nat.Prime 87613 := by norm_num

private theorem prime_sixtyNineBO_90199 : Nat.Prime 90199 := by norm_num

private theorem prime_sixtyNineBO_90631 : Nat.Prime 90631 := by norm_num

private theorem prime_sixtyNineBO_94727 : Nat.Prime 94727 := by norm_num

private theorem prime_sixtyNineBO_95191 : Nat.Prime 95191 := by norm_num

private theorem prime_sixtyNineBO_96749 : Nat.Prime 96749 := by norm_num

private theorem prime_sixtyNineBO_97429 : Nat.Prime 97429 := by norm_num

private theorem prime_sixtyNineBO_102533 : Nat.Prime 102533 := by norm_num

private theorem prime_sixtyNineBO_104417 : Nat.Prime 104417 := by norm_num

private theorem prime_sixtyNineBO_105503 : Nat.Prime 105503 := by norm_num

private theorem prime_sixtyNineBO_113143 : Nat.Prime 113143 := by norm_num

private theorem prime_sixtyNineBO_116099 : Nat.Prime 116099 := by norm_num

private theorem prime_sixtyNineBO_120067 : Nat.Prime 120067 := by norm_num

private theorem prime_sixtyNineBO_126323 : Nat.Prime 126323 := by norm_num

private theorem prime_sixtyNineBO_140407 : Nat.Prime 140407 := by norm_num

private theorem prime_sixtyNineBO_141107 : Nat.Prime 141107 := by norm_num

private theorem prime_sixtyNineBO_141539 : Nat.Prime 141539 := by norm_num

private theorem prime_sixtyNineBO_142391 : Nat.Prime 142391 := by norm_num

private theorem prime_sixtyNineBO_144583 : Nat.Prime 144583 := by norm_num

private theorem prime_sixtyNineBO_150779 : Nat.Prime 150779 := by norm_num

private theorem prime_sixtyNineBO_150893 : Nat.Prime 150893 := by norm_num

private theorem prime_sixtyNineBO_154279 : Nat.Prime 154279 := by norm_num

private theorem prime_sixtyNineBO_156823 : Nat.Prime 156823 := by norm_num

private theorem prime_sixtyNineBO_157867 : Nat.Prime 157867 := by norm_num

private theorem prime_sixtyNineBO_176467 : Nat.Prime 176467 := by norm_num

private theorem prime_sixtyNineBO_179947 : Nat.Prime 179947 := by norm_num

private theorem prime_sixtyNineBO_182711 : Nat.Prime 182711 := by norm_num

private theorem prime_sixtyNineBO_191831 : Nat.Prime 191831 := by norm_num

private theorem prime_sixtyNineBO_206237 : Nat.Prime 206237 := by norm_num

private theorem prime_sixtyNineBO_220681 : Nat.Prime 220681 := by norm_num

private theorem prime_sixtyNineBO_222011 : Nat.Prime 222011 := by norm_num

private theorem prime_sixtyNineBO_222643 : Nat.Prime 222643 := by norm_num

private theorem prime_sixtyNineBO_229267 : Nat.Prime 229267 := by norm_num

private theorem prime_sixtyNineBO_247739 : Nat.Prime 247739 := by norm_num

private theorem prime_sixtyNineBO_248099 : Nat.Prime 248099 := by norm_num

private theorem prime_sixtyNineBO_249763 : Nat.Prime 249763 := by norm_num

private theorem prime_sixtyNineBO_259309 : Nat.Prime 259309 := by norm_num

private theorem prime_sixtyNineBO_269923 : Nat.Prime 269923 := by norm_num

private theorem prime_sixtyNineBO_293453 : Nat.Prime 293453 := by norm_num

private theorem prime_sixtyNineBO_299857 : Nat.Prime 299857 := by norm_num

private theorem prime_sixtyNineBO_300893 : Nat.Prime 300893 := by norm_num

private theorem prime_sixtyNineBO_356869 : Nat.Prime 356869 := by norm_num

private theorem prime_sixtyNineBO_386119 : Nat.Prime 386119 := by norm_num

private theorem prime_sixtyNineBO_396871 : Nat.Prime 396871 := by norm_num

private theorem prime_sixtyNineBO_414857 : Nat.Prime 414857 := by norm_num

private theorem prime_sixtyNineBO_421397 : Nat.Prime 421397 := by norm_num

private theorem prime_sixtyNineBO_428759 : Nat.Prime 428759 := by norm_num

private theorem prime_sixtyNineBO_470201 : Nat.Prime 470201 := by norm_num

private theorem prime_sixtyNineBO_521567 : Nat.Prime 521567 := by norm_num

private theorem prime_sixtyNineBO_559703 : Nat.Prime 559703 := by norm_num

private theorem prime_sixtyNineBO_559859 : Nat.Prime 559859 := by norm_num

private theorem prime_sixtyNineBO_569797 : Nat.Prime 569797 := by norm_num

private theorem prime_sixtyNineBO_570181 : Nat.Prime 570181 := by norm_num

private theorem prime_sixtyNineBO_570643 : Nat.Prime 570643 := by norm_num

private theorem prime_sixtyNineBO_632923 : Nat.Prime 632923 := by norm_num

private theorem prime_sixtyNineBO_641873 : Nat.Prime 641873 := by norm_num

private theorem prime_sixtyNineBO_682447 : Nat.Prime 682447 := by norm_num

private theorem prime_sixtyNineBO_706897 : Nat.Prime 706897 := by norm_num

private theorem prime_sixtyNineBO_708359 : Nat.Prime 708359 := by norm_num

private theorem prime_sixtyNineBO_726367 : Nat.Prime 726367 := by norm_num

private theorem prime_sixtyNineBO_737683 : Nat.Prime 737683 := by norm_num

private theorem prime_sixtyNineBO_750209 : Nat.Prime 750209 := by norm_num

private theorem prime_sixtyNineBO_760729 : Nat.Prime 760729 := by norm_num

private theorem prime_sixtyNineBO_796247 : Nat.Prime 796247 := by norm_num

private theorem prime_sixtyNineBO_855607 : Nat.Prime 855607 := by norm_num

private theorem prime_sixtyNineBO_967607 : Nat.Prime 967607 := by norm_num

private theorem prime_sixtyNineBO_969421 : Nat.Prime 969421 := by norm_num

private theorem prime_sixtyNineBO_988231 : Nat.Prime 988231 := by norm_num

private theorem prime_sixtyNineBO_1030049 : Nat.Prime 1030049 := by norm_num

private theorem prime_sixtyNineBO_1040407 : Nat.Prime 1040407 := by norm_num

private theorem prime_sixtyNineBO_1143679 : Nat.Prime 1143679 := by norm_num

private theorem prime_sixtyNineBO_1151629 : Nat.Prime 1151629 := by norm_num

private theorem prime_sixtyNineBO_1256369 : Nat.Prime 1256369 := by norm_num

private theorem prime_sixtyNineBO_1344779 : Nat.Prime 1344779 := by norm_num

private theorem prime_sixtyNineBO_1370861 : Nat.Prime 1370861 := by norm_num

private theorem prime_sixtyNineBO_1408021 : Nat.Prime 1408021 := by norm_num

private theorem prime_sixtyNineBO_1506877 : Nat.Prime 1506877 := by norm_num

private theorem prime_sixtyNineBO_1625147 : Nat.Prime 1625147 := by norm_num

private theorem prime_sixtyNineBO_1672009 : Nat.Prime 1672009 := by norm_num

private theorem prime_sixtyNineBO_1710691 : Nat.Prime 1710691 := by norm_num

private theorem prime_sixtyNineBO_1950763 : Nat.Prime 1950763 := by norm_num

private theorem prime_sixtyNineBO_1953857 : Nat.Prime 1953857 := by norm_num

private theorem prime_sixtyNineBO_2127467 : Nat.Prime 2127467 := by norm_num

private theorem prime_sixtyNineBO_2132759 : Nat.Prime 2132759 := by norm_num

private theorem prime_sixtyNineBO_2146159 : Nat.Prime 2146159 := by norm_num

private theorem prime_sixtyNineBO_2220403 : Nat.Prime 2220403 := by norm_num

private theorem prime_sixtyNineBO_2278487 : Nat.Prime 2278487 := by norm_num

private theorem prime_sixtyNineBO_2367857 : Nat.Prime 2367857 := by norm_num

private theorem prime_sixtyNineBO_2435533 : Nat.Prime 2435533 := by norm_num

private theorem prime_sixtyNineBO_2583859 : Nat.Prime 2583859 := by norm_num

private theorem prime_sixtyNineBO_2779771 : Nat.Prime 2779771 := by norm_num

private theorem prime_sixtyNineBO_2795381 : Nat.Prime 2795381 := by norm_num

private theorem prime_sixtyNineBO_2799989 : Nat.Prime 2799989 := by norm_num

private theorem prime_sixtyNineBO_3216691 : Nat.Prime 3216691 := by norm_num

private theorem prime_sixtyNineBO_3286091 : Nat.Prime 3286091 := by norm_num

private theorem prime_sixtyNineBO_3434369 : Nat.Prime 3434369 := by norm_num

private theorem prime_sixtyNineBO_3583781 : Nat.Prime 3583781 := by norm_num

private theorem prime_sixtyNineBO_3589991 : Nat.Prime 3589991 := by norm_num

private theorem prime_sixtyNineBO_3625423 : Nat.Prime 3625423 := by norm_num

private theorem prime_sixtyNineBO_3676909 : Nat.Prime 3676909 := by norm_num

private theorem prime_sixtyNineBO_4005983 : Nat.Prime 4005983 := by norm_num

private theorem prime_sixtyNineBO_4038257 : Nat.Prime 4038257 := by norm_num

private theorem prime_sixtyNineBO_4043899 : Nat.Prime 4043899 := by norm_num

private theorem prime_sixtyNineBO_4415153 : Nat.Prime 4415153 := by norm_num

private theorem prime_sixtyNineBO_4493009 : Nat.Prime 4493009 := by norm_num

private theorem prime_sixtyNineBO_4725241 : Nat.Prime 4725241 := by norm_num

private theorem prime_sixtyNineBO_4808737 : Nat.Prime 4808737 := by norm_num

private theorem prime_sixtyNineBO_5087939 : Nat.Prime 5087939 := by norm_num

private theorem prime_sixtyNineBO_5193889 : Nat.Prime 5193889 := by norm_num

private theorem prime_sixtyNineBO_5401507 : Nat.Prime 5401507 := by norm_num

private theorem prime_sixtyNineBO_5495081 : Nat.Prime 5495081 := by norm_num

private theorem prime_sixtyNineBO_5545049 : Nat.Prime 5545049 := by norm_num

private theorem prime_sixtyNineBO_5711903 : Nat.Prime 5711903 := by norm_num

private theorem prime_sixtyNineBO_5866711 : Nat.Prime 5866711 := by norm_num

private theorem prime_sixtyNineBO_6053461 : Nat.Prime 6053461 := by norm_num

private theorem prime_sixtyNineBO_6533089 : Nat.Prime 6533089 := by norm_num

private theorem prime_sixtyNineBO_6558037 : Nat.Prime 6558037 := by norm_num

private theorem prime_sixtyNineBO_6583189 : Nat.Prime 6583189 := by norm_num

private theorem prime_sixtyNineBO_6711473 : Nat.Prime 6711473 := by norm_num

private theorem prime_sixtyNineBO_6755761 : Nat.Prime 6755761 := by norm_num

private theorem prime_sixtyNineBO_7469843 : Nat.Prime 7469843 := by norm_num

private theorem prime_sixtyNineBO_7502771 : Nat.Prime 7502771 := by norm_num

private theorem prime_sixtyNineBO_9068623 : Nat.Prime 9068623 := by norm_num

private theorem prime_sixtyNineBO_9603409 : Nat.Prime 9603409 := by norm_num

private theorem prime_sixtyNineBO_10308673 : Nat.Prime 10308673 := by norm_num

private theorem prime_sixtyNineBO_10328167 : Nat.Prime 10328167 := by norm_num

private theorem prime_sixtyNineBO_10422043 : Nat.Prime 10422043 := by norm_num

private theorem prime_sixtyNineBO_10458599 : Nat.Prime 10458599 := by norm_num

private theorem prime_sixtyNineBO_10651931 : Nat.Prime 10651931 := by norm_num

private theorem prime_sixtyNineBO_11284211 : Nat.Prime 11284211 := by norm_num

private theorem prime_sixtyNineBO_12209579 : Nat.Prime 12209579 := by norm_num

private theorem prime_sixtyNineBO_12641171 : Nat.Prime 12641171 := by norm_num

private theorem prime_sixtyNineBO_14648167 : Nat.Prime 14648167 := by norm_num

private theorem prime_sixtyNineBO_14740571 : Nat.Prime 14740571 := by norm_num

private theorem prime_sixtyNineBO_15651289 : Nat.Prime 15651289 := by norm_num

private theorem prime_sixtyNineBO_19381039 : Nat.Prime 19381039 := by norm_num

private theorem prime_sixtyNineBO_20314663 : Nat.Prime 20314663 := by norm_num

private theorem prime_sixtyNineBO_22157063 : Nat.Prime 22157063 := by norm_num

private theorem prime_sixtyNineBO_23553181 : Nat.Prime 23553181 := by norm_num

private theorem prime_sixtyNineBO_23972749 : Nat.Prime 23972749 := by norm_num

private theorem prime_sixtyNineBO_24406219 : Nat.Prime 24406219 := by norm_num

private theorem prime_sixtyNineBO_29095589 : Nat.Prime 29095589 := by norm_num

private theorem prime_sixtyNineBO_30577619 : Nat.Prime 30577619 := by
  apply lucas_primality 30577619 (2 : ZMod 30577619)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3719, 1), (4111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3719, 1), (4111, 1)] : List FactorBlock).map factorBlockValue).prod) = 30577619 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3719
      · exact prime_sixtyNineBO_4111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 30577619) ^ 15288809 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 30577619) ^ 8222 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 30577619) ^ 7438 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_36639107 : Nat.Prime 36639107 := by
  apply lucas_primality 36639107 (2 : ZMod 36639107)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (19, 1), (181, 1), (761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (19, 1), (181, 1), (761, 1)] : List FactorBlock).map factorBlockValue).prod) = 36639107 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_7
      · exact prime_sixtyNineBO_19
      · exact prime_sixtyNineBO_181
      · exact prime_sixtyNineBO_761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 36639107) ^ 18319553 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 36639107) ^ 5234158 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 36639107) ^ 1928374 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 36639107) ^ 202426 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 36639107) ^ 48146 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_37128541 : Nat.Prime 37128541 := by
  apply lucas_primality 37128541 (2 : ZMod 37128541)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (353, 1), (1753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (353, 1), (1753, 1)] : List FactorBlock).map factorBlockValue).prod) = 37128541 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_5
      · exact prime_sixtyNineBO_353
      · exact prime_sixtyNineBO_1753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 37128541) ^ 18564270 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 37128541) ^ 12376180 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 37128541) ^ 7425708 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 37128541) ^ 105180 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 37128541) ^ 21180 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_38230981 : Nat.Prime 38230981 := by
  apply lucas_primality 38230981 (2 : ZMod 38230981)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (521, 1), (1223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (521, 1), (1223, 1)] : List FactorBlock).map factorBlockValue).prod) = 38230981 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_5
      · exact prime_sixtyNineBO_521
      · exact prime_sixtyNineBO_1223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 38230981) ^ 19115490 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 38230981) ^ 12743660 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 38230981) ^ 7646196 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 38230981) ^ 73380 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 38230981) ^ 31260 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_38512381 : Nat.Prime 38512381 := by
  apply lucas_primality 38512381 (6 : ZMod 38512381)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (641873, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (641873, 1)] : List FactorBlock).map factorBlockValue).prod) = 38512381 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_5
      · exact prime_sixtyNineBO_641873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 38512381) ^ 19256190 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (6 : ZMod 38512381) ^ 12837460 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (6 : ZMod 38512381) ^ 7702476 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (6 : ZMod 38512381) ^ 60 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_40534567 : Nat.Prime 40534567 := by
  apply lucas_primality 40534567 (13 : ZMod 40534567)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (6755761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (6755761, 1)] : List FactorBlock).map factorBlockValue).prod) = 40534567 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_6755761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 40534567) ^ 20267283 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (13 : ZMod 40534567) ^ 13511522 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (13 : ZMod 40534567) ^ 6 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_40838081 : Nat.Prime 40838081 := by
  apply lucas_primality 40838081 (3 : ZMod 40838081)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (5, 1), (17, 1), (7507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (5, 1), (17, 1), (7507, 1)] : List FactorBlock).map factorBlockValue).prod) = 40838081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_5
      · exact prime_sixtyNineBO_17
      · exact prime_sixtyNineBO_7507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 40838081) ^ 20419040 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 40838081) ^ 8167616 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 40838081) ^ 2402240 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 40838081) ^ 5440 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_42443069 : Nat.Prime 42443069 := by
  apply lucas_primality 42443069 (2 : ZMod 42443069)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (47, 1), (61, 1), (3701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (47, 1), (61, 1), (3701, 1)] : List FactorBlock).map factorBlockValue).prod) = 42443069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_47
      · exact prime_sixtyNineBO_61
      · exact prime_sixtyNineBO_3701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 42443069) ^ 21221534 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 42443069) ^ 903044 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 42443069) ^ 695788 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 42443069) ^ 11468 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_42507991 : Nat.Prime 42507991 := by
  apply lucas_primality 42507991 (3 : ZMod 42507991)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 6), (5, 1), (7, 3), (17, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 6), (5, 1), (7, 3), (17, 1)] : List FactorBlock).map factorBlockValue).prod) = 42507991 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_5
      · exact prime_sixtyNineBO_7
      · exact prime_sixtyNineBO_17
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 42507991) ^ 21253995 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 42507991) ^ 14169330 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 42507991) ^ 8501598 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 42507991) ^ 6072570 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 42507991) ^ 2500470 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_43150313 : Nat.Prime 43150313 := by
  apply lucas_primality 43150313 (3 : ZMod 43150313)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (383, 1), (14083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (383, 1), (14083, 1)] : List FactorBlock).map factorBlockValue).prod) = 43150313 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_383
      · exact prime_sixtyNineBO_14083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 43150313) ^ 21575156 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 43150313) ^ 112664 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 43150313) ^ 3064 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_45643987 : Nat.Prime 45643987 := by
  apply lucas_primality 45643987 (2 : ZMod 45643987)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (139, 1), (2027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (139, 1), (2027, 1)] : List FactorBlock).map factorBlockValue).prod) = 45643987 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_139
      · exact prime_sixtyNineBO_2027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 45643987) ^ 22821993 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 45643987) ^ 15214662 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 45643987) ^ 328374 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 45643987) ^ 22518 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_46941031 : Nat.Prime 46941031 := by
  apply lucas_primality 46941031 (6 : ZMod 46941031)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (521567, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (521567, 1)] : List FactorBlock).map factorBlockValue).prod) = 46941031 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_5
      · exact prime_sixtyNineBO_521567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 46941031) ^ 23470515 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (6 : ZMod 46941031) ^ 15647010 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (6 : ZMod 46941031) ^ 9388206 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (6 : ZMod 46941031) ^ 90 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_48593257 : Nat.Prime 48593257 := by
  apply lucas_primality 48593257 (5 : ZMod 48593257)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (883, 1), (2293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (883, 1), (2293, 1)] : List FactorBlock).map factorBlockValue).prod) = 48593257 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_883
      · exact prime_sixtyNineBO_2293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 48593257) ^ 24296628 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 48593257) ^ 16197752 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 48593257) ^ 55032 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 48593257) ^ 21192 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_49291009 : Nat.Prime 49291009 := by
  apply lucas_primality 49291009 (7 : ZMod 49291009)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 1), (13, 1), (4937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 1), (13, 1), (4937, 1)] : List FactorBlock).map factorBlockValue).prod) = 49291009 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_13
      · exact prime_sixtyNineBO_4937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 49291009) ^ 24645504 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (7 : ZMod 49291009) ^ 16430336 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (7 : ZMod 49291009) ^ 3791616 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (7 : ZMod 49291009) ^ 9984 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_49786129 : Nat.Prime 49786129 := by
  apply lucas_primality 49786129 (11 : ZMod 49786129)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (7, 1), (49391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (7, 1), (49391, 1)] : List FactorBlock).map factorBlockValue).prod) = 49786129 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_7
      · exact prime_sixtyNineBO_49391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 49786129) ^ 24893064 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (11 : ZMod 49786129) ^ 16595376 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (11 : ZMod 49786129) ^ 7112304 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (11 : ZMod 49786129) ^ 1008 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_54031291 : Nat.Prime 54031291 := by
  apply lucas_primality 54031291 (3 : ZMod 54031291)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (643, 1), (2801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (643, 1), (2801, 1)] : List FactorBlock).map factorBlockValue).prod) = 54031291 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_5
      · exact prime_sixtyNineBO_643
      · exact prime_sixtyNineBO_2801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 54031291) ^ 27015645 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 54031291) ^ 18010430 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 54031291) ^ 10806258 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 54031291) ^ 84030 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 54031291) ^ 19290 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_55622647 : Nat.Prime 55622647 := by
  apply lucas_primality 55622647 (6 : ZMod 55622647)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (1030049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (1030049, 1)] : List FactorBlock).map factorBlockValue).prod) = 55622647 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_1030049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 55622647) ^ 27811323 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (6 : ZMod 55622647) ^ 18540882 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (6 : ZMod 55622647) ^ 54 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_56484629 : Nat.Prime 56484629 := by
  apply lucas_primality 56484629 (2 : ZMod 56484629)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (43, 1), (197, 1), (1667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (43, 1), (197, 1), (1667, 1)] : List FactorBlock).map factorBlockValue).prod) = 56484629 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_43
      · exact prime_sixtyNineBO_197
      · exact prime_sixtyNineBO_1667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 56484629) ^ 28242314 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 56484629) ^ 1313596 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 56484629) ^ 286724 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 56484629) ^ 33884 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_58592669 : Nat.Prime 58592669 := by
  apply lucas_primality 58592669 (2 : ZMod 58592669)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (14648167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (14648167, 1)] : List FactorBlock).map factorBlockValue).prod) = 58592669 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_14648167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 58592669) ^ 29296334 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 58592669) ^ 4 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_65831891 : Nat.Prime 65831891 := by
  apply lucas_primality 65831891 (2 : ZMod 65831891)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (6583189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (6583189, 1)] : List FactorBlock).map factorBlockValue).prod) = 65831891 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_5
      · exact prime_sixtyNineBO_6583189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 65831891) ^ 32915945 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 65831891) ^ 13166378 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 65831891) ^ 10 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_65891129 : Nat.Prime 65891129 := by
  apply lucas_primality 65891129 (3 : ZMod 65891129)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (281, 1), (29311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (281, 1), (29311, 1)] : List FactorBlock).map factorBlockValue).prod) = 65891129 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_281
      · exact prime_sixtyNineBO_29311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 65891129) ^ 32945564 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 65891129) ^ 234488 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 65891129) ^ 2248 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_70155703 : Nat.Prime 70155703 := by
  apply lucas_primality 70155703 (5 : ZMod 70155703)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (17, 1), (229267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (17, 1), (229267, 1)] : List FactorBlock).map factorBlockValue).prod) = 70155703 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_17
      · exact prime_sixtyNineBO_229267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 70155703) ^ 35077851 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 70155703) ^ 23385234 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 70155703) ^ 4126806 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 70155703) ^ 306 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_70267271 : Nat.Prime 70267271 := by
  apply lucas_primality 70267271 (7 : ZMod 70267271)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (521, 1), (13487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (521, 1), (13487, 1)] : List FactorBlock).map factorBlockValue).prod) = 70267271 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_5
      · exact prime_sixtyNineBO_521
      · exact prime_sixtyNineBO_13487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 70267271) ^ 35133635 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (7 : ZMod 70267271) ^ 14053454 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (7 : ZMod 70267271) ^ 134870 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (7 : ZMod 70267271) ^ 5210 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_79532617 : Nat.Prime 79532617 := by
  apply lucas_primality 79532617 (11 : ZMod 79532617)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (29, 1), (229, 1), (499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (29, 1), (229, 1), (499, 1)] : List FactorBlock).map factorBlockValue).prod) = 79532617 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_29
      · exact prime_sixtyNineBO_229
      · exact prime_sixtyNineBO_499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 79532617) ^ 39766308 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (11 : ZMod 79532617) ^ 26510872 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (11 : ZMod 79532617) ^ 2742504 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (11 : ZMod 79532617) ^ 347304 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (11 : ZMod 79532617) ^ 159384 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_79918877 : Nat.Prime 79918877 := by
  apply lucas_primality 79918877 (2 : ZMod 79918877)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (101, 1), (337, 1), (587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (101, 1), (337, 1), (587, 1)] : List FactorBlock).map factorBlockValue).prod) = 79918877 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_101
      · exact prime_sixtyNineBO_337
      · exact prime_sixtyNineBO_587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 79918877) ^ 39959438 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 79918877) ^ 791276 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 79918877) ^ 237148 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 79918877) ^ 136148 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_81676163 : Nat.Prime 81676163 := by
  apply lucas_primality 81676163 (2 : ZMod 81676163)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (40838081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (40838081, 1)] : List FactorBlock).map factorBlockValue).prod) = 81676163 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_40838081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 81676163) ^ 40838081 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 81676163) ^ 2 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_82809689 : Nat.Prime 82809689 := by
  apply lucas_primality 82809689 (3 : ZMod 82809689)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (796247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (796247, 1)] : List FactorBlock).map factorBlockValue).prod) = 82809689 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_13
      · exact prime_sixtyNineBO_796247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 82809689) ^ 41404844 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 82809689) ^ 6369976 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 82809689) ^ 104 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_91652177 : Nat.Prime 91652177 := by
  apply lucas_primality 91652177 (3 : ZMod 91652177)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (11, 2), (6763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (11, 2), (6763, 1)] : List FactorBlock).map factorBlockValue).prod) = 91652177 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_7
      · exact prime_sixtyNineBO_11
      · exact prime_sixtyNineBO_6763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 91652177) ^ 45826088 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 91652177) ^ 13093168 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 91652177) ^ 8332016 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 91652177) ^ 13552 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_92576929 : Nat.Prime 92576929 := by
  apply lucas_primality 92576929 (17 : ZMod 92576929)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (137, 1), (7039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (137, 1), (7039, 1)] : List FactorBlock).map factorBlockValue).prod) = 92576929 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_137
      · exact prime_sixtyNineBO_7039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 92576929) ^ 46288464 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (17 : ZMod 92576929) ^ 30858976 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (17 : ZMod 92576929) ^ 675744 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (17 : ZMod 92576929) ^ 13152 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_110190599 : Nat.Prime 110190599 := by
  apply lucas_primality 110190599 (14 : ZMod 110190599)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (1693, 1), (4649, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (1693, 1), (4649, 1)] : List FactorBlock).map factorBlockValue).prod) = 110190599 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_7
      · exact prime_sixtyNineBO_1693
      · exact prime_sixtyNineBO_4649
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 110190599) ^ 55095299 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (14 : ZMod 110190599) ^ 15741514 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (14 : ZMod 110190599) ^ 65086 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (14 : ZMod 110190599) ^ 23702 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_113841667 : Nat.Prime 113841667 := by
  apply lucas_primality 113841667 (3 : ZMod 113841667)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (41, 1), (51419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (41, 1), (51419, 1)] : List FactorBlock).map factorBlockValue).prod) = 113841667 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_41
      · exact prime_sixtyNineBO_51419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 113841667) ^ 56920833 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 113841667) ^ 37947222 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 113841667) ^ 2776626 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 113841667) ^ 2214 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_123632501 : Nat.Prime 123632501 := by
  apply lucas_primality 123632501 (2 : ZMod 123632501)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 4), (17, 1), (2909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 4), (17, 1), (2909, 1)] : List FactorBlock).map factorBlockValue).prod) = 123632501 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_5
      · exact prime_sixtyNineBO_17
      · exact prime_sixtyNineBO_2909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 123632501) ^ 61816250 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 123632501) ^ 24726500 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 123632501) ^ 7272500 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 123632501) ^ 42500 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_127802473 : Nat.Prime 127802473 := by
  apply lucas_primality 127802473 (5 : ZMod 127802473)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (760729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (760729, 1)] : List FactorBlock).map factorBlockValue).prod) = 127802473 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_7
      · exact prime_sixtyNineBO_760729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 127802473) ^ 63901236 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 127802473) ^ 42600824 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 127802473) ^ 18257496 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 127802473) ^ 168 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_137354177 : Nat.Prime 137354177 := by
  apply lucas_primality 137354177 (3 : ZMod 137354177)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (2146159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (2146159, 1)] : List FactorBlock).map factorBlockValue).prod) = 137354177 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_2146159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 137354177) ^ 68677088 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 137354177) ^ 64 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_146078533 : Nat.Prime 146078533 := by
  apply lucas_primality 146078533 (5 : ZMod 146078533)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (397, 1), (3407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (397, 1), (3407, 1)] : List FactorBlock).map factorBlockValue).prod) = 146078533 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_397
      · exact prime_sixtyNineBO_3407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 146078533) ^ 73039266 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 146078533) ^ 48692844 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 146078533) ^ 367956 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 146078533) ^ 42876 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_169806601 : Nat.Prime 169806601 := by
  apply lucas_primality 169806601 (7 : ZMod 169806601)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 2), (29, 1), (3253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 2), (29, 1), (3253, 1)] : List FactorBlock).map factorBlockValue).prod) = 169806601 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_5
      · exact prime_sixtyNineBO_29
      · exact prime_sixtyNineBO_3253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 169806601) ^ 84903300 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (7 : ZMod 169806601) ^ 56602200 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (7 : ZMod 169806601) ^ 33961320 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (7 : ZMod 169806601) ^ 5855400 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (7 : ZMod 169806601) ^ 52200 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_181921049 : Nat.Prime 181921049 := by
  apply lucas_primality 181921049 (3 : ZMod 181921049)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (19, 1), (257, 1), (4657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (19, 1), (257, 1), (4657, 1)] : List FactorBlock).map factorBlockValue).prod) = 181921049 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_19
      · exact prime_sixtyNineBO_257
      · exact prime_sixtyNineBO_4657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 181921049) ^ 90960524 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 181921049) ^ 9574792 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 181921049) ^ 707864 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 181921049) ^ 39064 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_182248169 : Nat.Prime 182248169 := by
  apply lucas_primality 182248169 (3 : ZMod 182248169)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (59, 1), (386119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (59, 1), (386119, 1)] : List FactorBlock).map factorBlockValue).prod) = 182248169 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_59
      · exact prime_sixtyNineBO_386119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 182248169) ^ 91124084 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 182248169) ^ 3088952 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 182248169) ^ 472 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_182926493 : Nat.Prime 182926493 := by
  apply lucas_primality 182926493 (2 : ZMod 182926493)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (6533089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (6533089, 1)] : List FactorBlock).map factorBlockValue).prod) = 182926493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_7
      · exact prime_sixtyNineBO_6533089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 182926493) ^ 91463246 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 182926493) ^ 26132356 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 182926493) ^ 28 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_211324021 : Nat.Prime 211324021 := by
  apply lucas_primality 211324021 (2 : ZMod 211324021)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (37, 1), (95191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (37, 1), (95191, 1)] : List FactorBlock).map factorBlockValue).prod) = 211324021 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_5
      · exact prime_sixtyNineBO_37
      · exact prime_sixtyNineBO_95191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 211324021) ^ 105662010 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 211324021) ^ 70441340 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 211324021) ^ 42264804 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 211324021) ^ 5711460 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 211324021) ^ 2220 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_216594839 : Nat.Prime 216594839 := by
  apply lucas_primality 216594839 (13 : ZMod 216594839)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7517, 1), (14407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7517, 1), (14407, 1)] : List FactorBlock).map factorBlockValue).prod) = 216594839 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_7517
      · exact prime_sixtyNineBO_14407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 216594839) ^ 108297419 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (13 : ZMod 216594839) ^ 28814 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (13 : ZMod 216594839) ^ 15034 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_229385887 : Nat.Prime 229385887 := by
  apply lucas_primality 229385887 (3 : ZMod 229385887)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (38230981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (38230981, 1)] : List FactorBlock).map factorBlockValue).prod) = 229385887 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_38230981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 229385887) ^ 114692943 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 229385887) ^ 76461962 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 229385887) ^ 6 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_232764713 : Nat.Prime 232764713 := by
  apply lucas_primality 232764713 (3 : ZMod 232764713)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (29095589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (29095589, 1)] : List FactorBlock).map factorBlockValue).prod) = 232764713 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_29095589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 232764713) ^ 116382356 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 232764713) ^ 8 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_233462791 : Nat.Prime 233462791 := by
  apply lucas_primality 233462791 (6 : ZMod 233462791)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (11, 1), (78607, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (11, 1), (78607, 1)] : List FactorBlock).map factorBlockValue).prod) = 233462791 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_5
      · exact prime_sixtyNineBO_11
      · exact prime_sixtyNineBO_78607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 233462791) ^ 116731395 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (6 : ZMod 233462791) ^ 77820930 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (6 : ZMod 233462791) ^ 46692558 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (6 : ZMod 233462791) ^ 21223890 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (6 : ZMod 233462791) ^ 2970 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_234462841 : Nat.Prime 234462841 := by
  apply lucas_primality 234462841 (11 : ZMod 234462841)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (1953857, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (1953857, 1)] : List FactorBlock).map factorBlockValue).prod) = 234462841 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_5
      · exact prime_sixtyNineBO_1953857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 234462841) ^ 117231420 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (11 : ZMod 234462841) ^ 78154280 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (11 : ZMod 234462841) ^ 46892568 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (11 : ZMod 234462841) ^ 120 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_249818761 : Nat.Prime 249818761 := by
  apply lucas_primality 249818761 (7 : ZMod 249818761)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (29, 1), (23929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (29, 1), (23929, 1)] : List FactorBlock).map factorBlockValue).prod) = 249818761 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_5
      · exact prime_sixtyNineBO_29
      · exact prime_sixtyNineBO_23929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 249818761) ^ 124909380 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (7 : ZMod 249818761) ^ 83272920 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (7 : ZMod 249818761) ^ 49963752 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (7 : ZMod 249818761) ^ 8614440 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (7 : ZMod 249818761) ^ 10440 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_280622813 : Nat.Prime 280622813 := by
  apply lucas_primality 280622813 (2 : ZMod 280622813)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (70155703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (70155703, 1)] : List FactorBlock).map factorBlockValue).prod) = 280622813 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_70155703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 280622813) ^ 140311406 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 280622813) ^ 4 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_321768913 : Nat.Prime 321768913 := by
  apply lucas_primality 321768913 (5 : ZMod 321768913)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (2267, 1), (2957, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (2267, 1), (2957, 1)] : List FactorBlock).map factorBlockValue).prod) = 321768913 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_2267
      · exact prime_sixtyNineBO_2957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 321768913) ^ 160884456 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 321768913) ^ 107256304 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 321768913) ^ 141936 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 321768913) ^ 108816 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_348050669 : Nat.Prime 348050669 := by
  apply lucas_primality 348050669 (2 : ZMod 348050669)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (1381, 1), (9001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (1381, 1), (9001, 1)] : List FactorBlock).map factorBlockValue).prod) = 348050669 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_7
      · exact prime_sixtyNineBO_1381
      · exact prime_sixtyNineBO_9001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 348050669) ^ 174025334 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 348050669) ^ 49721524 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 348050669) ^ 252028 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 348050669) ^ 38668 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_348294839 : Nat.Prime 348294839 := by
  apply lucas_primality 348294839 (7 : ZMod 348294839)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (383, 1), (12289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (383, 1), (12289, 1)] : List FactorBlock).map factorBlockValue).prod) = 348294839 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_37
      · exact prime_sixtyNineBO_383
      · exact prime_sixtyNineBO_12289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 348294839) ^ 174147419 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (7 : ZMod 348294839) ^ 9413374 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (7 : ZMod 348294839) ^ 909386 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (7 : ZMod 348294839) ^ 28342 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_364496339 : Nat.Prime 364496339 := by
  apply lucas_primality 364496339 (2 : ZMod 364496339)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (182248169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (182248169, 1)] : List FactorBlock).map factorBlockValue).prod) = 364496339 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_182248169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 364496339) ^ 182248169 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 364496339) ^ 2 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_364823819 : Nat.Prime 364823819 := by
  apply lucas_primality 364823819 (2 : ZMod 364823819)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (149, 1), (941, 1), (1301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (149, 1), (941, 1), (1301, 1)] : List FactorBlock).map factorBlockValue).prod) = 364823819 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_149
      · exact prime_sixtyNineBO_941
      · exact prime_sixtyNineBO_1301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 364823819) ^ 182411909 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 364823819) ^ 2448482 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 364823819) ^ 387698 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 364823819) ^ 280418 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_368994403 : Nat.Prime 368994403 := by
  apply lucas_primality 368994403 (2 : ZMod 368994403)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 2), (19, 1), (97, 1), (227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 2), (19, 1), (97, 1), (227, 1)] : List FactorBlock).map factorBlockValue).prod) = 368994403 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_7
      · exact prime_sixtyNineBO_19
      · exact prime_sixtyNineBO_97
      · exact prime_sixtyNineBO_227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 368994403) ^ 184497201 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 368994403) ^ 122998134 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 368994403) ^ 52713486 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 368994403) ^ 19420758 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 368994403) ^ 3804066 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 368994403) ^ 1625526 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_404813113 : Nat.Prime 404813113 := by
  apply lucas_primality 404813113 (10 : ZMod 404813113)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (17, 1), (90199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (17, 1), (90199, 1)] : List FactorBlock).map factorBlockValue).prod) = 404813113 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_11
      · exact prime_sixtyNineBO_17
      · exact prime_sixtyNineBO_90199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 404813113) ^ 202406556 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (10 : ZMod 404813113) ^ 134937704 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (10 : ZMod 404813113) ^ 36801192 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (10 : ZMod 404813113) ^ 23812536 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (10 : ZMod 404813113) ^ 4488 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_408387059 : Nat.Prime 408387059 := by
  apply lucas_primality 408387059 (2 : ZMod 408387059)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (83, 1), (919, 1), (2677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (83, 1), (919, 1), (2677, 1)] : List FactorBlock).map factorBlockValue).prod) = 408387059 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_83
      · exact prime_sixtyNineBO_919
      · exact prime_sixtyNineBO_2677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 408387059) ^ 204193529 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 408387059) ^ 4920326 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 408387059) ^ 444382 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 408387059) ^ 152554 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_419196521 : Nat.Prime 419196521 := by
  apply lucas_primality 419196521 (3 : ZMod 419196521)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (127, 1), (179, 1), (461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (127, 1), (179, 1), (461, 1)] : List FactorBlock).map factorBlockValue).prod) = 419196521 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_5
      · exact prime_sixtyNineBO_127
      · exact prime_sixtyNineBO_179
      · exact prime_sixtyNineBO_461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 419196521) ^ 209598260 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 419196521) ^ 83839304 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 419196521) ^ 3300760 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 419196521) ^ 2341880 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 419196521) ^ 909320 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_429700991 : Nat.Prime 429700991 := by
  apply lucas_primality 429700991 (11 : ZMod 429700991)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (193, 1), (222643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (193, 1), (222643, 1)] : List FactorBlock).map factorBlockValue).prod) = 429700991 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_5
      · exact prime_sixtyNineBO_193
      · exact prime_sixtyNineBO_222643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 429700991) ^ 214850495 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (11 : ZMod 429700991) ^ 85940198 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (11 : ZMod 429700991) ^ 2226430 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (11 : ZMod 429700991) ^ 1930 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_441370723 : Nat.Prime 441370723 := by
  apply lucas_primality 441370723 (2 : ZMod 441370723)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (19, 1), (431, 1), (691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (19, 1), (431, 1), (691, 1)] : List FactorBlock).map factorBlockValue).prod) = 441370723 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_13
      · exact prime_sixtyNineBO_19
      · exact prime_sixtyNineBO_431
      · exact prime_sixtyNineBO_691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 441370723) ^ 220685361 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 441370723) ^ 147123574 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 441370723) ^ 33951594 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 441370723) ^ 23230038 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 441370723) ^ 1024062 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 441370723) ^ 638742 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_479513263 : Nat.Prime 479513263 := by
  apply lucas_primality 479513263 (5 : ZMod 479513263)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (79918877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (79918877, 1)] : List FactorBlock).map factorBlockValue).prod) = 479513263 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_79918877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 479513263) ^ 239756631 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 479513263) ^ 159837754 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 479513263) ^ 6 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_522228463 : Nat.Prime 522228463 := by
  apply lucas_primality 522228463 (3 : ZMod 522228463)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (29, 1), (428759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (29, 1), (428759, 1)] : List FactorBlock).map factorBlockValue).prod) = 522228463 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_7
      · exact prime_sixtyNineBO_29
      · exact prime_sixtyNineBO_428759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 522228463) ^ 261114231 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 522228463) ^ 174076154 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 522228463) ^ 74604066 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 522228463) ^ 18007878 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 522228463) ^ 1218 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_532439417 : Nat.Prime 532439417 := by
  apply lucas_primality 532439417 (3 : ZMod 532439417)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (43, 1), (911, 1), (1699, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (43, 1), (911, 1), (1699, 1)] : List FactorBlock).map factorBlockValue).prod) = 532439417 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_43
      · exact prime_sixtyNineBO_911
      · exact prime_sixtyNineBO_1699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 532439417) ^ 266219708 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 532439417) ^ 12382312 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 532439417) ^ 584456 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 532439417) ^ 313384 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_677815549 : Nat.Prime 677815549 := by
  apply lucas_primality 677815549 (2 : ZMod 677815549)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (56484629, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (56484629, 1)] : List FactorBlock).map factorBlockValue).prod) = 677815549 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_56484629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 677815549) ^ 338907774 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 677815549) ^ 225938516 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 677815549) ^ 12 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_680364071 : Nat.Prime 680364071 := by
  apply lucas_primality 680364071 (7 : ZMod 680364071)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (29, 1), (547, 1), (4289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (29, 1), (547, 1), (4289, 1)] : List FactorBlock).map factorBlockValue).prod) = 680364071 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_5
      · exact prime_sixtyNineBO_29
      · exact prime_sixtyNineBO_547
      · exact prime_sixtyNineBO_4289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 680364071) ^ 340182035 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (7 : ZMod 680364071) ^ 136072814 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (7 : ZMod 680364071) ^ 23460830 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (7 : ZMod 680364071) ^ 1243810 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (7 : ZMod 680364071) ^ 158630 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_696101339 : Nat.Prime 696101339 := by
  apply lucas_primality 696101339 (2 : ZMod 696101339)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (348050669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (348050669, 1)] : List FactorBlock).map factorBlockValue).prod) = 696101339 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_348050669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 696101339) ^ 348050669 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 696101339) ^ 2 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_778396943 : Nat.Prime 778396943 := by
  apply lucas_primality 778396943 (5 : ZMod 778396943)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (139, 1), (2799989, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (139, 1), (2799989, 1)] : List FactorBlock).map factorBlockValue).prod) = 778396943 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_139
      · exact prime_sixtyNineBO_2799989
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 778396943) ^ 389198471 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 778396943) ^ 5599978 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 778396943) ^ 278 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_824125063 : Nat.Prime 824125063 := by
  apply lucas_primality 824125063 (5 : ZMod 824125063)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (137354177, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (137354177, 1)] : List FactorBlock).map factorBlockValue).prod) = 824125063 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_137354177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 824125063) ^ 412062531 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 824125063) ^ 274708354 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 824125063) ^ 6 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_890685119 : Nat.Prime 890685119 := by
  apply lucas_primality 890685119 (7 : ZMod 890685119)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (73, 1), (83, 1), (2371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (73, 1), (83, 1), (2371, 1)] : List FactorBlock).map factorBlockValue).prod) = 890685119 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_31
      · exact prime_sixtyNineBO_73
      · exact prime_sixtyNineBO_83
      · exact prime_sixtyNineBO_2371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 890685119) ^ 445342559 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (7 : ZMod 890685119) ^ 28731778 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (7 : ZMod 890685119) ^ 12201166 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (7 : ZMod 890685119) ^ 10731146 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (7 : ZMod 890685119) ^ 375658 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_917078369 : Nat.Prime 917078369 := by
  apply lucas_primality 917078369 (3 : ZMod 917078369)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (29, 1), (988231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (29, 1), (988231, 1)] : List FactorBlock).map factorBlockValue).prod) = 917078369 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_29
      · exact prime_sixtyNineBO_988231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 917078369) ^ 458539184 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 917078369) ^ 31623392 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 917078369) ^ 928 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_958155329 : Nat.Prime 958155329 := by
  apply lucas_primality 958155329 (3 : ZMod 958155329)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (13, 1), (1151629, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (13, 1), (1151629, 1)] : List FactorBlock).map factorBlockValue).prod) = 958155329 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_13
      · exact prime_sixtyNineBO_1151629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 958155329) ^ 479077664 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 958155329) ^ 73704256 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 958155329) ^ 832 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_1112147693 : Nat.Prime 1112147693 := by
  apply lucas_primality 1112147693 (2 : ZMod 1112147693)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (31, 1), (71, 1), (126323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (31, 1), (71, 1), (126323, 1)] : List FactorBlock).map factorBlockValue).prod) = 1112147693 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_31
      · exact prime_sixtyNineBO_71
      · exact prime_sixtyNineBO_126323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1112147693) ^ 556073846 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1112147693) ^ 35875732 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1112147693) ^ 15664052 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1112147693) ^ 8804 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_1223263049 : Nat.Prime 1223263049 := by
  apply lucas_primality 1223263049 (3 : ZMod 1223263049)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 2), (59, 1), (227, 1), (233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 2), (59, 1), (227, 1), (233, 1)] : List FactorBlock).map factorBlockValue).prod) = 1223263049 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_7
      · exact prime_sixtyNineBO_59
      · exact prime_sixtyNineBO_227
      · exact prime_sixtyNineBO_233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1223263049) ^ 611631524 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1223263049) ^ 174751864 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1223263049) ^ 20733272 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1223263049) ^ 5388824 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1223263049) ^ 5250056 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_1229940941 : Nat.Prime 1229940941 := by
  apply lucas_primality 1229940941 (2 : ZMod 1229940941)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (277, 1), (222011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (277, 1), (222011, 1)] : List FactorBlock).map factorBlockValue).prod) = 1229940941 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_5
      · exact prime_sixtyNineBO_277
      · exact prime_sixtyNineBO_222011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1229940941) ^ 614970470 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1229940941) ^ 245988188 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1229940941) ^ 4440220 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1229940941) ^ 5540 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_1392286067 : Nat.Prime 1392286067 := by
  apply lucas_primality 1392286067 (2 : ZMod 1392286067)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (36639107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (36639107, 1)] : List FactorBlock).map factorBlockValue).prod) = 1392286067 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_19
      · exact prime_sixtyNineBO_36639107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1392286067) ^ 696143033 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1392286067) ^ 73278214 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1392286067) ^ 38 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_1498912567 : Nat.Prime 1498912567 := by
  apply lucas_primality 1498912567 (5 : ZMod 1498912567)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (249818761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (249818761, 1)] : List FactorBlock).map factorBlockValue).prod) = 1498912567 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_249818761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1498912567) ^ 749456283 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 1498912567) ^ 499637522 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 1498912567) ^ 6 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_1530287677 : Nat.Prime 1530287677 := by
  apply lucas_primality 1530287677 (2 : ZMod 1530287677)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (42507991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (42507991, 1)] : List FactorBlock).map factorBlockValue).prod) = 1530287677 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_42507991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1530287677) ^ 765143838 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1530287677) ^ 510095892 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1530287677) ^ 36 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_1809974521 : Nat.Prime 1809974521 := by
  apply lucas_primality 1809974521 (31 : ZMod 1809974521)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (41, 1), (149, 1), (823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (41, 1), (149, 1), (823, 1)] : List FactorBlock).map factorBlockValue).prod) = 1809974521 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_5
      · exact prime_sixtyNineBO_41
      · exact prime_sixtyNineBO_149
      · exact prime_sixtyNineBO_823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (31 : ZMod 1809974521) ^ 904987260 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (31 : ZMod 1809974521) ^ 603324840 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (31 : ZMod 1809974521) ^ 361994904 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (31 : ZMod 1809974521) ^ 44145720 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (31 : ZMod 1809974521) ^ 12147480 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (31 : ZMod 1809974521) ^ 2199240 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_1896637231 : Nat.Prime 1896637231 := by
  apply lucas_primality 1896637231 (3 : ZMod 1896637231)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (353, 1), (59699, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (353, 1), (59699, 1)] : List FactorBlock).map factorBlockValue).prod) = 1896637231 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_5
      · exact prime_sixtyNineBO_353
      · exact prime_sixtyNineBO_59699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1896637231) ^ 948318615 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1896637231) ^ 632212410 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1896637231) ^ 379327446 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1896637231) ^ 5372910 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1896637231) ^ 31770 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_2169310457 : Nat.Prime 2169310457 := by
  apply lucas_primality 2169310457 (3 : ZMod 2169310457)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (67, 1), (541, 1), (7481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (67, 1), (541, 1), (7481, 1)] : List FactorBlock).map factorBlockValue).prod) = 2169310457 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_67
      · exact prime_sixtyNineBO_541
      · exact prime_sixtyNineBO_7481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2169310457) ^ 1084655228 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 2169310457) ^ 32377768 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 2169310457) ^ 4009816 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 2169310457) ^ 289976 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_2183052589 : Nat.Prime 2183052589 := by
  apply lucas_primality 2183052589 (10 : ZMod 2183052589)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (181921049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (181921049, 1)] : List FactorBlock).map factorBlockValue).prod) = 2183052589 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_181921049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 2183052589) ^ 1091526294 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (10 : ZMod 2183052589) ^ 727684196 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (10 : ZMod 2183052589) ^ 12 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_2210828843 : Nat.Prime 2210828843 := by
  apply lucas_primality 2210828843 (2 : ZMod 2210828843)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (6143, 1), (179947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (6143, 1), (179947, 1)] : List FactorBlock).map factorBlockValue).prod) = 2210828843 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_6143
      · exact prime_sixtyNineBO_179947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2210828843) ^ 1105414421 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2210828843) ^ 359894 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2210828843) ^ 12286 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_2289569291 : Nat.Prime 2289569291 := by
  apply lucas_primality 2289569291 (7 : ZMod 2289569291)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (251, 1), (269, 1), (3391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (251, 1), (269, 1), (3391, 1)] : List FactorBlock).map factorBlockValue).prod) = 2289569291 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_5
      · exact prime_sixtyNineBO_251
      · exact prime_sixtyNineBO_269
      · exact prime_sixtyNineBO_3391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 2289569291) ^ 1144784645 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (7 : ZMod 2289569291) ^ 457913858 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (7 : ZMod 2289569291) ^ 9121790 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (7 : ZMod 2289569291) ^ 8511410 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (7 : ZMod 2289569291) ^ 675190 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_2515713553 : Nat.Prime 2515713553 := by
  apply lucas_primality 2515713553 (5 : ZMod 2515713553)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 4), (11, 1), (176467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 4), (11, 1), (176467, 1)] : List FactorBlock).map factorBlockValue).prod) = 2515713553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_11
      · exact prime_sixtyNineBO_176467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2515713553) ^ 1257856776 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 2515713553) ^ 838571184 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 2515713553) ^ 228701232 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 2515713553) ^ 14256 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_2558951957 : Nat.Prime 2558951957 := by
  apply lucas_primality 2558951957 (2 : ZMod 2558951957)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (97, 1), (127, 1), (4721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (97, 1), (127, 1), (4721, 1)] : List FactorBlock).map factorBlockValue).prod) = 2558951957 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_11
      · exact prime_sixtyNineBO_97
      · exact prime_sixtyNineBO_127
      · exact prime_sixtyNineBO_4721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2558951957) ^ 1279475978 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2558951957) ^ 232631996 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2558951957) ^ 26380948 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2558951957) ^ 20149228 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2558951957) ^ 542036 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_2683216183 : Nat.Prime 2683216183 := by
  apply lucas_primality 2683216183 (3 : ZMod 2683216183)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (47, 1), (559703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (47, 1), (559703, 1)] : List FactorBlock).map factorBlockValue).prod) = 2683216183 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_17
      · exact prime_sixtyNineBO_47
      · exact prime_sixtyNineBO_559703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2683216183) ^ 1341608091 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 2683216183) ^ 894405394 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 2683216183) ^ 157836246 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 2683216183) ^ 57089706 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 2683216183) ^ 4794 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_2749565311 : Nat.Prime 2749565311 := by
  apply lucas_primality 2749565311 (3 : ZMod 2749565311)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (91652177, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (91652177, 1)] : List FactorBlock).map factorBlockValue).prod) = 2749565311 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_5
      · exact prime_sixtyNineBO_91652177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2749565311) ^ 1374782655 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 2749565311) ^ 916521770 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 2749565311) ^ 549913062 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 2749565311) ^ 30 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_2808783641 : Nat.Prime 2808783641 := by
  apply lucas_primality 2808783641 (7 : ZMod 2808783641)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (13, 1), (5401507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (13, 1), (5401507, 1)] : List FactorBlock).map factorBlockValue).prod) = 2808783641 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_5
      · exact prime_sixtyNineBO_13
      · exact prime_sixtyNineBO_5401507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 2808783641) ^ 1404391820 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (7 : ZMod 2808783641) ^ 561756728 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (7 : ZMod 2808783641) ^ 216060280 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (7 : ZMod 2808783641) ^ 520 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_3005416559 : Nat.Prime 3005416559 := by
  apply lucas_primality 3005416559 (13 : ZMod 3005416559)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (271, 1), (5545049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (271, 1), (5545049, 1)] : List FactorBlock).map factorBlockValue).prod) = 3005416559 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_271
      · exact prime_sixtyNineBO_5545049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 3005416559) ^ 1502708279 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (13 : ZMod 3005416559) ^ 11090098 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (13 : ZMod 3005416559) ^ 542 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_3296500253 : Nat.Prime 3296500253 := by
  apply lucas_primality 3296500253 (2 : ZMod 3296500253)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (824125063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (824125063, 1)] : List FactorBlock).map factorBlockValue).prod) = 3296500253 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_824125063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 3296500253) ^ 1648250126 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 3296500253) ^ 4 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_3978723019 : Nat.Prime 3978723019 := by
  apply lucas_primality 3978723019 (13 : ZMod 3978723019)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1163, 1), (570181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1163, 1), (570181, 1)] : List FactorBlock).map factorBlockValue).prod) = 3978723019 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_1163
      · exact prime_sixtyNineBO_570181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 3978723019) ^ 1989361509 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (13 : ZMod 3978723019) ^ 1326241006 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (13 : ZMod 3978723019) ^ 3421086 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (13 : ZMod 3978723019) ^ 6978 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_4082184427 : Nat.Prime 4082184427 := by
  apply lucas_primality 4082184427 (3 : ZMod 4082184427)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (680364071, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (680364071, 1)] : List FactorBlock).map factorBlockValue).prod) = 4082184427 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_680364071
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 4082184427) ^ 2041092213 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 4082184427) ^ 1360728142 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 4082184427) ^ 6 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_4433153639 : Nat.Prime 4433153639 := by
  apply lucas_primality 4433153639 (13 : ZMod 4433153639)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (617, 1), (1163, 1), (3089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (617, 1), (1163, 1), (3089, 1)] : List FactorBlock).map factorBlockValue).prod) = 4433153639 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_617
      · exact prime_sixtyNineBO_1163
      · exact prime_sixtyNineBO_3089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 4433153639) ^ 2216576819 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (13 : ZMod 4433153639) ^ 7185014 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (13 : ZMod 4433153639) ^ 3811826 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (13 : ZMod 4433153639) ^ 1435142 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_4729177771 : Nat.Prime 4729177771 := by
  apply lucas_primality 4729177771 (3 : ZMod 4729177771)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (97, 1), (1625147, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (97, 1), (1625147, 1)] : List FactorBlock).map factorBlockValue).prod) = 4729177771 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_5
      · exact prime_sixtyNineBO_97
      · exact prime_sixtyNineBO_1625147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4729177771) ^ 2364588885 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 4729177771) ^ 1576392590 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 4729177771) ^ 945835554 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 4729177771) ^ 48754410 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 4729177771) ^ 2910 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_5155515973 : Nat.Prime 5155515973 := by
  apply lucas_primality 5155515973 (2 : ZMod 5155515973)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (41, 1), (653, 1), (1783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (41, 1), (653, 1), (1783, 1)] : List FactorBlock).map factorBlockValue).prod) = 5155515973 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_41
      · exact prime_sixtyNineBO_653
      · exact prime_sixtyNineBO_1783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5155515973) ^ 2577757986 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 5155515973) ^ 1718505324 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 5155515973) ^ 125744292 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 5155515973) ^ 7895124 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 5155515973) ^ 2891484 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_5950292347 : Nat.Prime 5950292347 := by
  apply lucas_primality 5950292347 (3 : ZMod 5950292347)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (110190599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (110190599, 1)] : List FactorBlock).map factorBlockValue).prod) = 5950292347 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_110190599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 5950292347) ^ 2975146173 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 5950292347) ^ 1983430782 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 5950292347) ^ 54 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_6313009589 : Nat.Prime 6313009589 := by
  apply lucas_primality 6313009589 (2 : ZMod 6313009589)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (71, 1), (89, 1), (249763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (71, 1), (89, 1), (249763, 1)] : List FactorBlock).map factorBlockValue).prod) = 6313009589 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_71
      · exact prime_sixtyNineBO_89
      · exact prime_sixtyNineBO_249763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 6313009589) ^ 3156504794 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 6313009589) ^ 88915628 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 6313009589) ^ 70932692 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 6313009589) ^ 25276 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_7036057619 : Nat.Prime 7036057619 := by
  apply lucas_primality 7036057619 (2 : ZMod 7036057619)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (191, 1), (969421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (191, 1), (969421, 1)] : List FactorBlock).map factorBlockValue).prod) = 7036057619 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_19
      · exact prime_sixtyNineBO_191
      · exact prime_sixtyNineBO_969421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7036057619) ^ 3518028809 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 7036057619) ^ 370318822 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 7036057619) ^ 36837998 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 7036057619) ^ 7258 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_7162225153 : Nat.Prime 7162225153 := by
  apply lucas_primality 7162225153 (7 : ZMod 7162225153)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 9), (3, 1), (1021, 1), (4567, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 9), (3, 1), (1021, 1), (4567, 1)] : List FactorBlock).map factorBlockValue).prod) = 7162225153 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_1021
      · exact prime_sixtyNineBO_4567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 7162225153) ^ 3581112576 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (7 : ZMod 7162225153) ^ 2387408384 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (7 : ZMod 7162225153) ^ 7014912 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (7 : ZMod 7162225153) ^ 1568256 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_7448470817 : Nat.Prime 7448470817 := by
  apply lucas_primality 7448470817 (3 : ZMod 7448470817)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (232764713, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (232764713, 1)] : List FactorBlock).map factorBlockValue).prod) = 7448470817 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_232764713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 7448470817) ^ 3724235408 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 7448470817) ^ 32 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_8506776979 : Nat.Prime 8506776979 := by
  apply lucas_primality 8506776979 (2 : ZMod 8506776979)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (7, 1), (53, 1), (141539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (7, 1), (53, 1), (141539, 1)] : List FactorBlock).map factorBlockValue).prod) = 8506776979 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_7
      · exact prime_sixtyNineBO_53
      · exact prime_sixtyNineBO_141539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 8506776979) ^ 4253388489 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 8506776979) ^ 2835592326 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 8506776979) ^ 1215253854 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 8506776979) ^ 160505226 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 8506776979) ^ 60102 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_9340763317 : Nat.Prime 9340763317 := by
  apply lucas_primality 9340763317 (6 : ZMod 9340763317)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (778396943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (778396943, 1)] : List FactorBlock).map factorBlockValue).prod) = 9340763317 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_778396943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 9340763317) ^ 4670381658 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (6 : ZMod 9340763317) ^ 3113587772 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (6 : ZMod 9340763317) ^ 12 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_9593050183 : Nat.Prime 9593050183 := by
  apply lucas_primality 9593050183 (3 : ZMod 9593050183)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (5849, 1), (14387, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (5849, 1), (14387, 1)] : List FactorBlock).map factorBlockValue).prod) = 9593050183 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_19
      · exact prime_sixtyNineBO_5849
      · exact prime_sixtyNineBO_14387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 9593050183) ^ 4796525091 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 9593050183) ^ 3197683394 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 9593050183) ^ 504897378 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 9593050183) ^ 1640118 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 9593050183) ^ 666786 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_9694381309 : Nat.Prime 9694381309 := by
  apply lucas_primality 9694381309 (6 : ZMod 9694381309)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 2), (2795381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 2), (2795381, 1)] : List FactorBlock).map factorBlockValue).prod) = 9694381309 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_17
      · exact prime_sixtyNineBO_2795381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 9694381309) ^ 4847190654 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (6 : ZMod 9694381309) ^ 3231460436 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (6 : ZMod 9694381309) ^ 570257724 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (6 : ZMod 9694381309) ^ 3468 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_10266744251 : Nat.Prime 10266744251 := by
  apply lucas_primality 10266744251 (2 : ZMod 10266744251)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 3), (7, 1), (5866711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 3), (7, 1), (5866711, 1)] : List FactorBlock).map factorBlockValue).prod) = 10266744251 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_5
      · exact prime_sixtyNineBO_7
      · exact prime_sixtyNineBO_5866711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 10266744251) ^ 5133372125 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 10266744251) ^ 2053348850 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 10266744251) ^ 1466677750 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 10266744251) ^ 1750 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_12021788057 : Nat.Prime 12021788057 := by
  apply lucas_primality 12021788057 (3 : ZMod 12021788057)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (29741, 1), (50527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (29741, 1), (50527, 1)] : List FactorBlock).map factorBlockValue).prod) = 12021788057 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_29741
      · exact prime_sixtyNineBO_50527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 12021788057) ^ 6010894028 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 12021788057) ^ 404216 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 12021788057) ^ 237928 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_12417299849 : Nat.Prime 12417299849 := by
  apply lucas_primality 12417299849 (3 : ZMod 12417299849)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3911, 1), (396871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3911, 1), (396871, 1)] : List FactorBlock).map factorBlockValue).prod) = 12417299849 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3911
      · exact prime_sixtyNineBO_396871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 12417299849) ^ 6208649924 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 12417299849) ^ 3174968 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 12417299849) ^ 31288 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_14462188693 : Nat.Prime 14462188693 := by
  apply lucas_primality 14462188693 (5 : ZMod 14462188693)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 2), (163, 1), (150893, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 2), (163, 1), (150893, 1)] : List FactorBlock).map factorBlockValue).prod) = 14462188693 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_7
      · exact prime_sixtyNineBO_163
      · exact prime_sixtyNineBO_150893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 14462188693) ^ 7231094346 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 14462188693) ^ 4820729564 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 14462188693) ^ 2066026956 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 14462188693) ^ 88725084 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 14462188693) ^ 95844 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_17956392383 : Nat.Prime 17956392383 := by
  apply lucas_primality 17956392383 (5 : ZMod 17956392383)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (157, 1), (1483, 1), (38561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (157, 1), (1483, 1), (38561, 1)] : List FactorBlock).map factorBlockValue).prod) = 17956392383 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_157
      · exact prime_sixtyNineBO_1483
      · exact prime_sixtyNineBO_38561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 17956392383) ^ 8978196191 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 17956392383) ^ 114371926 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 17956392383) ^ 12108154 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 17956392383) ^ 465662 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_19706661917 : Nat.Prime 19706661917 := by
  apply lucas_primality 19706661917 (2 : ZMod 19706661917)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3499, 1), (1408021, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3499, 1), (1408021, 1)] : List FactorBlock).map factorBlockValue).prod) = 19706661917 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3499
      · exact prime_sixtyNineBO_1408021
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 19706661917) ^ 9853330958 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 19706661917) ^ 5632084 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 19706661917) ^ 13996 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_19951883069 : Nat.Prime 19951883069 := by
  apply lucas_primality 19951883069 (2 : ZMod 19951883069)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (367, 1), (523, 1), (1999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (367, 1), (523, 1), (1999, 1)] : List FactorBlock).map factorBlockValue).prod) = 19951883069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_13
      · exact prime_sixtyNineBO_367
      · exact prime_sixtyNineBO_523
      · exact prime_sixtyNineBO_1999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 19951883069) ^ 9975941534 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 19951883069) ^ 1534760236 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 19951883069) ^ 54364804 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 19951883069) ^ 38148916 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 19951883069) ^ 9980932 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_19952708161 : Nat.Prime 19952708161 := by
  apply lucas_primality 19952708161 (17 : ZMod 19952708161)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (5, 1), (7, 1), (11, 1), (269923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (5, 1), (7, 1), (11, 1), (269923, 1)] : List FactorBlock).map factorBlockValue).prod) = 19952708161 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_5
      · exact prime_sixtyNineBO_7
      · exact prime_sixtyNineBO_11
      · exact prime_sixtyNineBO_269923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 19952708161) ^ 9976354080 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (17 : ZMod 19952708161) ^ 6650902720 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (17 : ZMod 19952708161) ^ 3990541632 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (17 : ZMod 19952708161) ^ 2850386880 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (17 : ZMod 19952708161) ^ 1813882560 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (17 : ZMod 19952708161) ^ 73920 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_20868118367 : Nat.Prime 20868118367 := by
  apply lucas_primality 20868118367 (5 : ZMod 20868118367)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (443, 1), (23553181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (443, 1), (23553181, 1)] : List FactorBlock).map factorBlockValue).prod) = 20868118367 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_443
      · exact prime_sixtyNineBO_23553181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 20868118367) ^ 10434059183 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 20868118367) ^ 47106362 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 20868118367) ^ 886 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_26069428837 : Nat.Prime 26069428837 := by
  apply lucas_primality 26069428837 (5 : ZMod 26069428837)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (11, 1), (65831891, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (11, 1), (65831891, 1)] : List FactorBlock).map factorBlockValue).prod) = 26069428837 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_11
      · exact prime_sixtyNineBO_65831891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 26069428837) ^ 13034714418 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 26069428837) ^ 8689809612 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 26069428837) ^ 2369948076 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 26069428837) ^ 396 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_28565507207 : Nat.Prime 28565507207 := by
  apply lucas_primality 28565507207 (5 : ZMod 28565507207)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (331, 1), (43150313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (331, 1), (43150313, 1)] : List FactorBlock).map factorBlockValue).prod) = 28565507207 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_331
      · exact prime_sixtyNineBO_43150313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 28565507207) ^ 14282753603 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 28565507207) ^ 86300626 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 28565507207) ^ 662 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_30041397797 : Nat.Prime 30041397797 := by
  apply lucas_primality 30041397797 (2 : ZMod 30041397797)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (139, 1), (54031291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (139, 1), (54031291, 1)] : List FactorBlock).map factorBlockValue).prod) = 30041397797 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_139
      · exact prime_sixtyNineBO_54031291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 30041397797) ^ 15020698898 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 30041397797) ^ 216125164 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 30041397797) ^ 556 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_31056779657 : Nat.Prime 31056779657 := by
  apply lucas_primality 31056779657 (3 : ZMod 31056779657)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (109, 1), (5087939, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (109, 1), (5087939, 1)] : List FactorBlock).map factorBlockValue).prod) = 31056779657 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_7
      · exact prime_sixtyNineBO_109
      · exact prime_sixtyNineBO_5087939
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 31056779657) ^ 15528389828 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 31056779657) ^ 4436682808 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 31056779657) ^ 284924584 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 31056779657) ^ 6104 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_32296256431 : Nat.Prime 32296256431 := by
  apply lucas_primality 32296256431 (6 : ZMod 32296256431)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (17, 1), (19, 1), (1451, 1), (2297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (17, 1), (19, 1), (1451, 1), (2297, 1)] : List FactorBlock).map factorBlockValue).prod) = 32296256431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_5
      · exact prime_sixtyNineBO_17
      · exact prime_sixtyNineBO_19
      · exact prime_sixtyNineBO_1451
      · exact prime_sixtyNineBO_2297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 32296256431) ^ 16148128215 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (6 : ZMod 32296256431) ^ 10765418810 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (6 : ZMod 32296256431) ^ 6459251286 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (6 : ZMod 32296256431) ^ 1899779790 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (6 : ZMod 32296256431) ^ 1699802970 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (6 : ZMod 32296256431) ^ 22257930 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (6 : ZMod 32296256431) ^ 14060190 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_35581064731 : Nat.Prime 35581064731 := by
  apply lucas_primality 35581064731 (2 : ZMod 35581064731)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (251, 1), (4725241, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (251, 1), (4725241, 1)] : List FactorBlock).map factorBlockValue).prod) = 35581064731 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_5
      · exact prime_sixtyNineBO_251
      · exact prime_sixtyNineBO_4725241
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 35581064731) ^ 17790532365 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 35581064731) ^ 11860354910 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 35581064731) ^ 7116212946 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 35581064731) ^ 141757230 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 35581064731) ^ 7530 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_36994320929 : Nat.Prime 36994320929 := by
  apply lucas_primality 36994320929 (6 : ZMod 36994320929)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (23, 1), (353, 1), (142391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (23, 1), (353, 1), (142391, 1)] : List FactorBlock).map factorBlockValue).prod) = 36994320929 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_23
      · exact prime_sixtyNineBO_353
      · exact prime_sixtyNineBO_142391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 36994320929) ^ 18497160464 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (6 : ZMod 36994320929) ^ 1608448736 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (6 : ZMod 36994320929) ^ 104799776 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (6 : ZMod 36994320929) ^ 259808 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_37030690603 : Nat.Prime 37030690603 := by
  apply lucas_primality 37030690603 (3 : ZMod 37030690603)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (967, 1), (2127467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (967, 1), (2127467, 1)] : List FactorBlock).map factorBlockValue).prod) = 37030690603 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_967
      · exact prime_sixtyNineBO_2127467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 37030690603) ^ 18515345301 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 37030690603) ^ 12343563534 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 37030690603) ^ 38294406 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 37030690603) ^ 17406 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_37179326159 : Nat.Prime 37179326159 := by
  apply lucas_primality 37179326159 (17 : ZMod 37179326159)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (4007, 1), (356869, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (4007, 1), (356869, 1)] : List FactorBlock).map factorBlockValue).prod) = 37179326159 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_13
      · exact prime_sixtyNineBO_4007
      · exact prime_sixtyNineBO_356869
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 37179326159) ^ 18589663079 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (17 : ZMod 37179326159) ^ 2859948166 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (17 : ZMod 37179326159) ^ 9278594 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (17 : ZMod 37179326159) ^ 104182 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_42647584043 : Nat.Prime 42647584043 := by
  apply lucas_primality 42647584043 (2 : ZMod 42647584043)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (61, 1), (103, 1), (69263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (61, 1), (103, 1), (69263, 1)] : List FactorBlock).map factorBlockValue).prod) = 42647584043 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_7
      · exact prime_sixtyNineBO_61
      · exact prime_sixtyNineBO_103
      · exact prime_sixtyNineBO_69263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 42647584043) ^ 21323792021 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 42647584043) ^ 6092512006 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 42647584043) ^ 699140722 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 42647584043) ^ 414054214 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 42647584043) ^ 615734 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_50963027279 : Nat.Prime 50963027279 := by
  apply lucas_primality 50963027279 (26 : ZMod 50963027279)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (1498912567, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (1498912567, 1)] : List FactorBlock).map factorBlockValue).prod) = 50963027279 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_17
      · exact prime_sixtyNineBO_1498912567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (26 : ZMod 50963027279) ^ 25481513639 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (26 : ZMod 50963027279) ^ 2997825134 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (26 : ZMod 50963027279) ^ 34 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_69831659341 : Nat.Prime 69831659341 := by
  apply lucas_primality 69831659341 (13 : ZMod 69831659341)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (283, 1), (1370861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (283, 1), (1370861, 1)] : List FactorBlock).map factorBlockValue).prod) = 69831659341 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_5
      · exact prime_sixtyNineBO_283
      · exact prime_sixtyNineBO_1370861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 69831659341) ^ 34915829670 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (13 : ZMod 69831659341) ^ 23277219780 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (13 : ZMod 69831659341) ^ 13966331868 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (13 : ZMod 69831659341) ^ 246754980 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (13 : ZMod 69831659341) ^ 50940 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_77435126401 : Nat.Prime 77435126401 := by
  apply lucas_primality 77435126401 (7 : ZMod 77435126401)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (5, 2), (89, 1), (90631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (5, 2), (89, 1), (90631, 1)] : List FactorBlock).map factorBlockValue).prod) = 77435126401 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_5
      · exact prime_sixtyNineBO_89
      · exact prime_sixtyNineBO_90631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 77435126401) ^ 38717563200 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (7 : ZMod 77435126401) ^ 25811708800 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (7 : ZMod 77435126401) ^ 15487025280 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (7 : ZMod 77435126401) ^ 870057600 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (7 : ZMod 77435126401) ^ 854400 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_77477447197 : Nat.Prime 77477447197 := by
  apply lucas_primality 77477447197 (5 : ZMod 77477447197)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (479, 1), (4493009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (479, 1), (4493009, 1)] : List FactorBlock).map factorBlockValue).prod) = 77477447197 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_479
      · exact prime_sixtyNineBO_4493009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 77477447197) ^ 38738723598 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 77477447197) ^ 25825815732 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 77477447197) ^ 161748324 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 77477447197) ^ 17244 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_89484204889 : Nat.Prime 89484204889 := by
  apply lucas_primality 89484204889 (19 : ZMod 89484204889)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (13, 1), (37, 1), (2583859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (13, 1), (37, 1), (2583859, 1)] : List FactorBlock).map factorBlockValue).prod) = 89484204889 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_13
      · exact prime_sixtyNineBO_37
      · exact prime_sixtyNineBO_2583859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 89484204889) ^ 44742102444 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (19 : ZMod 89484204889) ^ 29828068296 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (19 : ZMod 89484204889) ^ 6883400376 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (19 : ZMod 89484204889) ^ 2418492024 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (19 : ZMod 89484204889) ^ 34632 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_112738582699 : Nat.Prime 112738582699 := by
  apply lucas_primality 112738582699 (3 : ZMod 112738582699)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (107, 1), (3583781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (107, 1), (3583781, 1)] : List FactorBlock).map factorBlockValue).prod) = 112738582699 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_7
      · exact prime_sixtyNineBO_107
      · exact prime_sixtyNineBO_3583781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 112738582699) ^ 56369291349 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 112738582699) ^ 37579527566 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 112738582699) ^ 16105511814 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 112738582699) ^ 1053631614 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 112738582699) ^ 31458 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_114595602449 : Nat.Prime 114595602449 := by
  apply lucas_primality 114595602449 (3 : ZMod 114595602449)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7162225153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7162225153, 1)] : List FactorBlock).map factorBlockValue).prod) = 114595602449 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_7162225153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 114595602449) ^ 57297801224 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 114595602449) ^ 16 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_123874614427 : Nat.Prime 123874614427 := by
  apply lucas_primality 123874614427 (3 : ZMod 123874614427)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (79, 1), (2251, 1), (116099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (79, 1), (2251, 1), (116099, 1)] : List FactorBlock).map factorBlockValue).prod) = 123874614427 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_79
      · exact prime_sixtyNineBO_2251
      · exact prime_sixtyNineBO_116099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 123874614427) ^ 61937307213 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 123874614427) ^ 41291538142 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 123874614427) ^ 1568033094 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 123874614427) ^ 55030926 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 123874614427) ^ 1066974 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_144621886931 : Nat.Prime 144621886931 := by
  apply lucas_primality 144621886931 (2 : ZMod 144621886931)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (14462188693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (14462188693, 1)] : List FactorBlock).map factorBlockValue).prod) = 144621886931 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_5
      · exact prime_sixtyNineBO_14462188693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 144621886931) ^ 72310943465 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 144621886931) ^ 28924377386 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 144621886931) ^ 10 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_166944946937 : Nat.Prime 166944946937 := by
  apply lucas_primality 166944946937 (3 : ZMod 166944946937)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (20868118367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (20868118367, 1)] : List FactorBlock).map factorBlockValue).prod) = 166944946937 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_20868118367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 166944946937) ^ 83472473468 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 166944946937) ^ 8 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_184801396519 : Nat.Prime 184801396519 := by
  apply lucas_primality 184801396519 (3 : ZMod 184801396519)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (10266744251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (10266744251, 1)] : List FactorBlock).map factorBlockValue).prod) = 184801396519 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_10266744251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 184801396519) ^ 92400698259 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 184801396519) ^ 61600465506 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 184801396519) ^ 18 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_186865592489 : Nat.Prime 186865592489 := by
  apply lucas_primality 186865592489 (3 : ZMod 186865592489)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (53, 1), (59, 1), (7469843, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (53, 1), (59, 1), (7469843, 1)] : List FactorBlock).map factorBlockValue).prod) = 186865592489 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_53
      · exact prime_sixtyNineBO_59
      · exact prime_sixtyNineBO_7469843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 186865592489) ^ 93432796244 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 186865592489) ^ 3525765896 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 186865592489) ^ 3167213432 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 186865592489) ^ 25016 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_191307829759 : Nat.Prime 191307829759 := by
  apply lucas_primality 191307829759 (3 : ZMod 191307829759)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (139, 1), (229385887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (139, 1), (229385887, 1)] : List FactorBlock).map factorBlockValue).prod) = 191307829759 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_139
      · exact prime_sixtyNineBO_229385887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 191307829759) ^ 95653914879 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 191307829759) ^ 63769276586 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 191307829759) ^ 1376315322 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 191307829759) ^ 834 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_208842910051 : Nat.Prime 208842910051 := by
  apply lucas_primality 208842910051 (2 : ZMod 208842910051)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (1392286067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (1392286067, 1)] : List FactorBlock).map factorBlockValue).prod) = 208842910051 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_5
      · exact prime_sixtyNineBO_1392286067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 208842910051) ^ 104421455025 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 208842910051) ^ 69614303350 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 208842910051) ^ 41768582010 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 208842910051) ^ 150 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_259870473077 : Nat.Prime 259870473077 := by
  apply lucas_primality 259870473077 (2 : ZMod 259870473077)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (48311, 1), (1344779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (48311, 1), (1344779, 1)] : List FactorBlock).map factorBlockValue).prod) = 259870473077 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_48311
      · exact prime_sixtyNineBO_1344779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 259870473077) ^ 129935236538 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 259870473077) ^ 5379116 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 259870473077) ^ 193244 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_280222899511 : Nat.Prime 280222899511 := by
  apply lucas_primality 280222899511 (6 : ZMod 280222899511)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (9340763317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (9340763317, 1)] : List FactorBlock).map factorBlockValue).prod) = 280222899511 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_5
      · exact prime_sixtyNineBO_9340763317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 280222899511) ^ 140111449755 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (6 : ZMod 280222899511) ^ 93407633170 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (6 : ZMod 280222899511) ^ 56044579902 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (6 : ZMod 280222899511) ^ 30 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_310272609401 : Nat.Prime 310272609401 := by
  apply lucas_primality 310272609401 (3 : ZMod 310272609401)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (13, 2), (37, 1), (248099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (13, 2), (37, 1), (248099, 1)] : List FactorBlock).map factorBlockValue).prod) = 310272609401 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_5
      · exact prime_sixtyNineBO_13
      · exact prime_sixtyNineBO_37
      · exact prime_sixtyNineBO_248099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 310272609401) ^ 155136304700 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 310272609401) ^ 62054521880 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 310272609401) ^ 23867123800 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 310272609401) ^ 8385746200 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 310272609401) ^ 1250600 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_335153033323 : Nat.Prime 335153033323 := by
  apply lucas_primality 335153033323 (2 : ZMod 335153033323)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (137, 1), (4139, 1), (4283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (137, 1), (4139, 1), (4283, 1)] : List FactorBlock).map factorBlockValue).prod) = 335153033323 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_23
      · exact prime_sixtyNineBO_137
      · exact prime_sixtyNineBO_4139
      · exact prime_sixtyNineBO_4283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 335153033323) ^ 167576516661 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 335153033323) ^ 111717677774 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 335153033323) ^ 14571871014 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 335153033323) ^ 2446372506 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 335153033323) ^ 80974398 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 335153033323) ^ 78251934 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_360337639471 : Nat.Prime 360337639471 := by
  apply lucas_primality 360337639471 (6 : ZMod 360337639471)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (23, 1), (522228463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (23, 1), (522228463, 1)] : List FactorBlock).map factorBlockValue).prod) = 360337639471 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_5
      · exact prime_sixtyNineBO_23
      · exact prime_sixtyNineBO_522228463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 360337639471) ^ 180168819735 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (6 : ZMod 360337639471) ^ 120112546490 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (6 : ZMod 360337639471) ^ 72067527894 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (6 : ZMod 360337639471) ^ 15666853890 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (6 : ZMod 360337639471) ^ 690 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_411912711527 : Nat.Prime 411912711527 := by
  apply lucas_primality 411912711527 (5 : ZMod 411912711527)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1531, 1), (1913, 1), (70321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1531, 1), (1913, 1), (70321, 1)] : List FactorBlock).map factorBlockValue).prod) = 411912711527 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_1531
      · exact prime_sixtyNineBO_1913
      · exact prime_sixtyNineBO_70321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 411912711527) ^ 205956355763 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 411912711527) ^ 269048146 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 411912711527) ^ 215322902 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 411912711527) ^ 5857606 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_417012511249 : Nat.Prime 417012511249 := by
  apply lucas_primality 417012511249 (14 : ZMod 417012511249)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 4), (321768913, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 4), (321768913, 1)] : List FactorBlock).map factorBlockValue).prod) = 417012511249 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_321768913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (14 : ZMod 417012511249) ^ 208506255624 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (14 : ZMod 417012511249) ^ 139004170416 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (14 : ZMod 417012511249) ^ 1296 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_428910115519 : Nat.Prime 428910115519 := by
  apply lucas_primality 428910115519 (6 : ZMod 428910115519)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (31, 1), (449, 1), (570643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (31, 1), (449, 1), (570643, 1)] : List FactorBlock).map factorBlockValue).prod) = 428910115519 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_31
      · exact prime_sixtyNineBO_449
      · exact prime_sixtyNineBO_570643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 428910115519) ^ 214455057759 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (6 : ZMod 428910115519) ^ 142970038506 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (6 : ZMod 428910115519) ^ 13835810178 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (6 : ZMod 428910115519) ^ 955256382 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (6 : ZMod 428910115519) ^ 751626 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_464864683183 : Nat.Prime 464864683183 := by
  apply lucas_primality 464864683183 (3 : ZMod 464864683183)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (77477447197, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (77477447197, 1)] : List FactorBlock).map factorBlockValue).prod) = 464864683183 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_77477447197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 464864683183) ^ 232432341591 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 464864683183) ^ 154954894394 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 464864683183) ^ 6 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_535526311231 : Nat.Prime 535526311231 := by
  apply lucas_primality 535526311231 (14 : ZMod 535526311231)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (5950292347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (5950292347, 1)] : List FactorBlock).map factorBlockValue).prod) = 535526311231 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_5
      · exact prime_sixtyNineBO_5950292347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 535526311231) ^ 267763155615 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (14 : ZMod 535526311231) ^ 178508770410 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (14 : ZMod 535526311231) ^ 107105262246 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (14 : ZMod 535526311231) ^ 90 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_535709774861 : Nat.Prime 535709774861 := by
  apply lucas_primality 535709774861 (2 : ZMod 535709774861)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (13, 1), (307, 1), (6711473, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (13, 1), (307, 1), (6711473, 1)] : List FactorBlock).map factorBlockValue).prod) = 535709774861 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_5
      · exact prime_sixtyNineBO_13
      · exact prime_sixtyNineBO_307
      · exact prime_sixtyNineBO_6711473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 535709774861) ^ 267854887430 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 535709774861) ^ 107141954972 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 535709774861) ^ 41208444220 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 535709774861) ^ 1744982980 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 535709774861) ^ 79820 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_567427816933 : Nat.Prime 567427816933 := by
  apply lucas_primality 567427816933 (2 : ZMod 567427816933)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (41, 1), (7649, 1), (150779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (41, 1), (7649, 1), (150779, 1)] : List FactorBlock).map factorBlockValue).prod) = 567427816933 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_41
      · exact prime_sixtyNineBO_7649
      · exact prime_sixtyNineBO_150779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 567427816933) ^ 283713908466 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 567427816933) ^ 189142605644 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 567427816933) ^ 13839702852 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 567427816933) ^ 74183268 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 567427816933) ^ 3763308 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_595391918411 : Nat.Prime 595391918411 := by
  apply lucas_primality 595391918411 (2 : ZMod 595391918411)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (523, 1), (113841667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (523, 1), (113841667, 1)] : List FactorBlock).map factorBlockValue).prod) = 595391918411 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_5
      · exact prime_sixtyNineBO_523
      · exact prime_sixtyNineBO_113841667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 595391918411) ^ 297695959205 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 595391918411) ^ 119078383682 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 595391918411) ^ 1138416670 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 595391918411) ^ 5230 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_620545218803 : Nat.Prime 620545218803 := by
  apply lucas_primality 620545218803 (2 : ZMod 620545218803)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (310272609401, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (310272609401, 1)] : List FactorBlock).map factorBlockValue).prod) = 620545218803 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_310272609401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 620545218803) ^ 310272609401 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 620545218803) ^ 2 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_681168443591 : Nat.Prime 681168443591 := by
  apply lucas_primality 681168443591 (11 : ZMod 681168443591)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (257, 1), (14011, 1), (18917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (257, 1), (14011, 1), (18917, 1)] : List FactorBlock).map factorBlockValue).prod) = 681168443591 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_5
      · exact prime_sixtyNineBO_257
      · exact prime_sixtyNineBO_14011
      · exact prime_sixtyNineBO_18917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 681168443591) ^ 340584221795 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (11 : ZMod 681168443591) ^ 136233688718 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (11 : ZMod 681168443591) ^ 2650460870 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (11 : ZMod 681168443591) ^ 48616690 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (11 : ZMod 681168443591) ^ 36008270 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_705469795159 : Nat.Prime 705469795159 := by
  apply lucas_primality 705469795159 (3 : ZMod 705469795159)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (43, 1), (71, 1), (38512381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (43, 1), (71, 1), (38512381, 1)] : List FactorBlock).map factorBlockValue).prod) = 705469795159 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_43
      · exact prime_sixtyNineBO_71
      · exact prime_sixtyNineBO_38512381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 705469795159) ^ 352734897579 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 705469795159) ^ 235156598386 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 705469795159) ^ 16406274306 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 705469795159) ^ 9936194298 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 705469795159) ^ 18318 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_762083263147 : Nat.Prime 762083263147 := by
  apply lucas_primality 762083263147 (5 : ZMod 762083263147)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (83, 1), (1530287677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (83, 1), (1530287677, 1)] : List FactorBlock).map factorBlockValue).prod) = 762083263147 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_83
      · exact prime_sixtyNineBO_1530287677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 762083263147) ^ 381041631573 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 762083263147) ^ 254027754382 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 762083263147) ^ 9181726062 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 762083263147) ^ 498 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_1650981814817 : Nat.Prime 1650981814817 := by
  apply lucas_primality 1650981814817 (3 : ZMod 1650981814817)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (59, 1), (523, 1), (1672009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (59, 1), (523, 1), (1672009, 1)] : List FactorBlock).map factorBlockValue).prod) = 1650981814817 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_59
      · exact prime_sixtyNineBO_523
      · exact prime_sixtyNineBO_1672009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1650981814817) ^ 825490907408 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1650981814817) ^ 27982742624 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1650981814817) ^ 3156752992 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1650981814817) ^ 987424 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_1724718660611 : Nat.Prime 1724718660611 := by
  apply lucas_primality 1724718660611 (2 : ZMod 1724718660611)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (809, 1), (19381039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (809, 1), (19381039, 1)] : List FactorBlock).map factorBlockValue).prod) = 1724718660611 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_5
      · exact prime_sixtyNineBO_11
      · exact prime_sixtyNineBO_809
      · exact prime_sixtyNineBO_19381039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1724718660611) ^ 862359330305 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1724718660611) ^ 344943732122 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1724718660611) ^ 156792605510 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1724718660611) ^ 2131914290 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1724718660611) ^ 88990 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_2236791311701 : Nat.Prime 2236791311701 := by
  apply lucas_primality 2236791311701 (14 : ZMod 2236791311701)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (11, 1), (677815549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (11, 1), (677815549, 1)] : List FactorBlock).map factorBlockValue).prod) = 2236791311701 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_5
      · exact prime_sixtyNineBO_11
      · exact prime_sixtyNineBO_677815549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 2236791311701) ^ 1118395655850 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (14 : ZMod 2236791311701) ^ 745597103900 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (14 : ZMod 2236791311701) ^ 447358262340 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (14 : ZMod 2236791311701) ^ 203344664700 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (14 : ZMod 2236791311701) ^ 3300 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_3310719202057 : Nat.Prime 3310719202057 := by
  apply lucas_primality 3310719202057 (5 : ZMod 3310719202057)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (19706661917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (19706661917, 1)] : List FactorBlock).map factorBlockValue).prod) = 3310719202057 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_7
      · exact prime_sixtyNineBO_19706661917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 3310719202057) ^ 1655359601028 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 3310719202057) ^ 1103573067352 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 3310719202057) ^ 472959886008 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 3310719202057) ^ 168 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_3378330571283 : Nat.Prime 3378330571283 := by
  apply lucas_primality 3378330571283 (2 : ZMod 3378330571283)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13217, 1), (127802473, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13217, 1), (127802473, 1)] : List FactorBlock).map factorBlockValue).prod) = 3378330571283 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_13217
      · exact prime_sixtyNineBO_127802473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3378330571283) ^ 1689165285641 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 3378330571283) ^ 255604946 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 3378330571283) ^ 26434 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_3688728073799 : Nat.Prime 3688728073799 := by
  apply lucas_primality 3688728073799 (13 : ZMod 3688728073799)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1019, 1), (1809974521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1019, 1), (1809974521, 1)] : List FactorBlock).map factorBlockValue).prod) = 3688728073799 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_1019
      · exact prime_sixtyNineBO_1809974521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 3688728073799) ^ 1844364036899 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (13 : ZMod 3688728073799) ^ 3619949042 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (13 : ZMod 3688728073799) ^ 2038 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_4981101266261 : Nat.Prime 4981101266261 := by
  apply lucas_primality 4981101266261 (3 : ZMod 4981101266261)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (19, 1), (449, 1), (1759, 1), (2371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (19, 1), (449, 1), (1759, 1), (2371, 1)] : List FactorBlock).map factorBlockValue).prod) = 4981101266261 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_5
      · exact prime_sixtyNineBO_7
      · exact prime_sixtyNineBO_19
      · exact prime_sixtyNineBO_449
      · exact prime_sixtyNineBO_1759
      · exact prime_sixtyNineBO_2371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4981101266261) ^ 2490550633130 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 4981101266261) ^ 996220253252 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 4981101266261) ^ 711585895180 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 4981101266261) ^ 262163224540 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 4981101266261) ^ 11093766740 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 4981101266261) ^ 2831780140 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 4981101266261) ^ 2100844060 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_5795615632589 : Nat.Prime 5795615632589 := by
  apply lucas_primality 5795615632589 (2 : ZMod 5795615632589)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (149, 1), (14249, 1), (682447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (149, 1), (14249, 1), (682447, 1)] : List FactorBlock).map factorBlockValue).prod) = 5795615632589 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_149
      · exact prime_sixtyNineBO_14249
      · exact prime_sixtyNineBO_682447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5795615632589) ^ 2897807816294 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 5795615632589) ^ 38896749212 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 5795615632589) ^ 406738412 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 5795615632589) ^ 8492404 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_6134642754463 : Nat.Prime 6134642754463 := by
  apply lucas_primality 6134642754463 (5 : ZMod 6134642754463)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 5), (37, 1), (5347, 1), (63803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 5), (37, 1), (5347, 1), (63803, 1)] : List FactorBlock).map factorBlockValue).prod) = 6134642754463 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_37
      · exact prime_sixtyNineBO_5347
      · exact prime_sixtyNineBO_63803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 6134642754463) ^ 3067321377231 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 6134642754463) ^ 2044880918154 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 6134642754463) ^ 165801155526 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 6134642754463) ^ 1147305546 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 6134642754463) ^ 96149754 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_6473398431887 : Nat.Prime 6473398431887 := by
  apply lucas_primality 6473398431887 (5 : ZMod 6473398431887)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (6079, 1), (532439417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (6079, 1), (532439417, 1)] : List FactorBlock).map factorBlockValue).prod) = 6473398431887 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_6079
      · exact prime_sixtyNineBO_532439417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 6473398431887) ^ 3236699215943 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 6473398431887) ^ 1064878834 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 6473398431887) ^ 12158 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_7528900299607 : Nat.Prime 7528900299607 := by
  apply lucas_primality 7528900299607 (5 : ZMod 7528900299607)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (43, 1), (35897, 1), (38711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (43, 1), (35897, 1), (38711, 1)] : List FactorBlock).map factorBlockValue).prod) = 7528900299607 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_7
      · exact prime_sixtyNineBO_43
      · exact prime_sixtyNineBO_35897
      · exact prime_sixtyNineBO_38711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 7528900299607) ^ 3764450149803 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 7528900299607) ^ 2509633433202 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 7528900299607) ^ 1075557185658 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 7528900299607) ^ 175090704642 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 7528900299607) ^ 209736198 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 7528900299607) ^ 194489946 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_11591231265179 : Nat.Prime 11591231265179 := by
  apply lucas_primality 11591231265179 (2 : ZMod 11591231265179)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5795615632589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5795615632589, 1)] : List FactorBlock).map factorBlockValue).prod) = 11591231265179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_5795615632589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 11591231265179) ^ 5795615632589 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 11591231265179) ^ 2 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_11596185166681 : Nat.Prime 11596185166681 := by
  apply lucas_primality 11596185166681 (14 : ZMod 11596185166681)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (647, 1), (49786129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (647, 1), (49786129, 1)] : List FactorBlock).map factorBlockValue).prod) = 11596185166681 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_5
      · exact prime_sixtyNineBO_647
      · exact prime_sixtyNineBO_49786129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 11596185166681) ^ 5798092583340 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (14 : ZMod 11596185166681) ^ 3865395055560 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (14 : ZMod 11596185166681) ^ 2319237033336 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (14 : ZMod 11596185166681) ^ 17923006440 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (14 : ZMod 11596185166681) ^ 232920 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_11917942654697 : Nat.Prime 11917942654697 := by
  apply lucas_primality 11917942654697 (3 : ZMod 11917942654697)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (114595602449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (114595602449, 1)] : List FactorBlock).map factorBlockValue).prod) = 11917942654697 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_13
      · exact prime_sixtyNineBO_114595602449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 11917942654697) ^ 5958971327348 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 11917942654697) ^ 916764819592 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 11917942654697) ^ 104 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_13267405356571 : Nat.Prime 13267405356571 := by
  apply lucas_primality 13267405356571 (2 : ZMod 13267405356571)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (17, 1), (59, 1), (97, 1), (191, 1), (7933, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (17, 1), (59, 1), (97, 1), (191, 1), (7933, 1)] : List FactorBlock).map factorBlockValue).prod) = 13267405356571 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_5
      · exact prime_sixtyNineBO_17
      · exact prime_sixtyNineBO_59
      · exact prime_sixtyNineBO_97
      · exact prime_sixtyNineBO_191
      · exact prime_sixtyNineBO_7933
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 13267405356571) ^ 6633702678285 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 13267405356571) ^ 4422468452190 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 13267405356571) ^ 2653481071314 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 13267405356571) ^ 780435609210 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 13267405356571) ^ 224871277230 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 13267405356571) ^ 136777374810 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 13267405356571) ^ 69462855270 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 13267405356571) ^ 1672432290 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_27654453511147 : Nat.Prime 27654453511147 := by
  apply lucas_primality 27654453511147 (2 : ZMod 27654453511147)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (11, 1), (19952708161, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (11, 1), (19952708161, 1)] : List FactorBlock).map factorBlockValue).prod) = 27654453511147 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_7
      · exact prime_sixtyNineBO_11
      · exact prime_sixtyNineBO_19952708161
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 27654453511147) ^ 13827226755573 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 27654453511147) ^ 9218151170382 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 27654453511147) ^ 3950636215878 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 27654453511147) ^ 2514041228286 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 27654453511147) ^ 1386 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_29769593274247 : Nat.Prime 29769593274247 := by
  apply lucas_primality 29769593274247 (3 : ZMod 29769593274247)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (5639, 1), (7649, 1), (16433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (5639, 1), (7649, 1), (16433, 1)] : List FactorBlock).map factorBlockValue).prod) = 29769593274247 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_7
      · exact prime_sixtyNineBO_5639
      · exact prime_sixtyNineBO_7649
      · exact prime_sixtyNineBO_16433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 29769593274247) ^ 14884796637123 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 29769593274247) ^ 9923197758082 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 29769593274247) ^ 4252799039178 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 29769593274247) ^ 5279232714 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 29769593274247) ^ 3891958854 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 29769593274247) ^ 1811573862 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_34573352859533 : Nat.Prime 34573352859533 := by
  apply lucas_primality 34573352859533 (2 : ZMod 34573352859533)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (53, 1), (9593050183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (53, 1), (9593050183, 1)] : List FactorBlock).map factorBlockValue).prod) = 34573352859533 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_17
      · exact prime_sixtyNineBO_53
      · exact prime_sixtyNineBO_9593050183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 34573352859533) ^ 17286676429766 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 34573352859533) ^ 2033726638796 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 34573352859533) ^ 652327412444 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 34573352859533) ^ 3604 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_37450235917579 : Nat.Prime 37450235917579 := by
  apply lucas_primality 37450235917579 (2 : ZMod 37450235917579)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (567427816933, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (567427816933, 1)] : List FactorBlock).map factorBlockValue).prod) = 37450235917579 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_11
      · exact prime_sixtyNineBO_567427816933
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 37450235917579) ^ 18725117958789 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 37450235917579) ^ 12483411972526 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 37450235917579) ^ 3404566901598 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 37450235917579) ^ 66 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_41023486080779 : Nat.Prime 41023486080779 := by
  apply lucas_primality 41023486080779 (2 : ZMod 41023486080779)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (233, 1), (3607, 1), (24406219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (233, 1), (3607, 1), (24406219, 1)] : List FactorBlock).map factorBlockValue).prod) = 41023486080779 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_233
      · exact prime_sixtyNineBO_3607
      · exact prime_sixtyNineBO_24406219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 41023486080779) ^ 20511743040389 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 41023486080779) ^ 176066463866 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 41023486080779) ^ 11373298054 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 41023486080779) ^ 1680862 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_44347111964867 : Nat.Prime 44347111964867 := by
  apply lucas_primality 44347111964867 (2 : ZMod 44347111964867)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (179, 1), (123874614427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (179, 1), (123874614427, 1)] : List FactorBlock).map factorBlockValue).prod) = 44347111964867 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_179
      · exact prime_sixtyNineBO_123874614427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 44347111964867) ^ 22173555982433 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 44347111964867) ^ 247749228854 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 44347111964867) ^ 358 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_54737669175487 : Nat.Prime 54737669175487 := by
  apply lucas_primality 54737669175487 (5 : ZMod 54737669175487)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (137, 1), (163, 1), (1693, 1), (21937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (137, 1), (163, 1), (1693, 1), (21937, 1)] : List FactorBlock).map factorBlockValue).prod) = 54737669175487 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_11
      · exact prime_sixtyNineBO_137
      · exact prime_sixtyNineBO_163
      · exact prime_sixtyNineBO_1693
      · exact prime_sixtyNineBO_21937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 54737669175487) ^ 27368834587743 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 54737669175487) ^ 18245889725162 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 54737669175487) ^ 4976151743226 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 54737669175487) ^ 399545030478 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 54737669175487) ^ 335813921322 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 54737669175487) ^ 32331759702 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 54737669175487) ^ 2495221278 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_56550258880903 : Nat.Prime 56550258880903 := by
  apply lucas_primality 56550258880903 (3 : ZMod 56550258880903)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (47, 1), (149, 1), (11527, 1), (12973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (47, 1), (149, 1), (11527, 1), (12973, 1)] : List FactorBlock).map factorBlockValue).prod) = 56550258880903 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_47
      · exact prime_sixtyNineBO_149
      · exact prime_sixtyNineBO_11527
      · exact prime_sixtyNineBO_12973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 56550258880903) ^ 28275129440451 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 56550258880903) ^ 18850086293634 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 56550258880903) ^ 1203196997466 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 56550258880903) ^ 379531938798 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 56550258880903) ^ 4905895626 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 56550258880903) ^ 4359073374 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_56593356222257 : Nat.Prime 56593356222257 := by
  apply lucas_primality 56593356222257 (3 : ZMod 56593356222257)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (127, 1), (3978723019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (127, 1), (3978723019, 1)] : List FactorBlock).map factorBlockValue).prod) = 56593356222257 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_7
      · exact prime_sixtyNineBO_127
      · exact prime_sixtyNineBO_3978723019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 56593356222257) ^ 28296678111128 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 56593356222257) ^ 8084765174608 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 56593356222257) ^ 445616978128 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 56593356222257) ^ 14224 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_56978775693703 : Nat.Prime 56978775693703 := by
  apply lucas_primality 56978775693703 (3 : ZMod 56978775693703)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (1669, 1), (1896637231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (1669, 1), (1896637231, 1)] : List FactorBlock).map factorBlockValue).prod) = 56978775693703 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_1669
      · exact prime_sixtyNineBO_1896637231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 56978775693703) ^ 28489387846851 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 56978775693703) ^ 18992925231234 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 56978775693703) ^ 34139470158 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 56978775693703) ^ 30042 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_59325855612437 : Nat.Prime 59325855612437 := by
  apply lucas_primality 59325855612437 (2 : ZMod 59325855612437)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (211, 1), (349, 1), (1877, 1), (15329, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (211, 1), (349, 1), (1877, 1), (15329, 1)] : List FactorBlock).map factorBlockValue).prod) = 59325855612437 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_7
      · exact prime_sixtyNineBO_211
      · exact prime_sixtyNineBO_349
      · exact prime_sixtyNineBO_1877
      · exact prime_sixtyNineBO_15329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 59325855612437) ^ 29662927806218 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 59325855612437) ^ 8475122230348 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 59325855612437) ^ 281165192476 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 59325855612437) ^ 169988124964 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 59325855612437) ^ 31606742468 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 59325855612437) ^ 3870171284 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_59338638787777 : Nat.Prime 59338638787777 := by
  apply lucas_primality 59338638787777 (5 : ZMod 59338638787777)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (337, 1), (917078369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (337, 1), (917078369, 1)] : List FactorBlock).map factorBlockValue).prod) = 59338638787777 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_337
      · exact prime_sixtyNineBO_917078369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 59338638787777) ^ 29669319393888 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 59338638787777) ^ 19779546262592 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 59338638787777) ^ 176079046848 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 59338638787777) ^ 64704 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_64249659110303 : Nat.Prime 64249659110303 := by
  apply lucas_primality 64249659110303 (5 : ZMod 64249659110303)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (359, 1), (89484204889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (359, 1), (89484204889, 1)] : List FactorBlock).map factorBlockValue).prod) = 64249659110303 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_359
      · exact prime_sixtyNineBO_89484204889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 64249659110303) ^ 32124829555151 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 64249659110303) ^ 178968409778 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 64249659110303) ^ 718 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_71438978425273 : Nat.Prime 71438978425273 := by
  apply lucas_primality 71438978425273 (5 : ZMod 71438978425273)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (101, 1), (389, 1), (631, 1), (120067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (101, 1), (389, 1), (631, 1), (120067, 1)] : List FactorBlock).map factorBlockValue).prod) = 71438978425273 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_101
      · exact prime_sixtyNineBO_389
      · exact prime_sixtyNineBO_631
      · exact prime_sixtyNineBO_120067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 71438978425273) ^ 35719489212636 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 71438978425273) ^ 23812992808424 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 71438978425273) ^ 707316618072 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 71438978425273) ^ 183647759448 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 71438978425273) ^ 113215496712 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 71438978425273) ^ 594992616 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_76881349865821 : Nat.Prime 76881349865821 := by
  apply lucas_primality 76881349865821 (2 : ZMod 76881349865821)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (101, 1), (5209, 1), (2435533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (101, 1), (5209, 1), (2435533, 1)] : List FactorBlock).map factorBlockValue).prod) = 76881349865821 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_5
      · exact prime_sixtyNineBO_101
      · exact prime_sixtyNineBO_5209
      · exact prime_sixtyNineBO_2435533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 76881349865821) ^ 38440674932910 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 76881349865821) ^ 25627116621940 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 76881349865821) ^ 15376269973164 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 76881349865821) ^ 761201483820 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 76881349865821) ^ 14759329980 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 76881349865821) ^ 31566540 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_77484555853781 : Nat.Prime 77484555853781 := by
  apply lucas_primality 77484555853781 (3 : ZMod 77484555853781)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (19, 1), (359, 1), (587, 1), (967607, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (19, 1), (359, 1), (587, 1), (967607, 1)] : List FactorBlock).map factorBlockValue).prod) = 77484555853781 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_5
      · exact prime_sixtyNineBO_19
      · exact prime_sixtyNineBO_359
      · exact prime_sixtyNineBO_587
      · exact prime_sixtyNineBO_967607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 77484555853781) ^ 38742277926890 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 77484555853781) ^ 15496911170756 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 77484555853781) ^ 4078134518620 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 77484555853781) ^ 215834417420 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 77484555853781) ^ 132000946940 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 77484555853781) ^ 80078540 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_82786495709329 : Nat.Prime 82786495709329 := by
  apply lucas_primality 82786495709329 (7 : ZMod 82786495709329)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (1724718660611, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (1724718660611, 1)] : List FactorBlock).map factorBlockValue).prod) = 82786495709329 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_1724718660611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 82786495709329) ^ 41393247854664 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (7 : ZMod 82786495709329) ^ 27595498569776 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (7 : ZMod 82786495709329) ^ 48 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_84791095060619 : Nat.Prime 84791095060619 := by
  apply lucas_primality 84791095060619 (2 : ZMod 84791095060619)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (907, 1), (2749565311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (907, 1), (2749565311, 1)] : List FactorBlock).map factorBlockValue).prod) = 84791095060619 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_17
      · exact prime_sixtyNineBO_907
      · exact prime_sixtyNineBO_2749565311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 84791095060619) ^ 42395547530309 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 84791095060619) ^ 4987711474154 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 84791095060619) ^ 93485220574 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 84791095060619) ^ 30838 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_148533492461777 : Nat.Prime 148533492461777 := by
  apply lucas_primality 148533492461777 (3 : ZMod 148533492461777)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7589, 1), (1223263049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7589, 1), (1223263049, 1)] : List FactorBlock).map factorBlockValue).prod) = 148533492461777 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_7589
      · exact prime_sixtyNineBO_1223263049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 148533492461777) ^ 74266746230888 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 148533492461777) ^ 19572208784 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 148533492461777) ^ 121424 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_190317239508181 : Nat.Prime 190317239508181 := by
  apply lucas_primality 190317239508181 (6 : ZMod 190317239508181)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (19, 1), (166944946937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (19, 1), (166944946937, 1)] : List FactorBlock).map factorBlockValue).prod) = 190317239508181 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_5
      · exact prime_sixtyNineBO_19
      · exact prime_sixtyNineBO_166944946937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 190317239508181) ^ 95158619754090 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (6 : ZMod 190317239508181) ^ 63439079836060 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (6 : ZMod 190317239508181) ^ 38063447901636 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (6 : ZMod 190317239508181) ^ 10016696816220 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (6 : ZMod 190317239508181) ^ 1140 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_227990231938657 : Nat.Prime 227990231938657 := by
  apply lucas_primality 227990231938657 (5 : ZMod 227990231938657)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (11, 1), (1481, 1), (48593257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (11, 1), (1481, 1), (48593257, 1)] : List FactorBlock).map factorBlockValue).prod) = 227990231938657 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_11
      · exact prime_sixtyNineBO_1481
      · exact prime_sixtyNineBO_48593257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 227990231938657) ^ 113995115969328 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 227990231938657) ^ 75996743979552 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 227990231938657) ^ 20726384721696 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 227990231938657) ^ 153943438176 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 227990231938657) ^ 4691808 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_334375885506319 : Nat.Prime 334375885506319 := by
  apply lucas_primality 334375885506319 (3 : ZMod 334375885506319)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (269, 2), (40534567, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (269, 2), (40534567, 1)] : List FactorBlock).map factorBlockValue).prod) = 334375885506319 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_19
      · exact prime_sixtyNineBO_269
      · exact prime_sixtyNineBO_40534567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 334375885506319) ^ 167187942753159 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 334375885506319) ^ 111458628502106 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 334375885506319) ^ 17598730816122 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 334375885506319) ^ 1243033031622 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 334375885506319) ^ 8249154 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_339229454538101 : Nat.Prime 339229454538101 := by
  apply lucas_primality 339229454538101 (2 : ZMod 339229454538101)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (7, 1), (141107, 1), (3434369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (7, 1), (141107, 1), (3434369, 1)] : List FactorBlock).map factorBlockValue).prod) = 339229454538101 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_5
      · exact prime_sixtyNineBO_7
      · exact prime_sixtyNineBO_141107
      · exact prime_sixtyNineBO_3434369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 339229454538101) ^ 169614727269050 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 339229454538101) ^ 67845890907620 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 339229454538101) ^ 48461350648300 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 339229454538101) ^ 2404058300 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 339229454538101) ^ 98774900 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_343089635009119 : Nat.Prime 343089635009119 := by
  apply lucas_primality 343089635009119 (3 : ZMod 343089635009119)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2141, 1), (13691, 1), (1950763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2141, 1), (13691, 1), (1950763, 1)] : List FactorBlock).map factorBlockValue).prod) = 343089635009119 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_2141
      · exact prime_sixtyNineBO_13691
      · exact prime_sixtyNineBO_1950763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 343089635009119) ^ 171544817504559 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 343089635009119) ^ 114363211669706 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 343089635009119) ^ 160247377398 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 343089635009119) ^ 25059501498 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 343089635009119) ^ 175874586 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_415603237769219 : Nat.Prime 415603237769219 := by
  apply lucas_primality 415603237769219 (2 : ZMod 415603237769219)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (109, 1), (22543, 1), (3676909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (109, 1), (22543, 1), (3676909, 1)] : List FactorBlock).map factorBlockValue).prod) = 415603237769219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_23
      · exact prime_sixtyNineBO_109
      · exact prime_sixtyNineBO_22543
      · exact prime_sixtyNineBO_3676909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 415603237769219) ^ 207801618884609 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 415603237769219) ^ 18069705989966 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 415603237769219) ^ 3812873741002 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 415603237769219) ^ 18436021726 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 415603237769219) ^ 113030602 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_492451581900259 : Nat.Prime 492451581900259 := by
  apply lucas_primality 492451581900259 (2 : ZMod 492451581900259)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (131, 1), (208842910051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (131, 1), (208842910051, 1)] : List FactorBlock).map factorBlockValue).prod) = 492451581900259 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_131
      · exact prime_sixtyNineBO_208842910051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 492451581900259) ^ 246225790950129 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 492451581900259) ^ 164150527300086 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 492451581900259) ^ 3759172380918 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 492451581900259) ^ 2358 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_549237458000821 : Nat.Prime 549237458000821 := by
  apply lucas_primality 549237458000821 (11 : ZMod 549237458000821)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (97, 1), (1933, 1), (6073, 1), (8039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (97, 1), (1933, 1), (6073, 1), (8039, 1)] : List FactorBlock).map factorBlockValue).prod) = 549237458000821 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_5
      · exact prime_sixtyNineBO_97
      · exact prime_sixtyNineBO_1933
      · exact prime_sixtyNineBO_6073
      · exact prime_sixtyNineBO_8039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 549237458000821) ^ 274618729000410 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (11 : ZMod 549237458000821) ^ 183079152666940 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (11 : ZMod 549237458000821) ^ 109847491600164 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (11 : ZMod 549237458000821) ^ 5662241835060 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (11 : ZMod 549237458000821) ^ 284137329540 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (11 : ZMod 549237458000821) ^ 90439232340 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (11 : ZMod 549237458000821) ^ 68321614380 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_582605858869831 : Nat.Prime 582605858869831 := by
  apply lucas_primality 582605858869831 (3 : ZMod 582605858869831)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (6473398431887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (6473398431887, 1)] : List FactorBlock).map factorBlockValue).prod) = 582605858869831 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_5
      · exact prime_sixtyNineBO_6473398431887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 582605858869831) ^ 291302929434915 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 582605858869831) ^ 194201952956610 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 582605858869831) ^ 116521171773966 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 582605858869831) ^ 90 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_589028010947197 : Nat.Prime 589028010947197 := by
  apply lucas_primality 589028010947197 (2 : ZMod 589028010947197)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (9521, 1), (5155515973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (9521, 1), (5155515973, 1)] : List FactorBlock).map factorBlockValue).prod) = 589028010947197 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_9521
      · exact prime_sixtyNineBO_5155515973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 589028010947197) ^ 294514005473598 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 589028010947197) ^ 196342670315732 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 589028010947197) ^ 61866191676 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 589028010947197) ^ 114252 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_619827629364199 : Nat.Prime 619827629364199 := by
  apply lucas_primality 619827629364199 (3 : ZMod 619827629364199)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (19, 1), (42701, 1), (42443069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (19, 1), (42701, 1), (42443069, 1)] : List FactorBlock).map factorBlockValue).prod) = 619827629364199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_19
      · exact prime_sixtyNineBO_42701
      · exact prime_sixtyNineBO_42443069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 619827629364199) ^ 309913814682099 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 619827629364199) ^ 206609209788066 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 619827629364199) ^ 32622506808642 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 619827629364199) ^ 14515529598 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 619827629364199) ^ 14603742 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_718033793568929 : Nat.Prime 718033793568929 := by
  apply lucas_primality 718033793568929 (3 : ZMod 718033793568929)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (79, 1), (661, 1), (429700991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (79, 1), (661, 1), (429700991, 1)] : List FactorBlock).map factorBlockValue).prod) = 718033793568929 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_79
      · exact prime_sixtyNineBO_661
      · exact prime_sixtyNineBO_429700991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 718033793568929) ^ 359016896784464 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 718033793568929) ^ 9089035361632 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 718033793568929) ^ 1086284105248 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 718033793568929) ^ 1671008 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_833548611678917 : Nat.Prime 833548611678917 := by
  apply lucas_primality 833548611678917 (2 : ZMod 833548611678917)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (29769593274247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (29769593274247, 1)] : List FactorBlock).map factorBlockValue).prod) = 833548611678917 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_7
      · exact prime_sixtyNineBO_29769593274247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 833548611678917) ^ 416774305839458 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 833548611678917) ^ 119078373096988 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 833548611678917) ^ 28 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_1383864297584779 : Nat.Prime 1383864297584779 := by
  apply lucas_primality 1383864297584779 (10 : ZMod 1383864297584779)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (76881349865821, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (76881349865821, 1)] : List FactorBlock).map factorBlockValue).prod) = 1383864297584779 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_76881349865821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 1383864297584779) ^ 691932148792389 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (10 : ZMod 1383864297584779) ^ 461288099194926 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (10 : ZMod 1383864297584779) ^ 18 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_1761762670108039 : Nat.Prime 1761762670108039 := by
  apply lucas_primality 1761762670108039 (15 : ZMod 1761762670108039)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (7528900299607, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (7528900299607, 1)] : List FactorBlock).map factorBlockValue).prod) = 1761762670108039 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_13
      · exact prime_sixtyNineBO_7528900299607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (15 : ZMod 1761762670108039) ^ 880881335054019 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (15 : ZMod 1761762670108039) ^ 587254223369346 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (15 : ZMod 1761762670108039) ^ 135520205392926 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (15 : ZMod 1761762670108039) ^ 234 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_1968199739166511 : Nat.Prime 1968199739166511 := by
  apply lucas_primality 1968199739166511 (3 : ZMod 1968199739166511)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (1597, 1), (3391, 1), (4038257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (1597, 1), (3391, 1), (4038257, 1)] : List FactorBlock).map factorBlockValue).prod) = 1968199739166511 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_5
      · exact prime_sixtyNineBO_1597
      · exact prime_sixtyNineBO_3391
      · exact prime_sixtyNineBO_4038257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1968199739166511) ^ 984099869583255 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1968199739166511) ^ 656066579722170 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1968199739166511) ^ 393639947833302 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1968199739166511) ^ 1232435653830 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1968199739166511) ^ 580418678610 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 1968199739166511) ^ 487388430 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_2954604727545773 : Nat.Prime 2954604727545773 := by
  apply lucas_primality 2954604727545773 (2 : ZMod 2954604727545773)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (571, 1), (184801396519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (571, 1), (184801396519, 1)] : List FactorBlock).map factorBlockValue).prod) = 2954604727545773 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_7
      · exact prime_sixtyNineBO_571
      · exact prime_sixtyNineBO_184801396519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2954604727545773) ^ 1477302363772886 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2954604727545773) ^ 422086389649396 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2954604727545773) ^ 5174439102532 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2954604727545773) ^ 15988 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_3370641025715603 : Nat.Prime 3370641025715603 := by
  apply lucas_primality 3370641025715603 (2 : ZMod 3370641025715603)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (359, 1), (66809, 1), (70267271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (359, 1), (66809, 1), (70267271, 1)] : List FactorBlock).map factorBlockValue).prod) = 3370641025715603 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_359
      · exact prime_sixtyNineBO_66809
      · exact prime_sixtyNineBO_70267271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3370641025715603) ^ 1685320512857801 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 3370641025715603) ^ 9388972216478 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 3370641025715603) ^ 50451900578 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 3370641025715603) ^ 47968862 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_4449685080592651 : Nat.Prime 4449685080592651 := by
  apply lucas_primality 4449685080592651 (3 : ZMod 4449685080592651)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (3847, 1), (73849, 1), (104417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (3847, 1), (73849, 1), (104417, 1)] : List FactorBlock).map factorBlockValue).prod) = 4449685080592651 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_5
      · exact prime_sixtyNineBO_3847
      · exact prime_sixtyNineBO_73849
      · exact prime_sixtyNineBO_104417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4449685080592651) ^ 2224842540296325 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 4449685080592651) ^ 1483228360197550 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 4449685080592651) ^ 889937016118530 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 4449685080592651) ^ 1156663654950 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 4449685080592651) ^ 60253829850 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 4449685080592651) ^ 42614565450 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_5759673424637371 : Nat.Prime 5759673424637371 := by
  apply lucas_primality 5759673424637371 (22 : ZMod 5759673424637371)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (59, 1), (464864683183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (59, 1), (464864683183, 1)] : List FactorBlock).map factorBlockValue).prod) = 5759673424637371 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_5
      · exact prime_sixtyNineBO_7
      · exact prime_sixtyNineBO_59
      · exact prime_sixtyNineBO_464864683183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (22 : ZMod 5759673424637371) ^ 2879836712318685 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (22 : ZMod 5759673424637371) ^ 1919891141545790 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (22 : ZMod 5759673424637371) ^ 1151934684927474 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (22 : ZMod 5759673424637371) ^ 822810489233910 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (22 : ZMod 5759673424637371) ^ 97621583468430 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (22 : ZMod 5759673424637371) ^ 12390 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_6135992800124441 : Nat.Prime 6135992800124441 := by
  apply lucas_primality 6135992800124441 (3 : ZMod 6135992800124441)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (11, 1), (47, 2), (6313009589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (11, 1), (47, 2), (6313009589, 1)] : List FactorBlock).map factorBlockValue).prod) = 6135992800124441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_5
      · exact prime_sixtyNineBO_11
      · exact prime_sixtyNineBO_47
      · exact prime_sixtyNineBO_6313009589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 6135992800124441) ^ 3067996400062220 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 6135992800124441) ^ 1227198560024888 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 6135992800124441) ^ 557817527284040 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 6135992800124441) ^ 130553038300520 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 6135992800124441) ^ 971960 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_6220577778297277 : Nat.Prime 6220577778297277 := by
  apply lucas_primality 6220577778297277 (2 : ZMod 6220577778297277)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (2220403, 1), (233462791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (2220403, 1), (233462791, 1)] : List FactorBlock).map factorBlockValue).prod) = 6220577778297277 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_2220403
      · exact prime_sixtyNineBO_233462791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 6220577778297277) ^ 3110288889148638 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 6220577778297277) ^ 2073525926099092 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 6220577778297277) ^ 2801553492 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 6220577778297277) ^ 26644836 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_11409675082261943 : Nat.Prime 11409675082261943 := by
  apply lucas_primality 11409675082261943 (5 : ZMod 11409675082261943)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (15651289, 1), (364496339, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (15651289, 1), (364496339, 1)] : List FactorBlock).map factorBlockValue).prod) = 11409675082261943 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_15651289
      · exact prime_sixtyNineBO_364496339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 11409675082261943) ^ 5704837541130971 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 11409675082261943) ^ 728992678 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 11409675082261943) ^ 31302578 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_13636207846012379 : Nat.Prime 13636207846012379 := by
  apply lucas_primality 13636207846012379 (2 : ZMod 13636207846012379)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (619827629364199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (619827629364199, 1)] : List FactorBlock).map factorBlockValue).prod) = 13636207846012379 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_11
      · exact prime_sixtyNineBO_619827629364199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 13636207846012379) ^ 6818103923006189 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 13636207846012379) ^ 1239655258728398 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 13636207846012379) ^ 22 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_24387869551319401 : Nat.Prime 24387869551319401 := by
  apply lucas_primality 24387869551319401 (11 : ZMod 24387869551319401)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 2), (7, 1), (31, 1), (89, 1), (383, 1), (5495081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 2), (7, 1), (31, 1), (89, 1), (383, 1), (5495081, 1)] : List FactorBlock).map factorBlockValue).prod) = 24387869551319401 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_5
      · exact prime_sixtyNineBO_7
      · exact prime_sixtyNineBO_31
      · exact prime_sixtyNineBO_89
      · exact prime_sixtyNineBO_383
      · exact prime_sixtyNineBO_5495081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 24387869551319401) ^ 12193934775659700 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (11 : ZMod 24387869551319401) ^ 8129289850439800 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (11 : ZMod 24387869551319401) ^ 4877573910263880 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (11 : ZMod 24387869551319401) ^ 3483981364474200 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (11 : ZMod 24387869551319401) ^ 786705469397400 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (11 : ZMod 24387869551319401) ^ 274021006194600 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (11 : ZMod 24387869551319401) ^ 63675899611800 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (11 : ZMod 24387869551319401) ^ 4438127400 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_26760991530711283 : Nat.Prime 26760991530711283 := by
  apply lucas_primality 26760991530711283 (2 : ZMod 26760991530711283)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (343089635009119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (343089635009119, 1)] : List FactorBlock).map factorBlockValue).prod) = 26760991530711283 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_13
      · exact prime_sixtyNineBO_343089635009119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 26760991530711283) ^ 13380495765355641 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 26760991530711283) ^ 8920330510237094 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 26760991530711283) ^ 2058537810054714 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 26760991530711283) ^ 78 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_31395735542919031 : Nat.Prime 31395735542919031 := by
  apply lucas_primality 31395735542919031 (3 : ZMod 31395735542919031)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (1847, 1), (4583, 1), (123632501, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (1847, 1), (4583, 1), (123632501, 1)] : List FactorBlock).map factorBlockValue).prod) = 31395735542919031 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_5
      · exact prime_sixtyNineBO_1847
      · exact prime_sixtyNineBO_4583
      · exact prime_sixtyNineBO_123632501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 31395735542919031) ^ 15697867771459515 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 31395735542919031) ^ 10465245180973010 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 31395735542919031) ^ 6279147108583806 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 31395735542919031) ^ 16998232562490 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 31395735542919031) ^ 6850476880410 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 31395735542919031) ^ 253944030 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_37225534502073527 : Nat.Prime 37225534502073527 := by
  apply lucas_primality 37225534502073527 (5 : ZMod 37225534502073527)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (71, 1), (37450235917579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (71, 1), (37450235917579, 1)] : List FactorBlock).map factorBlockValue).prod) = 37225534502073527 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_7
      · exact prime_sixtyNineBO_71
      · exact prime_sixtyNineBO_37450235917579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 37225534502073527) ^ 18612767251036763 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 37225534502073527) ^ 5317933500296218 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 37225534502073527) ^ 524303302846106 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 37225534502073527) ^ 994 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_40625384123447983 : Nat.Prime 40625384123447983 := by
  apply lucas_primality 40625384123447983 (3 : ZMod 40625384123447983)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (1040407, 1), (2169310457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (1040407, 1), (2169310457, 1)] : List FactorBlock).map factorBlockValue).prod) = 40625384123447983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_1040407
      · exact prime_sixtyNineBO_2169310457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 40625384123447983) ^ 20312692061723991 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 40625384123447983) ^ 13541794707815994 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 40625384123447983) ^ 39047588226 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 40625384123447983) ^ 18727326 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_60314838659790037 : Nat.Prime 60314838659790037 := by
  apply lucas_primality 60314838659790037 (2 : ZMod 60314838659790037)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (718033793568929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (718033793568929, 1)] : List FactorBlock).map factorBlockValue).prod) = 60314838659790037 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_7
      · exact prime_sixtyNineBO_718033793568929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 60314838659790037) ^ 30157419329895018 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 60314838659790037) ^ 20104946219930012 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 60314838659790037) ^ 8616405522827148 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 60314838659790037) ^ 84 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_87395845581438773 : Nat.Prime 87395845581438773 := by
  apply lucas_primality 87395845581438773 (2 : ZMod 87395845581438773)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (67, 1), (139, 1), (335153033323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (67, 1), (139, 1), (335153033323, 1)] : List FactorBlock).map factorBlockValue).prod) = 87395845581438773 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_7
      · exact prime_sixtyNineBO_67
      · exact prime_sixtyNineBO_139
      · exact prime_sixtyNineBO_335153033323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 87395845581438773) ^ 43697922790719386 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 87395845581438773) ^ 12485120797348396 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 87395845581438773) ^ 1304415605693116 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 87395845581438773) ^ 628747090513948 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 87395845581438773) ^ 260764 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_152329424889651487 : Nat.Prime 152329424889651487 := by
  apply lucas_primality 152329424889651487 (5 : ZMod 152329424889651487)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (113, 1), (6043, 1), (37179326159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (113, 1), (6043, 1), (37179326159, 1)] : List FactorBlock).map factorBlockValue).prod) = 152329424889651487 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_113
      · exact prime_sixtyNineBO_6043
      · exact prime_sixtyNineBO_37179326159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 152329424889651487) ^ 76164712444825743 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 152329424889651487) ^ 50776474963217162 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 152329424889651487) ^ 1348048007873022 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 152329424889651487) ^ 25207583135802 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 152329424889651487) ^ 4097154 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_158182660729565987 : Nat.Prime 158182660729565987 := by
  apply lucas_primality 158182660729565987 (5 : ZMod 158182660729565987)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1231, 1), (64249659110303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1231, 1), (64249659110303, 1)] : List FactorBlock).map factorBlockValue).prod) = 158182660729565987 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_1231
      · exact prime_sixtyNineBO_64249659110303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 158182660729565987) ^ 79091330364782993 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 158182660729565987) ^ 128499318220606 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 158182660729565987) ^ 2462 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_176434845614554139 : Nat.Prime 176434845614554139 := by
  apply lucas_primality 176434845614554139 (2 : ZMod 176434845614554139)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3797, 1), (1143679, 1), (20314663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3797, 1), (1143679, 1), (20314663, 1)] : List FactorBlock).map factorBlockValue).prod) = 176434845614554139 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3797
      · exact prime_sixtyNineBO_1143679
      · exact prime_sixtyNineBO_20314663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 176434845614554139) ^ 88217422807277069 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 176434845614554139) ^ 46466906930354 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 176434845614554139) ^ 154269550822 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 176434845614554139) ^ 8685098326 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_267648485123377037 : Nat.Prime 267648485123377037 := by
  apply lucas_primality 267648485123377037 (2 : ZMod 267648485123377037)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (23, 1), (415603237769219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (23, 1), (415603237769219, 1)] : List FactorBlock).map factorBlockValue).prod) = 267648485123377037 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_7
      · exact prime_sixtyNineBO_23
      · exact prime_sixtyNineBO_415603237769219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 267648485123377037) ^ 133824242561688518 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 267648485123377037) ^ 38235497874768148 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 267648485123377037) ^ 11636890657538132 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 267648485123377037) ^ 644 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_560477726185536557 : Nat.Prime 560477726185536557 := by
  apply lucas_primality 560477726185536557 (2 : ZMod 560477726185536557)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11284211, 1), (12417299849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11284211, 1), (12417299849, 1)] : List FactorBlock).map factorBlockValue).prod) = 560477726185536557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_11284211
      · exact prime_sixtyNineBO_12417299849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 560477726185536557) ^ 280238863092768278 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 560477726185536557) ^ 49669199396 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 560477726185536557) ^ 45136844 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_656671553715872281 : Nat.Prime 656671553715872281 := by
  apply lucas_primality 656671553715872281 (7 : ZMod 656671553715872281)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (17, 1), (4157, 1), (77435126401, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (17, 1), (4157, 1), (77435126401, 1)] : List FactorBlock).map factorBlockValue).prod) = 656671553715872281 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_5
      · exact prime_sixtyNineBO_17
      · exact prime_sixtyNineBO_4157
      · exact prime_sixtyNineBO_77435126401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 656671553715872281) ^ 328335776857936140 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (7 : ZMod 656671553715872281) ^ 218890517905290760 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (7 : ZMod 656671553715872281) ^ 131334310743174456 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (7 : ZMod 656671553715872281) ^ 38627738453874840 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (7 : ZMod 656671553715872281) ^ 157967657858040 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (7 : ZMod 656671553715872281) ^ 8480280 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_818815161375170989 : Nat.Prime 818815161375170989 := by
  apply lucas_primality 818815161375170989 (2 : ZMod 818815161375170989)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (653, 1), (70639, 1), (211324021, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (653, 1), (70639, 1), (211324021, 1)] : List FactorBlock).map factorBlockValue).prod) = 818815161375170989 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_7
      · exact prime_sixtyNineBO_653
      · exact prime_sixtyNineBO_70639
      · exact prime_sixtyNineBO_211324021
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 818815161375170989) ^ 409407580687585494 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 818815161375170989) ^ 272938387125056996 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 818815161375170989) ^ 116973594482167284 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 818815161375170989) ^ 1253928271631196 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 818815161375170989) ^ 11591545199892 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 818815161375170989) ^ 3874690428 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_1257242877640270177 : Nat.Prime 1257242877640270177 := by
  apply lucas_primality 1257242877640270177 (7 : ZMod 1257242877640270177)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (17, 1), (137, 1), (1871, 1), (3005416559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (17, 1), (137, 1), (1871, 1), (3005416559, 1)] : List FactorBlock).map factorBlockValue).prod) = 1257242877640270177 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_17
      · exact prime_sixtyNineBO_137
      · exact prime_sixtyNineBO_1871
      · exact prime_sixtyNineBO_3005416559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1257242877640270177) ^ 628621438820135088 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (7 : ZMod 1257242877640270177) ^ 419080959213423392 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (7 : ZMod 1257242877640270177) ^ 73955463390604128 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (7 : ZMod 1257242877640270177) ^ 9176955311242848 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (7 : ZMod 1257242877640270177) ^ 671963055927456 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (7 : ZMod 1257242877640270177) ^ 418325664 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_1682861583759080083 : Nat.Prime 1682861583759080083 := by
  apply lucas_primality 1682861583759080083 (2 : ZMod 1682861583759080083)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 2), (67, 1), (11596185166681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 2), (67, 1), (11596185166681, 1)] : List FactorBlock).map factorBlockValue).prod) = 1682861583759080083 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_19
      · exact prime_sixtyNineBO_67
      · exact prime_sixtyNineBO_11596185166681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1682861583759080083) ^ 841430791879540041 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1682861583759080083) ^ 560953861253026694 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1682861583759080083) ^ 88571662303109478 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1682861583759080083) ^ 25117337071031046 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1682861583759080083) ^ 145122 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_2727404814486332041 : Nat.Prime 2727404814486332041 := by
  apply lucas_primality 2727404814486332041 (7 : ZMod 2727404814486332041)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (67, 1), (339229454538101, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (67, 1), (339229454538101, 1)] : List FactorBlock).map factorBlockValue).prod) = 2727404814486332041 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_5
      · exact prime_sixtyNineBO_67
      · exact prime_sixtyNineBO_339229454538101
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 2727404814486332041) ^ 1363702407243166020 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (7 : ZMod 2727404814486332041) ^ 909134938162110680 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (7 : ZMod 2727404814486332041) ^ 545480962897266408 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (7 : ZMod 2727404814486332041) ^ 40707534544572120 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (7 : ZMod 2727404814486332041) ^ 8040 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_2904332459514447167 : Nat.Prime 2904332459514447167 := by
  apply lucas_primality 2904332459514447167 (5 : ZMod 2904332459514447167)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (311, 1), (463, 1), (809, 1), (1021, 1), (12209579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (311, 1), (463, 1), (809, 1), (1021, 1), (12209579, 1)] : List FactorBlock).map factorBlockValue).prod) = 2904332459514447167 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_311
      · exact prime_sixtyNineBO_463
      · exact prime_sixtyNineBO_809
      · exact prime_sixtyNineBO_1021
      · exact prime_sixtyNineBO_12209579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2904332459514447167) ^ 1452166229757223583 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 2904332459514447167) ^ 9338689580432306 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 2904332459514447167) ^ 6272856284048482 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 2904332459514447167) ^ 3590027762069774 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 2904332459514447167) ^ 2844595944676246 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 2904332459514447167) ^ 237873268154 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_4812236858329330949 : Nat.Prime 4812236858329330949 := by
  apply lucas_primality 4812236858329330949 (2 : ZMod 4812236858329330949)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (349, 1), (492451581900259, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (349, 1), (492451581900259, 1)] : List FactorBlock).map factorBlockValue).prod) = 4812236858329330949 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_7
      · exact prime_sixtyNineBO_349
      · exact prime_sixtyNineBO_492451581900259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4812236858329330949) ^ 2406118429164665474 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 4812236858329330949) ^ 687462408332761564 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 4812236858329330949) ^ 13788644293207252 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 4812236858329330949) ^ 9772 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_6849481560150114419 : Nat.Prime 6849481560150114419 := by
  apply lucas_primality 6849481560150114419 (2 : ZMod 6849481560150114419)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (151, 1), (193, 1), (154279, 1), (58592669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (151, 1), (193, 1), (154279, 1), (58592669, 1)] : List FactorBlock).map factorBlockValue).prod) = 6849481560150114419 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_13
      · exact prime_sixtyNineBO_151
      · exact prime_sixtyNineBO_193
      · exact prime_sixtyNineBO_154279
      · exact prime_sixtyNineBO_58592669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6849481560150114419) ^ 3424740780075057209 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 6849481560150114419) ^ 526883196934624186 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 6849481560150114419) ^ 45360805034106718 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 6849481560150114419) ^ 35489541762435826 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 6849481560150114419) ^ 44396719969342 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 6849481560150114419) ^ 116899975322 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_16490570002582268309 : Nat.Prime 16490570002582268309 := by
  apply lucas_primality 16490570002582268309 (2 : ZMod 16490570002582268309)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1123, 1), (9068623, 1), (404813113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1123, 1), (9068623, 1), (404813113, 1)] : List FactorBlock).map factorBlockValue).prod) = 16490570002582268309 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_1123
      · exact prime_sixtyNineBO_9068623
      · exact prime_sixtyNineBO_404813113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 16490570002582268309) ^ 8245285001291134154 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 16490570002582268309) ^ 14684390029013596 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 16490570002582268309) ^ 1818420503596 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 16490570002582268309) ^ 40736254516 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_20959726153797832547 : Nat.Prime 20959726153797832547 := by
  apply lucas_primality 20959726153797832547 (2 : ZMod 20959726153797832547)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (37, 1), (3623, 1), (191831, 1), (23972749, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (37, 1), (3623, 1), (191831, 1), (23972749, 1)] : List FactorBlock).map factorBlockValue).prod) = 20959726153797832547 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_17
      · exact prime_sixtyNineBO_37
      · exact prime_sixtyNineBO_3623
      · exact prime_sixtyNineBO_191831
      · exact prime_sixtyNineBO_23972749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 20959726153797832547) ^ 10479863076898916273 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 20959726153797832547) ^ 1232925067870460738 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 20959726153797832547) ^ 566479085237779258 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 20959726153797832547) ^ 5785185248081102 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 20959726153797832547) ^ 109261413190766 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 20959726153797832547) ^ 874314670954 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_24645628453965733987 : Nat.Prime 24645628453965733987 := by
  apply lucas_primality 24645628453965733987 (3 : ZMod 24645628453965733987)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (47, 1), (87395845581438773, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (47, 1), (87395845581438773, 1)] : List FactorBlock).map factorBlockValue).prod) = 24645628453965733987 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_47
      · exact prime_sixtyNineBO_87395845581438773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 24645628453965733987) ^ 12322814226982866993 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 24645628453965733987) ^ 8215209484655244662 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 24645628453965733987) ^ 524375073488632638 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 24645628453965733987) ^ 282 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_29277068545327605349 : Nat.Prime 29277068545327605349 := by
  apply lucas_primality 29277068545327605349 (6 : ZMod 29277068545327605349)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1741, 1), (3889, 1), (360337639471, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1741, 1), (3889, 1), (360337639471, 1)] : List FactorBlock).map factorBlockValue).prod) = 29277068545327605349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_1741
      · exact prime_sixtyNineBO_3889
      · exact prime_sixtyNineBO_360337639471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 29277068545327605349) ^ 14638534272663802674 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (6 : ZMod 29277068545327605349) ^ 9759022848442535116 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (6 : ZMod 29277068545327605349) ^ 16816236958832628 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (6 : ZMod 29277068545327605349) ^ 7528173963828132 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (6 : ZMod 29277068545327605349) ^ 81248988 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_34493344144497192683 : Nat.Prime 34493344144497192683 := by
  apply lucas_primality 34493344144497192683 (2 : ZMod 34493344144497192683)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13, 1), (31, 1), (2278487, 1), (2683216183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13, 1), (31, 1), (2278487, 1), (2683216183, 1)] : List FactorBlock).map factorBlockValue).prod) = 34493344144497192683 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_7
      · exact prime_sixtyNineBO_13
      · exact prime_sixtyNineBO_31
      · exact prime_sixtyNineBO_2278487
      · exact prime_sixtyNineBO_2683216183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 34493344144497192683) ^ 17246672072248596341 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 34493344144497192683) ^ 4927620592071027526 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 34493344144497192683) ^ 2653334164961322514 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 34493344144497192683) ^ 1112688520790232022 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 34493344144497192683) ^ 15138705704486 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 34493344144497192683) ^ 12855223654 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_75764619533606924969 : Nat.Prime 75764619533606924969 := by
  apply lucas_primality 75764619533606924969 (3 : ZMod 75764619533606924969)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17, 1), (19, 2), (706897, 1), (2183052589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17, 1), (19, 2), (706897, 1), (2183052589, 1)] : List FactorBlock).map factorBlockValue).prod) = 75764619533606924969 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_17
      · exact prime_sixtyNineBO_19
      · exact prime_sixtyNineBO_706897
      · exact prime_sixtyNineBO_2183052589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 75764619533606924969) ^ 37882309766803462484 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 75764619533606924969) ^ 4456742325506289704 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 75764619533606924969) ^ 3987611554400364472 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 75764619533606924969) ^ 107179149909544 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 75764619533606924969) ^ 34705815112 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_80807924209533053443 : Nat.Prime 80807924209533053443 := by
  apply lucas_primality 80807924209533053443 (2 : ZMod 80807924209533053443)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (13, 1), (101, 1), (127, 1), (49211, 1), (234462841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (13, 1), (101, 1), (127, 1), (49211, 1), (234462841, 1)] : List FactorBlock).map factorBlockValue).prod) = 80807924209533053443 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_7
      · exact prime_sixtyNineBO_13
      · exact prime_sixtyNineBO_101
      · exact prime_sixtyNineBO_127
      · exact prime_sixtyNineBO_49211
      · exact prime_sixtyNineBO_234462841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 80807924209533053443) ^ 40403962104766526721 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 80807924209533053443) ^ 26935974736511017814 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 80807924209533053443) ^ 11543989172790436206 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 80807924209533053443) ^ 6215994169964081034 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 80807924209533053443) ^ 800078457520129242 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 80807924209533053443) ^ 636282867791598846 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 80807924209533053443) ^ 1642070354382822 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 80807924209533053443) ^ 344651305362 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_84158409568047286067 : Nat.Prime 84158409568047286067 := by
  apply lucas_primality 84158409568047286067 (2 : ZMod 84158409568047286067)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (1151, 1), (7502771, 1), (696101339, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (1151, 1), (7502771, 1), (696101339, 1)] : List FactorBlock).map factorBlockValue).prod) = 84158409568047286067 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_7
      · exact prime_sixtyNineBO_1151
      · exact prime_sixtyNineBO_7502771
      · exact prime_sixtyNineBO_696101339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 84158409568047286067) ^ 42079204784023643033 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 84158409568047286067) ^ 12022629938292469438 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 84158409568047286067) ^ 73117645150345166 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 84158409568047286067) ^ 11216976976646 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 84158409568047286067) ^ 120899651894 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_103539601359502903057 : Nat.Prime 103539601359502903057 := by
  apply lucas_primality 103539601359502903057 (5 : ZMod 103539601359502903057)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (7, 1), (11, 1), (1013, 1), (27654453511147, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (7, 1), (11, 1), (1013, 1), (27654453511147, 1)] : List FactorBlock).map factorBlockValue).prod) = 103539601359502903057 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_7
      · exact prime_sixtyNineBO_11
      · exact prime_sixtyNineBO_1013
      · exact prime_sixtyNineBO_27654453511147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 103539601359502903057) ^ 51769800679751451528 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 103539601359502903057) ^ 34513200453167634352 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 103539601359502903057) ^ 14791371622786129008 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 103539601359502903057) ^ 9412691032682082096 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 103539601359502903057) ^ 102210860177199312 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 103539601359502903057) ^ 3744048 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_197886840030987219709 : Nat.Prime 197886840030987219709 := by
  apply lucas_primality 197886840030987219709 (10 : ZMod 197886840030987219709)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (16490570002582268309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (16490570002582268309, 1)] : List FactorBlock).map factorBlockValue).prod) = 197886840030987219709 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_16490570002582268309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 197886840030987219709) ^ 98943420015493609854 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (10 : ZMod 197886840030987219709) ^ 65962280010329073236 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (10 : ZMod 197886840030987219709) ^ 12 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_206874480402436933423 : Nat.Prime 206874480402436933423 := by
  apply lucas_primality 206874480402436933423 (3 : ZMod 206874480402436933423)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 1), (167, 1), (7057, 1), (44963, 1), (10328167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 1), (167, 1), (7057, 1), (44963, 1), (10328167, 1)] : List FactorBlock).map factorBlockValue).prod) = 206874480402436933423 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_7
      · exact prime_sixtyNineBO_167
      · exact prime_sixtyNineBO_7057
      · exact prime_sixtyNineBO_44963
      · exact prime_sixtyNineBO_10328167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 206874480402436933423) ^ 103437240201218466711 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 206874480402436933423) ^ 68958160134145644474 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 206874480402436933423) ^ 29553497200348133346 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 206874480402436933423) ^ 1238769343727167266 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 206874480402436933423) ^ 29314791044698446 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 206874480402436933423) ^ 4600993714886394 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 206874480402436933423) ^ 20030125423266 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_268963350415569243163 : Nat.Prime 268963350415569243163 := by
  apply lucas_primality 268963350415569243163 (2 : ZMod 268963350415569243163)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (521, 1), (23209, 1), (411912711527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (521, 1), (23209, 1), (411912711527, 1)] : List FactorBlock).map factorBlockValue).prod) = 268963350415569243163 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_521
      · exact prime_sixtyNineBO_23209
      · exact prime_sixtyNineBO_411912711527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 268963350415569243163) ^ 134481675207784621581 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 268963350415569243163) ^ 89654450138523081054 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 268963350415569243163) ^ 516244434578827722 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 268963350415569243163) ^ 11588752226100618 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 268963350415569243163) ^ 652962006 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_463144736553392806681 : Nat.Prime 463144736553392806681 := by
  apply lucas_primality 463144736553392806681 (14 : ZMod 463144736553392806681)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (17, 1), (37, 1), (6135992800124441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (17, 1), (37, 1), (6135992800124441, 1)] : List FactorBlock).map factorBlockValue).prod) = 463144736553392806681 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_5
      · exact prime_sixtyNineBO_17
      · exact prime_sixtyNineBO_37
      · exact prime_sixtyNineBO_6135992800124441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 463144736553392806681) ^ 231572368276696403340 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (14 : ZMod 463144736553392806681) ^ 154381578851130935560 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (14 : ZMod 463144736553392806681) ^ 92628947310678561336 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (14 : ZMod 463144736553392806681) ^ 27243808032552518040 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (14 : ZMod 463144736553392806681) ^ 12517425312253859640 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (14 : ZMod 463144736553392806681) ^ 75480 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_762878940652318588601 : Nat.Prime 762878940652318588601 := by
  apply lucas_primality 762878940652318588601 (6 : ZMod 762878940652318588601)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (1291, 1), (2954604727545773, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (1291, 1), (2954604727545773, 1)] : List FactorBlock).map factorBlockValue).prod) = 762878940652318588601 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_5
      · exact prime_sixtyNineBO_1291
      · exact prime_sixtyNineBO_2954604727545773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 762878940652318588601) ^ 381439470326159294300 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (6 : ZMod 762878940652318588601) ^ 152575788130463717720 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (6 : ZMod 762878940652318588601) ^ 590920945509154600 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (6 : ZMod 762878940652318588601) ^ 258200 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_1176871321384713868171 : Nat.Prime 1176871321384713868171 := by
  apply lucas_primality 1176871321384713868171 (11 : ZMod 1176871321384713868171)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (101, 1), (6547, 1), (59325855612437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (101, 1), (6547, 1), (59325855612437, 1)] : List FactorBlock).map factorBlockValue).prod) = 1176871321384713868171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_5
      · exact prime_sixtyNineBO_101
      · exact prime_sixtyNineBO_6547
      · exact prime_sixtyNineBO_59325855612437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 1176871321384713868171) ^ 588435660692356934085 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (11 : ZMod 1176871321384713868171) ^ 392290440461571289390 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (11 : ZMod 1176871321384713868171) ^ 235374264276942773634 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (11 : ZMod 1176871321384713868171) ^ 11652191300838751170 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (11 : ZMod 1176871321384713868171) ^ 179757342505684110 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (11 : ZMod 1176871321384713868171) ^ 19837410 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_1395918287707855858417 : Nat.Prime 1395918287707855858417 := by
  apply lucas_primality 1395918287707855858417 (5 : ZMod 1395918287707855858417)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (409, 1), (433, 1), (54737669175487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (409, 1), (433, 1), (54737669175487, 1)] : List FactorBlock).map factorBlockValue).prod) = 1395918287707855858417 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_409
      · exact prime_sixtyNineBO_433
      · exact prime_sixtyNineBO_54737669175487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1395918287707855858417) ^ 697959143853927929208 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 1395918287707855858417) ^ 465306095902618619472 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 1395918287707855858417) ^ 3413003148429965424 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 1395918287707855858417) ^ 3223829763759482352 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 1395918287707855858417) ^ 25501968 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_1525757881304637177203 : Nat.Prime 1525757881304637177203 := by
  apply lucas_primality 1525757881304637177203 (2 : ZMod 1525757881304637177203)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (762878940652318588601, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (762878940652318588601, 1)] : List FactorBlock).map factorBlockValue).prod) = 1525757881304637177203 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_762878940652318588601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 1525757881304637177203) ^ 762878940652318588601 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 1525757881304637177203) ^ 2 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_2879055542277063148823 : Nat.Prime 2879055542277063148823 := by
  apply lucas_primality 2879055542277063148823 (5 : ZMod 2879055542277063148823)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (75764619533606924969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (75764619533606924969, 1)] : List FactorBlock).map factorBlockValue).prod) = 2879055542277063148823 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_19
      · exact prime_sixtyNineBO_75764619533606924969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 2879055542277063148823) ^ 1439527771138531574411 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 2879055542277063148823) ^ 151529239067213849938 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 2879055542277063148823) ^ 38 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_3970850737547832043559 : Nat.Prime 3970850737547832043559 := by
  apply lucas_primality 3970850737547832043559 (11 : ZMod 3970850737547832043559)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (409, 1), (140407, 1), (34573352859533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (409, 1), (140407, 1), (34573352859533, 1)] : List FactorBlock).map factorBlockValue).prod) = 3970850737547832043559 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_409
      · exact prime_sixtyNineBO_140407
      · exact prime_sixtyNineBO_34573352859533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 3970850737547832043559) ^ 1985425368773916021779 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (11 : ZMod 3970850737547832043559) ^ 9708681509896899862 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (11 : ZMod 3970850737547832043559) ^ 28281002639097994 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (11 : ZMod 3970850737547832043559) ^ 114852926 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_5070473542817781875417 : Nat.Prime 5070473542817781875417 := by
  apply lucas_primality 5070473542817781875417 (3 : ZMod 5070473542817781875417)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (607, 1), (87613, 1), (11917942654697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (607, 1), (87613, 1), (11917942654697, 1)] : List FactorBlock).map factorBlockValue).prod) = 5070473542817781875417 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_607
      · exact prime_sixtyNineBO_87613
      · exact prime_sixtyNineBO_11917942654697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 5070473542817781875417) ^ 2535236771408890937708 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 5070473542817781875417) ^ 8353333678447746088 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 5070473542817781875417) ^ 57873529531208632 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 5070473542817781875417) ^ 425448728 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_5071646212765762711273 : Nat.Prime 5071646212765762711273 := by
  apply lucas_primality 5071646212765762711273 (5 : ZMod 5071646212765762711273)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (18521, 1), (11409675082261943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (18521, 1), (11409675082261943, 1)] : List FactorBlock).map factorBlockValue).prod) = 5071646212765762711273 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_18521
      · exact prime_sixtyNineBO_11409675082261943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 5071646212765762711273) ^ 2535823106382881355636 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 5071646212765762711273) ^ 1690548737588587570424 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 5071646212765762711273) ^ 273832201974286632 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 5071646212765762711273) ^ 444504 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_5376318287488599375131 : Nat.Prime 5376318287488599375131 := by
  apply lucas_primality 5376318287488599375131 (2 : ZMod 5376318287488599375131)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (29, 1), (619, 1), (1761762670108039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (29, 1), (619, 1), (1761762670108039, 1)] : List FactorBlock).map factorBlockValue).prod) = 5376318287488599375131 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_5
      · exact prime_sixtyNineBO_17
      · exact prime_sixtyNineBO_29
      · exact prime_sixtyNineBO_619
      · exact prime_sixtyNineBO_1761762670108039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5376318287488599375131) ^ 2688159143744299687565 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 5376318287488599375131) ^ 1075263657497719875026 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 5376318287488599375131) ^ 316254016911094080890 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 5376318287488599375131) ^ 185390285775468943970 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 5376318287488599375131) ^ 8685489963632632270 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 5376318287488599375131) ^ 3051670 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_32290431511864519916323 : Nat.Prime 32290431511864519916323 := by
  apply lucas_primality 32290431511864519916323 (3 : ZMod 32290431511864519916323)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (37, 1), (6977, 1), (259309, 1), (4729177771, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (37, 1), (6977, 1), (259309, 1), (4729177771, 1)] : List FactorBlock).map factorBlockValue).prod) = 32290431511864519916323 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_17
      · exact prime_sixtyNineBO_37
      · exact prime_sixtyNineBO_6977
      · exact prime_sixtyNineBO_259309
      · exact prime_sixtyNineBO_4729177771
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 32290431511864519916323) ^ 16145215755932259958161 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 32290431511864519916323) ^ 10763477170621506638774 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 32290431511864519916323) ^ 1899437147756736465666 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 32290431511864519916323) ^ 872714365185527565306 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 32290431511864519916323) ^ 4628125485432781986 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 32290431511864519916323) ^ 124524916265399658 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 32290431511864519916323) ^ 6827916622182 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_50713561471351447158277 : Nat.Prime 50713561471351447158277 := by
  apply lucas_primality 50713561471351447158277 (2 : ZMod 50713561471351447158277)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (617, 1), (6849481560150114419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (617, 1), (6849481560150114419, 1)] : List FactorBlock).map factorBlockValue).prod) = 50713561471351447158277 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_617
      · exact prime_sixtyNineBO_6849481560150114419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 50713561471351447158277) ^ 25356780735675723579138 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 50713561471351447158277) ^ 16904520490450482386092 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 50713561471351447158277) ^ 82193778721801373028 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 50713561471351447158277) ^ 7404 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_105110700944587991313341 : Nat.Prime 105110700944587991313341 := by
  apply lucas_primality 105110700944587991313341 (2 : ZMod 105110700944587991313341)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (26267, 1), (79532617, 1), (2515713553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (26267, 1), (79532617, 1), (2515713553, 1)] : List FactorBlock).map factorBlockValue).prod) = 105110700944587991313341 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_5
      · exact prime_sixtyNineBO_26267
      · exact prime_sixtyNineBO_79532617
      · exact prime_sixtyNineBO_2515713553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 105110700944587991313341) ^ 52555350472293995656670 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 105110700944587991313341) ^ 21022140188917598262668 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 105110700944587991313341) ^ 4001625649849164020 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 105110700944587991313341) ^ 1321604957933020 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 105110700944587991313341) ^ 41781665014780 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_168635159026128931685669 : Nat.Prime 168635159026128931685669 := by
  apply lucas_primality 168635159026128931685669 (2 : ZMod 168635159026128931685669)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (470201, 1), (45643987, 1), (280622813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (470201, 1), (45643987, 1), (280622813, 1)] : List FactorBlock).map factorBlockValue).prod) = 168635159026128931685669 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_7
      · exact prime_sixtyNineBO_470201
      · exact prime_sixtyNineBO_45643987
      · exact prime_sixtyNineBO_280622813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 168635159026128931685669) ^ 84317579513064465842834 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 168635159026128931685669) ^ 24090737003732704526524 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 168635159026128931685669) ^ 358644832797312068 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 168635159026128931685669) ^ 3694575564271564 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 168635159026128931685669) ^ 600931753278836 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_226878448668079708694749 : Nat.Prime 226878448668079708694749 := by
  apply lucas_primality 226878448668079708694749 (6 : ZMod 226878448668079708694749)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (41, 1), (92576929, 1), (4981101266261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (41, 1), (92576929, 1), (4981101266261, 1)] : List FactorBlock).map factorBlockValue).prod) = 226878448668079708694749 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_41
      · exact prime_sixtyNineBO_92576929
      · exact prime_sixtyNineBO_4981101266261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 226878448668079708694749) ^ 113439224334039854347374 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (6 : ZMod 226878448668079708694749) ^ 75626149556026569564916 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (6 : ZMod 226878448668079708694749) ^ 5533620699221456309628 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (6 : ZMod 226878448668079708694749) ^ 2450701823000412 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (6 : ZMod 226878448668079708694749) ^ 45547849068 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_256089101460992381213083 : Nat.Prime 256089101460992381213083 := by
  apply lucas_primality 256089101460992381213083 (3 : ZMod 256089101460992381213083)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (3119, 1), (5009, 1), (82786495709329, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (3119, 1), (5009, 1), (82786495709329, 1)] : List FactorBlock).map factorBlockValue).prod) = 256089101460992381213083 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_11
      · exact prime_sixtyNineBO_3119
      · exact prime_sixtyNineBO_5009
      · exact prime_sixtyNineBO_82786495709329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 256089101460992381213083) ^ 128044550730496190606541 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 256089101460992381213083) ^ 85363033820330793737694 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 256089101460992381213083) ^ 23280827405544761928462 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 256089101460992381213083) ^ 82106156287589734278 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 256089101460992381213083) ^ 51125793863244635898 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 256089101460992381213083) ^ 3093368058 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_449132664595221851216389 : Nat.Prime 449132664595221851216389 := by
  apply lucas_primality 449132664595221851216389 (6 : ZMod 449132664595221851216389)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (2879055542277063148823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (2879055542277063148823, 1)] : List FactorBlock).map factorBlockValue).prod) = 449132664595221851216389 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_13
      · exact prime_sixtyNineBO_2879055542277063148823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 449132664595221851216389) ^ 224566332297610925608194 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (6 : ZMod 449132664595221851216389) ^ 149710888198407283738796 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (6 : ZMod 449132664595221851216389) ^ 34548666507324757785876 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (6 : ZMod 449132664595221851216389) ^ 156 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_786422718407175676107277 : Nat.Prime 786422718407175676107277 := by
  apply lucas_primality 786422718407175676107277 (2 : ZMod 786422718407175676107277)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (811, 1), (80807924209533053443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (811, 1), (80807924209533053443, 1)] : List FactorBlock).map factorBlockValue).prod) = 786422718407175676107277 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_811
      · exact prime_sixtyNineBO_80807924209533053443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 786422718407175676107277) ^ 393211359203587838053638 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 786422718407175676107277) ^ 262140906135725225369092 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 786422718407175676107277) ^ 969695090514396641316 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 786422718407175676107277) ^ 9732 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_855188332142727120854219 : Nat.Prime 855188332142727120854219 := by
  apply lucas_primality 855188332142727120854219 (2 : ZMod 855188332142727120854219)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (55639, 1), (479513263, 1), (2289569291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (55639, 1), (479513263, 1), (2289569291, 1)] : List FactorBlock).map factorBlockValue).prod) = 855188332142727120854219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_7
      · exact prime_sixtyNineBO_55639
      · exact prime_sixtyNineBO_479513263
      · exact prime_sixtyNineBO_2289569291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 855188332142727120854219) ^ 427594166071363560427109 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 855188332142727120854219) ^ 122169761734675302979174 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 855188332142727120854219) ^ 15370303782288091462 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 855188332142727120854219) ^ 1783450840947286 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 855188332142727120854219) ^ 373514938160798 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_2170162676326010642678477 : Nat.Prime 2170162676326010642678477 := by
  apply lucas_primality 2170162676326010642678477 (2 : ZMod 2170162676326010642678477)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (107, 1), (5070473542817781875417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (107, 1), (5070473542817781875417, 1)] : List FactorBlock).map factorBlockValue).prod) = 2170162676326010642678477 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_107
      · exact prime_sixtyNineBO_5070473542817781875417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2170162676326010642678477) ^ 1085081338163005321339238 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2170162676326010642678477) ^ 20281894171271127501668 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2170162676326010642678477) ^ 428 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_3113128339302959092439473 : Nat.Prime 3113128339302959092439473 := by
  apply lucas_primality 3113128339302959092439473 (10 : ZMod 3113128339302959092439473)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (71, 1), (408387059, 1), (2236791311701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (71, 1), (408387059, 1), (2236791311701, 1)] : List FactorBlock).map factorBlockValue).prod) = 3113128339302959092439473 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_71
      · exact prime_sixtyNineBO_408387059
      · exact prime_sixtyNineBO_2236791311701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 3113128339302959092439473) ^ 1556564169651479546219736 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (10 : ZMod 3113128339302959092439473) ^ 1037709446434319697479824 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (10 : ZMod 3113128339302959092439473) ^ 43846878018351536513232 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (10 : ZMod 3113128339302959092439473) ^ 7622984790277008 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (10 : ZMod 3113128339302959092439473) ^ 1391783097072 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_3323138952382871926767311 : Nat.Prime 3323138952382871926767311 := by
  apply lucas_primality 3323138952382871926767311 (7 : ZMod 3323138952382871926767311)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (113, 1), (191, 1), (379, 1), (40625384123447983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (113, 1), (191, 1), (379, 1), (40625384123447983, 1)] : List FactorBlock).map factorBlockValue).prod) = 3323138952382871926767311 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_5
      · exact prime_sixtyNineBO_113
      · exact prime_sixtyNineBO_191
      · exact prime_sixtyNineBO_379
      · exact prime_sixtyNineBO_40625384123447983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 3323138952382871926767311) ^ 1661569476191435963383655 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (7 : ZMod 3323138952382871926767311) ^ 664627790476574385353462 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (7 : ZMod 3323138952382871926767311) ^ 29408309313122760413870 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (7 : ZMod 3323138952382871926767311) ^ 17398633258549067679410 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (7 : ZMod 3323138952382871926767311) ^ 8768176655363778170890 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (7 : ZMod 3323138952382871926767311) ^ 81799570 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_3558248931479313445794467 : Nat.Prime 3558248931479313445794467 := by
  apply lucas_primality 3558248931479313445794467 (2 : ZMod 3558248931479313445794467)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (293, 1), (10308673, 1), (589028010947197, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (293, 1), (10308673, 1), (589028010947197, 1)] : List FactorBlock).map factorBlockValue).prod) = 3558248931479313445794467 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_293
      · exact prime_sixtyNineBO_10308673
      · exact prime_sixtyNineBO_589028010947197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3558248931479313445794467) ^ 1779124465739656722897233 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 3558248931479313445794467) ^ 12144194305390148279162 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 3558248931479313445794467) ^ 345170414415057442 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 3558248931479313445794467) ^ 6040882378 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_4634496932342616751408019 : Nat.Prime 4634496932342616751408019 := by
  apply lucas_primality 4634496932342616751408019 (2 : ZMod 4634496932342616751408019)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (22679, 1), (958155329, 1), (9694381309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (22679, 1), (958155329, 1), (9694381309, 1)] : List FactorBlock).map factorBlockValue).prod) = 4634496932342616751408019 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_11
      · exact prime_sixtyNineBO_22679
      · exact prime_sixtyNineBO_958155329
      · exact prime_sixtyNineBO_9694381309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4634496932342616751408019) ^ 2317248466171308375704009 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 4634496932342616751408019) ^ 421317902940237886491638 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 4634496932342616751408019) ^ 204351908476679604542 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 4634496932342616751408019) ^ 4836895221549842 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 4634496932342616751408019) ^ 478060103540602 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_10152634101194118239985557 : Nat.Prime 10152634101194118239985557 := by
  apply lucas_primality 10152634101194118239985557 (2 : ZMod 10152634101194118239985557)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (191307829759, 1), (13267405356571, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (191307829759, 1), (13267405356571, 1)] : List FactorBlock).map factorBlockValue).prod) = 10152634101194118239985557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_191307829759
      · exact prime_sixtyNineBO_13267405356571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 10152634101194118239985557) ^ 5076317050597059119992778 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 10152634101194118239985557) ^ 53069621426284 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 10152634101194118239985557) ^ 765231319036 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_10907396042665428541019381 : Nat.Prime 10907396042665428541019381 := by
  apply lucas_primality 10907396042665428541019381 (2 : ZMod 10907396042665428541019381)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (29, 1), (31, 1), (193, 1), (1597, 1), (1968199739166511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (29, 1), (31, 1), (193, 1), (1597, 1), (1968199739166511, 1)] : List FactorBlock).map factorBlockValue).prod) = 10907396042665428541019381 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_5
      · exact prime_sixtyNineBO_29
      · exact prime_sixtyNineBO_31
      · exact prime_sixtyNineBO_193
      · exact prime_sixtyNineBO_1597
      · exact prime_sixtyNineBO_1968199739166511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 10907396042665428541019381) ^ 5453698021332714270509690 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 10907396042665428541019381) ^ 2181479208533085708203876 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 10907396042665428541019381) ^ 376117104919497535897220 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 10907396042665428541019381) ^ 351851485247271888419980 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 10907396042665428541019381) ^ 56515005402411546844660 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 10907396042665428541019381) ^ 6829928642871276481540 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 10907396042665428541019381) ^ 5541813580 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_13096229732396008999563967 : Nat.Prime 13096229732396008999563967 := by
  apply lucas_primality 13096229732396008999563967 (5 : ZMod 13096229732396008999563967)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (7069, 1), (2210828843, 1), (19951883069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (7069, 1), (2210828843, 1), (19951883069, 1)] : List FactorBlock).map factorBlockValue).prod) = 13096229732396008999563967 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_7
      · exact prime_sixtyNineBO_7069
      · exact prime_sixtyNineBO_2210828843
      · exact prime_sixtyNineBO_19951883069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 13096229732396008999563967) ^ 6548114866198004499781983 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 13096229732396008999563967) ^ 4365409910798669666521322 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 13096229732396008999563967) ^ 1870889961770858428509138 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 13096229732396008999563967) ^ 1852628339566559485014 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 13096229732396008999563967) ^ 5923674179419962 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 13096229732396008999563967) ^ 656390661829014 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_20858198671208064448551253 : Nat.Prime 20858198671208064448551253 := by
  apply lucas_primality 20858198671208064448551253 (6 : ZMod 20858198671208064448551253)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (23, 1), (181, 1), (67121, 1), (6220577778297277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (23, 1), (181, 1), (67121, 1), (6220577778297277, 1)] : List FactorBlock).map factorBlockValue).prod) = 20858198671208064448551253 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_23
      · exact prime_sixtyNineBO_181
      · exact prime_sixtyNineBO_67121
      · exact prime_sixtyNineBO_6220577778297277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 20858198671208064448551253) ^ 10429099335604032224275626 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (6 : ZMod 20858198671208064448551253) ^ 6952732890402688149517084 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (6 : ZMod 20858198671208064448551253) ^ 906878203096002802110924 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (6 : ZMod 20858198671208064448551253) ^ 115238666691757262146692 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (6 : ZMod 20858198671208064448551253) ^ 310755183492618769812 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (6 : ZMod 20858198671208064448551253) ^ 3353096676 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_32003301295839442941657101 : Nat.Prime 32003301295839442941657101 := by
  apply lucas_primality 32003301295839442941657101 (2 : ZMod 32003301295839442941657101)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (691, 1), (463144736553392806681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (691, 1), (463144736553392806681, 1)] : List FactorBlock).map factorBlockValue).prod) = 32003301295839442941657101 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_5
      · exact prime_sixtyNineBO_691
      · exact prime_sixtyNineBO_463144736553392806681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 32003301295839442941657101) ^ 16001650647919721470828550 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 32003301295839442941657101) ^ 6400660259167888588331420 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 32003301295839442941657101) ^ 46314473655339280668100 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 32003301295839442941657101) ^ 69100 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_101086016112880718783499319 : Nat.Prime 101086016112880718783499319 := by
  apply lucas_primality 101086016112880718783499319 (3 : ZMod 101086016112880718783499319)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1907, 1), (7027, 1), (1257242877640270177, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1907, 1), (7027, 1), (1257242877640270177, 1)] : List FactorBlock).map factorBlockValue).prod) = 101086016112880718783499319 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_1907
      · exact prime_sixtyNineBO_7027
      · exact prime_sixtyNineBO_1257242877640270177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 101086016112880718783499319) ^ 50543008056440359391749659 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 101086016112880718783499319) ^ 33695338704293572927833106 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 101086016112880718783499319) ^ 53007874207069071202674 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 101086016112880718783499319) ^ 14385373005959971365234 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 101086016112880718783499319) ^ 80402934 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_111443189894938169478529987 : Nat.Prime 111443189894938169478529987 := by
  apply lucas_primality 111443189894938169478529987 (3 : ZMod 111443189894938169478529987)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (113143, 1), (4433153639, 1), (37030690603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (113143, 1), (4433153639, 1), (37030690603, 1)] : List FactorBlock).map factorBlockValue).prod) = 111443189894938169478529987 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_113143
      · exact prime_sixtyNineBO_4433153639
      · exact prime_sixtyNineBO_37030690603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 111443189894938169478529987) ^ 55721594947469084739264993 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 111443189894938169478529987) ^ 37147729964979389826176662 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 111443189894938169478529987) ^ 984976444808235325902 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 111443189894938169478529987) ^ 25138580561371374 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 111443189894938169478529987) ^ 3009481813064262 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_134392775952380131891736327 : Nat.Prime 134392775952380131891736327 := by
  apply lucas_primality 134392775952380131891736327 (5 : ZMod 134392775952380131891736327)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2081, 1), (32290431511864519916323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2081, 1), (32290431511864519916323, 1)] : List FactorBlock).map factorBlockValue).prod) = 134392775952380131891736327 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_2081
      · exact prime_sixtyNineBO_32290431511864519916323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 134392775952380131891736327) ^ 67196387976190065945868163 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 134392775952380131891736327) ^ 64580863023729039832646 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 134392775952380131891736327) ^ 4162 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_204965866841946583061014951 : Nat.Prime 204965866841946583061014951 := by
  apply lucas_primality 204965866841946583061014951 (6 : ZMod 204965866841946583061014951)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (13, 1), (105110700944587991313341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (13, 1), (105110700944587991313341, 1)] : List FactorBlock).map factorBlockValue).prod) = 204965866841946583061014951 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_5
      · exact prime_sixtyNineBO_13
      · exact prime_sixtyNineBO_105110700944587991313341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 204965866841946583061014951) ^ 102482933420973291530507475 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (6 : ZMod 204965866841946583061014951) ^ 68321955613982194353671650 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (6 : ZMod 204965866841946583061014951) ^ 40993173368389316612202990 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (6 : ZMod 204965866841946583061014951) ^ 15766605141688198697001150 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (6 : ZMod 204965866841946583061014951) ^ 1950 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_337092623979730330819355167 : Nat.Prime 337092623979730330819355167 := by
  apply lucas_primality 337092623979730330819355167 (3 : ZMod 337092623979730330819355167)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (47, 1), (2132759, 1), (560477726185536557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (47, 1), (2132759, 1), (560477726185536557, 1)] : List FactorBlock).map factorBlockValue).prod) = 337092623979730330819355167 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_47
      · exact prime_sixtyNineBO_2132759
      · exact prime_sixtyNineBO_560477726185536557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 337092623979730330819355167) ^ 168546311989865165409677583 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 337092623979730330819355167) ^ 112364207993243443606451722 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 337092623979730330819355167) ^ 7172183488930432570624578 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 337092623979730330819355167) ^ 158054718784321309074 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 337092623979730330819355167) ^ 601438038 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_1102383986528307298084918249 : Nat.Prime 1102383986528307298084918249 := by
  apply lucas_primality 1102383986528307298084918249 (7 : ZMod 1102383986528307298084918249)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (19, 1), (5639, 1), (144583, 1), (726367, 1), (4082184427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (19, 1), (5639, 1), (144583, 1), (726367, 1), (4082184427, 1)] : List FactorBlock).map factorBlockValue).prod) = 1102383986528307298084918249 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_19
      · exact prime_sixtyNineBO_5639
      · exact prime_sixtyNineBO_144583
      · exact prime_sixtyNineBO_726367
      · exact prime_sixtyNineBO_4082184427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1102383986528307298084918249) ^ 551191993264153649042459124 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (7 : ZMod 1102383986528307298084918249) ^ 367461328842769099361639416 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (7 : ZMod 1102383986528307298084918249) ^ 58020209817279331478153592 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (7 : ZMod 1102383986528307298084918249) ^ 195492815486488259990232 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (7 : ZMod 1102383986528307298084918249) ^ 7624575410167912535256 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (7 : ZMod 1102383986528307298084918249) ^ 1517668047320854744344 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (7 : ZMod 1102383986528307298084918249) ^ 270047570422596024 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_2549262968846710626821373451 : Nat.Prime 2549262968846710626821373451 := by
  apply lucas_primality 2549262968846710626821373451 (2 : ZMod 2549262968846710626821373451)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (1117, 1), (5071646212765762711273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (1117, 1), (5071646212765762711273, 1)] : List FactorBlock).map factorBlockValue).prod) = 2549262968846710626821373451 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_5
      · exact prime_sixtyNineBO_1117
      · exact prime_sixtyNineBO_5071646212765762711273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2549262968846710626821373451) ^ 1274631484423355313410686725 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2549262968846710626821373451) ^ 849754322948903542273791150 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2549262968846710626821373451) ^ 509852593769342125364274690 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2549262968846710626821373451) ^ 2282240795744593220072850 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (2 : ZMod 2549262968846710626821373451) ^ 502650 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_5826886785935338575591710743 : Nat.Prime 5826886785935338575591710743 := by
  apply lucas_primality 5826886785935338575591710743 (17 : ZMod 5826886785935338575591710743)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (631, 1), (1112147693, 1), (1383864297584779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (631, 1), (1112147693, 1), (1383864297584779, 1)] : List FactorBlock).map factorBlockValue).prod) = 5826886785935338575591710743 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_631
      · exact prime_sixtyNineBO_1112147693
      · exact prime_sixtyNineBO_1383864297584779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 5826886785935338575591710743) ^ 2913443392967669287795855371 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (17 : ZMod 5826886785935338575591710743) ^ 1942295595311779525197236914 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (17 : ZMod 5826886785935338575591710743) ^ 9234368915903864620589082 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (17 : ZMod 5826886785935338575591710743) ^ 5239310230655973294 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (17 : ZMod 5826886785935338575591710743) ^ 4210591165698 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_27192138334364913352761316813 : Nat.Prime 27192138334364913352761316813 := by
  apply lucas_primality 27192138334364913352761316813 (6 : ZMod 27192138334364913352761316813)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (23, 1), (9901, 1), (26687, 1), (48049, 1), (705469795159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (23, 1), (9901, 1), (26687, 1), (48049, 1), (705469795159, 1)] : List FactorBlock).map factorBlockValue).prod) = 27192138334364913352761316813 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_11
      · exact prime_sixtyNineBO_23
      · exact prime_sixtyNineBO_9901
      · exact prime_sixtyNineBO_26687
      · exact prime_sixtyNineBO_48049
      · exact prime_sixtyNineBO_705469795159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 27192138334364913352761316813) ^ 13596069167182456676380658406 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (6 : ZMod 27192138334364913352761316813) ^ 9064046111454971117587105604 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (6 : ZMod 27192138334364913352761316813) ^ 2472012575851355759341937892 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (6 : ZMod 27192138334364913352761316813) ^ 1182266884102822319685274644 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (6 : ZMod 27192138334364913352761316813) ^ 2746403225367630880998012 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (6 : ZMod 27192138334364913352761316813) ^ 1018928254744441613997876 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (6 : ZMod 27192138334364913352761316813) ^ 565925166691604681736588 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (6 : ZMod 27192138334364913352761316813) ^ 38544723701794068 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_40788207501547370029141975217 : Nat.Prime 40788207501547370029141975217 := by
  apply lucas_primality 40788207501547370029141975217 (3 : ZMod 40788207501547370029141975217)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (2549262968846710626821373451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (2549262968846710626821373451, 1)] : List FactorBlock).map factorBlockValue).prod) = 40788207501547370029141975217 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_2549262968846710626821373451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 40788207501547370029141975217) ^ 20394103750773685014570987608 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (3 : ZMod 40788207501547370029141975217) ^ 16 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_40788207501547370029141975223 : Nat.Prime 40788207501547370029141975223 := by
  apply lucas_primality 40788207501547370029141975223 (5 : ZMod 40788207501547370029141975223)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (29, 1), (283, 1), (50713561471351447158277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (29, 1), (283, 1), (50713561471351447158277, 1)] : List FactorBlock).map factorBlockValue).prod) = 40788207501547370029141975223 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_7
      · exact prime_sixtyNineBO_29
      · exact prime_sixtyNineBO_283
      · exact prime_sixtyNineBO_50713561471351447158277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 40788207501547370029141975223) ^ 20394103750773685014570987611 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 40788207501547370029141975223) ^ 5826886785935338575591710746 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 40788207501547370029141975223) ^ 1406489913846461035487654318 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 40788207501547370029141975223) ^ 144127941701580812823823234 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (5 : ZMod 40788207501547370029141975223) ^ 804286 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem prime_sixtyNineBO_81576415003094740058283950461 : Nat.Prime 81576415003094740058283950461 := by
  apply lucas_primality 81576415003094740058283950461 (30 : ZMod 81576415003094740058283950461)
  · rw [← sixtyNineBOFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (31, 1), (102533, 1), (12021788057, 1), (35581064731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (31, 1), (102533, 1), (12021788057, 1), (35581064731, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_sixtyNineBO_2
      · exact prime_sixtyNineBO_3
      · exact prime_sixtyNineBO_5
      · exact prime_sixtyNineBO_31
      · exact prime_sixtyNineBO_102533
      · exact prime_sixtyNineBO_12021788057
      · exact prime_sixtyNineBO_35581064731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (30 : ZMod 81576415003094740058283950461) ^ 40788207501547370029141975230 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (30 : ZMod 81576415003094740058283950461) ^ 27192138334364913352761316820 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (30 : ZMod 81576415003094740058283950461) ^ 16315283000618948011656790092 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (30 : ZMod 81576415003094740058283950461) ^ 2631497258164346453493030660 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (30 : ZMod 81576415003094740058283950461) ^ 795611315411572274860620 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (30 : ZMod 81576415003094740058283950461) ^ 6785713956718338780 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide
    · change (30 : ZMod 81576415003094740058283950461) ^ 2292691790417988660 ≠ 1
      rw [← sixtyNineBOFastPow_eq_pow]
      decide

private theorem phi_sixtyNineBO_81576415003094740058283950400 : Nat.totient 81576415003094740058283950400 = 21734235546034910153393479680 := by
  rw [← show ((([(2, 6), (3, 2), (5, 2), (1117, 1), (5071646212765762711273, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950400 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_2, prime_sixtyNineBO_3, prime_sixtyNineBO_5, prime_sixtyNineBO_1117, prime_sixtyNineBO_5071646212765762711273]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950401 : Nat.totient 81576415003094740058283950401 = 80825817846712571388948088512 := by
  rw [← show ((([(113, 1), (2819, 1), (256089101460992381213083, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950401 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_113, prime_sixtyNineBO_2819, prime_sixtyNineBO_256089101460992381213083]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950402 : Nat.totient 81576415003094740058283950402 = 34961320715612031453550264452 := by
  rw [← show ((([(2, 1), (7, 1), (5826886785935338575591710743, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950402 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_2, prime_sixtyNineBO_7, prime_sixtyNineBO_5826886785935338575591710743]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950403 : Nat.totient 81576415003094740058283950403 = 49423971941107281265776336000 := by
  rw [← show ((([(3, 1), (11, 1), (3037, 1), (182926493, 1), (4449685080592651, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950403 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_3, prime_sixtyNineBO_11, prime_sixtyNineBO_3037, prime_sixtyNineBO_182926493, prime_sixtyNineBO_4449685080592651]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950404 : Nat.totient 81576415003094740058283950404 = 40788207501493846521914026344 := by
  rw [← show ((([(2, 2), (762083263147, 1), (26760991530711283, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950404 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_2, prime_sixtyNineBO_762083263147, prime_sixtyNineBO_26760991530711283]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950405 : Nat.totient 81576415003094740058283950405 = 65260457461839687530900030656 := by
  rw [← show ((([(5, 1), (96749, 1), (168635159026128931685669, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950405 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_5, prime_sixtyNineBO_96749, prime_sixtyNineBO_168635159026128931685669]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950406 : Nat.totient 81576415003094740058283950406 = 26679079120500568882782654720 := by
  rw [← show ((([(2, 1), (3, 1), (53, 1), (3310719202057, 1), (77484555853781, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950406 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_2, prime_sixtyNineBO_3, prime_sixtyNineBO_53, prime_sixtyNineBO_3310719202057, prime_sixtyNineBO_77484555853781]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950407 : Nat.totient 81576415003094740058283950407 = 79839924511516686194940018720 := by
  rw [← show ((([(47, 1), (97429, 1), (30577619, 1), (582605858869831, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950407 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_47, prime_sixtyNineBO_97429, prime_sixtyNineBO_30577619, prime_sixtyNineBO_582605858869831]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950408 : Nat.totient 81576415003094740058283950408 = 40613889597090373099889740800 := by
  rw [← show ((([(2, 3), (271, 1), (2609, 1), (5531, 1), (45763, 1), (56978775693703, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950408 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_2, prime_sixtyNineBO_271, prime_sixtyNineBO_2609, prime_sixtyNineBO_5531, prime_sixtyNineBO_45763, prime_sixtyNineBO_56978775693703]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950409 : Nat.totient 81576415003094740058283950409 = 43082373026074766682906720000 := by
  rw [← show ((([(3, 2), (7, 1), (19, 1), (41, 1), (19751, 1), (84158409568047286067, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950409 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_3, prime_sixtyNineBO_7, prime_sixtyNineBO_19, prime_sixtyNineBO_41, prime_sixtyNineBO_19751, prime_sixtyNineBO_84158409568047286067]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950410 : Nat.totient 81576415003094740058283950410 = 32627145247909325114830125136 := by
  rw [← show ((([(2, 1), (5, 1), (9539, 1), (855188332142727120854219, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950410 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_2, prime_sixtyNineBO_5, prime_sixtyNineBO_9539, prime_sixtyNineBO_855188332142727120854219]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950411 : Nat.totient 81576415003094740058283950411 = 76777802355851610844811427328 := by
  rw [← show ((([(17, 1), (56593356222257, 1), (84791095060619, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950411 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_17, prime_sixtyNineBO_56593356222257, prime_sixtyNineBO_84791095060619]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950412 : Nat.totient 81576415003094740058283950412 = 25071593057341781497113600000 := by
  rw [← show ((([(2, 2), (3, 1), (13, 1), (929, 1), (13751, 1), (146078533, 1), (280222899511, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950412 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_2, prime_sixtyNineBO_3, prime_sixtyNineBO_13, prime_sixtyNineBO_929, prime_sixtyNineBO_13751, prime_sixtyNineBO_146078533, prime_sixtyNineBO_280222899511]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950413 : Nat.totient 81576415003094740058283950413 = 78029508571644538402861785264 := by
  rw [← show ((([(23, 1), (737683, 1), (42647584043, 1), (112738582699, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950413 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_23, prime_sixtyNineBO_737683, prime_sixtyNineBO_42647584043, prime_sixtyNineBO_112738582699]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950414 : Nat.totient 81576415003094740058283950414 = 37080188637770336390129068260 := by
  rw [← show ((([(2, 1), (11, 2), (337092623979730330819355167, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950414 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_2, prime_sixtyNineBO_11, prime_sixtyNineBO_337092623979730330819355167]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950415 : Nat.totient 81576415003094740058283950415 = 41857603098183094394730270720 := by
  rw [← show ((([(3, 1), (5, 1), (29, 1), (281, 1), (708359, 1), (3625423, 1), (259870473077, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950415 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_3, prime_sixtyNineBO_5, prime_sixtyNineBO_29, prime_sixtyNineBO_281, prime_sixtyNineBO_708359, prime_sixtyNineBO_3625423, prime_sixtyNineBO_259870473077]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950416 : Nat.totient 81576415003094740058283950416 = 34464217462339811488072980480 := by
  rw [← show ((([(2, 4), (7, 1), (71, 1), (7349, 1), (1395918287707855858417, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950416 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_2, prime_sixtyNineBO_7, prime_sixtyNineBO_71, prime_sixtyNineBO_7349, prime_sixtyNineBO_1395918287707855858417]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950417 : Nat.totient 81576415003094740058283950417 = 81210498774937666351687159632 := by
  rw [← show ((([(223, 1), (855607, 1), (10422043, 1), (41023486080779, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950417 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_223, prime_sixtyNineBO_855607, prime_sixtyNineBO_10422043, prime_sixtyNineBO_41023486080779]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950418 : Nat.totient 81576415003094740058283950418 = 27083803060514466444586122000 := by
  rw [← show ((([(2, 1), (3, 3), (251, 1), (441370723, 1), (13636207846012379, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950418 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_2, prime_sixtyNineBO_3, prime_sixtyNineBO_251, prime_sixtyNineBO_441370723, prime_sixtyNineBO_13636207846012379]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950419 : Nat.totient 81576415003094740058283950419 = 79679289071226736630184973576 := by
  rw [← show ((([(43, 1), (50963027279, 1), (37225534502073527, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950419 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_43, prime_sixtyNineBO_50963027279, prime_sixtyNineBO_37225534502073527]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950420 : Nat.totient 81576415003094740058283950420 = 32623228656126558912424166400 := by
  rw [← show ((([(2, 2), (5, 1), (4451, 1), (5193889, 1), (176434845614554139, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950420 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_2, prime_sixtyNineBO_5, prime_sixtyNineBO_4451, prime_sixtyNineBO_5193889, prime_sixtyNineBO_176434845614554139]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950421 : Nat.totient 81576415003094740058283950421 = 54384122145260369031250242560 := by
  rw [← show ((([(3, 1), (421397, 1), (2367857, 1), (22157063, 1), (1229940941, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950421 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_3, prime_sixtyNineBO_421397, prime_sixtyNineBO_2367857, prime_sixtyNineBO_22157063, prime_sixtyNineBO_1229940941]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950422 : Nat.totient 81576415003094740058283950422 = 40788176489464221708741480000 := by
  rw [← show ((([(2, 1), (2779771, 1), (3286091, 1), (10651931, 1), (419196521, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950422 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_2, prime_sixtyNineBO_2779771, prime_sixtyNineBO_3286091, prime_sixtyNineBO_10651931, prime_sixtyNineBO_419196521]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950423 : Nat.totient 81576415003094740058283950423 = 68776368620854553157404291040 := by
  rw [← show ((([(7, 1), (61, 1), (3378330571283, 1), (56550258880903, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950423 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_7, prime_sixtyNineBO_61, prime_sixtyNineBO_3378330571283, prime_sixtyNineBO_56550258880903]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950424 : Nat.totient 81576415003094740058283950424 = 27171630136604868950572596224 := by
  rw [← show ((([(2, 3), (3, 1), (2399, 1), (2963, 1), (2558951957, 1), (186865592489, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950424 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_2, prime_sixtyNineBO_3, prime_sixtyNineBO_2399, prime_sixtyNineBO_2963, prime_sixtyNineBO_2558951957, prime_sixtyNineBO_186865592489]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950425 : Nat.totient 81576415003094740058283950425 = 54644536305807751562273280000 := by
  rw [← show ((([(5, 2), (11, 1), (13, 1), (491, 1), (7607, 1), (41131, 1), (148533492461777, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950425 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_5, prime_sixtyNineBO_11, prime_sixtyNineBO_13, prime_sixtyNineBO_491, prime_sixtyNineBO_7607, prime_sixtyNineBO_41131, prime_sixtyNineBO_148533492461777]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950426 : Nat.totient 81576415003094740058283950426 = 39685823515019062731057056928 := by
  rw [← show ((([(2, 1), (37, 1), (1102383986528307298084918249, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950426 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_2, prime_sixtyNineBO_37, prime_sixtyNineBO_1102383986528307298084918249]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950427 : Nat.totient 81576415003094740058283950427 = 53302156801326415736952422400 := by
  rw [← show ((([(3, 2), (59, 1), (401, 1), (1973, 1), (7448470817, 1), (26069428837, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950427 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_3, prime_sixtyNineBO_59, prime_sixtyNineBO_401, prime_sixtyNineBO_1973, prime_sixtyNineBO_7448470817, prime_sixtyNineBO_26069428837]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950428 : Nat.totient 81576415003094740058283950428 = 36368432694878150366541440640 := by
  rw [← show ((([(2, 2), (17, 1), (19, 2), (3323138952382871926767311, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950428 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_2, prime_sixtyNineBO_17, prime_sixtyNineBO_19, prime_sixtyNineBO_3323138952382871926767311]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950429 : Nat.totient 81576415003094740058283950429 = 78944917744927283032268340480 := by
  rw [← show ((([(31, 1), (44347111964867, 1), (59338638787777, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950429 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_31, prime_sixtyNineBO_44347111964867, prime_sixtyNineBO_59338638787777]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950430 : Nat.totient 81576415003094740058283950430 = 18541869906529434931044898944 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (7, 1), (179, 1), (2170162676326010642678477, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950430 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_2, prime_sixtyNineBO_3, prime_sixtyNineBO_5, prime_sixtyNineBO_7, prime_sixtyNineBO_179, prime_sixtyNineBO_2170162676326010642678477]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950431 : Nat.totient 81576415003094740058283950431 = 81056805334715195760614112000 := by
  rw [← show ((([(157, 1), (5711903, 1), (169806601, 1), (535709774861, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950431 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_157, prime_sixtyNineBO_5711903, prime_sixtyNineBO_169806601, prime_sixtyNineBO_535709774861]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950432 : Nat.totient 81576415003094740058283950432 = 40788207501547370029141975200 := by
  rw [← show ((([(2, 5), (2549262968846710626821373451, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950432 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_2, prime_sixtyNineBO_2549262968846710626821373451]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950433 : Nat.totient 81576415003094740058283950433 = 54182104636504065267955634448 := by
  rw [← show ((([(3, 1), (269, 1), (101086016112880718783499319, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950433 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_3, prime_sixtyNineBO_269, prime_sixtyNineBO_101086016112880718783499319]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950434 : Nat.totient 81576415003094740058283950434 = 40788207501547370029141975216 := by
  rw [← show ((([(2, 1), (40788207501547370029141975217, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950434 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_2, prime_sixtyNineBO_40788207501547370029141975217]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950435 : Nat.totient 81576415003094740058283950435 = 65258581003993549424686303968 := by
  rw [← show ((([(5, 1), (25747, 1), (4005983, 1), (158182660729565987, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950435 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_5, prime_sixtyNineBO_25747, prime_sixtyNineBO_4005983, prime_sixtyNineBO_158182660729565987]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950436 : Nat.totient 81576415003094740058283950436 = 23641571529524772989028864000 := by
  rw [← show ((([(2, 2), (3, 2), (11, 1), (23, 1), (9901, 1), (26687, 1), (48049, 1), (705469795159, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950436 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_2, prime_sixtyNineBO_3, prime_sixtyNineBO_11, prime_sixtyNineBO_23, prime_sixtyNineBO_9901, prime_sixtyNineBO_26687, prime_sixtyNineBO_48049, prime_sixtyNineBO_705469795159]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950437 : Nat.totient 81576415003094740058283950437 = 68246455113768933920023269120 := by
  rw [← show ((([(7, 1), (67, 1), (109, 1), (105503, 1), (216594839, 1), (69831659341, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950437 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_7, prime_sixtyNineBO_67, prime_sixtyNineBO_109, prime_sixtyNineBO_105503, prime_sixtyNineBO_216594839, prime_sixtyNineBO_69831659341]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950438 : Nat.totient 81576415003094740058283950438 = 37595039115163307087421842016 := by
  rw [← show ((([(2, 1), (13, 1), (677, 1), (4634496932342616751408019, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950438 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_2, prime_sixtyNineBO_13, prime_sixtyNineBO_677, prime_sixtyNineBO_4634496932342616751408019]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950439 : Nat.totient 81576415003094740058283950439 = 54384276668729826705522633624 := by
  rw [← show ((([(3, 1), (27192138334364913352761316813, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950439 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_3, prime_sixtyNineBO_27192138334364913352761316813]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950440 : Nat.totient 81576415003094740058283950440 = 31944485572465622984220518400 := by
  rw [← show ((([(2, 3), (5, 1), (89, 1), (101, 1), (226878448668079708694749, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950440 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_2, prime_sixtyNineBO_5, prime_sixtyNineBO_89, prime_sixtyNineBO_101, prime_sixtyNineBO_226878448668079708694749]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950441 : Nat.totient 81576415003094740058283950441 = 80947782381043361372728467456 := by
  rw [← show ((([(137, 1), (3847, 1), (6673, 1), (55622647, 1), (417012511249, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950441 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_137, prime_sixtyNineBO_3847, prime_sixtyNineBO_6673, prime_sixtyNineBO_55622647, prime_sixtyNineBO_417012511249]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950442 : Nat.totient 81576415003094740058283950442 = 27185021836501954725869720240 := by
  rw [← show ((([(2, 1), (3, 1), (3821, 1), (3558248931479313445794467, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950442 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_2, prime_sixtyNineBO_3, prime_sixtyNineBO_3821, prime_sixtyNineBO_3558248931479313445794467]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950443 : Nat.totient 81576415003094740058283950443 = 81563318773362344049284380248 := by
  rw [← show ((([(6229, 1), (13096229732396008999563967, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950443 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_6229, prime_sixtyNineBO_13096229732396008999563967]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950444 : Nat.totient 81576415003094740058283950444 = 33636479635734446247986772864 := by
  rw [← show ((([(2, 2), (7, 2), (29, 1), (283, 1), (50713561471351447158277, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950444 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_2, prime_sixtyNineBO_7, prime_sixtyNineBO_29, prime_sixtyNineBO_283, prime_sixtyNineBO_50713561471351447158277]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950445 : Nat.totient 81576415003094740058283950445 = 40383416236750726426409041920 := by
  rw [← show ((([(3, 4), (5, 1), (17, 1), (73, 1), (10847, 1), (559859, 1), (4415153, 1), (6053461, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950445 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_3, prime_sixtyNineBO_5, prime_sixtyNineBO_17, prime_sixtyNineBO_73, prime_sixtyNineBO_10847, prime_sixtyNineBO_559859, prime_sixtyNineBO_4415153, prime_sixtyNineBO_6053461]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950446 : Nat.totient 81576415003094740058283950446 = 40788207501547370029141975222 := by
  rw [← show ((([(2, 1), (40788207501547370029141975223, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950446 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_2, prime_sixtyNineBO_40788207501547370029141975223]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950447 : Nat.totient 81576415003094740058283950447 = 70158061343936881771873200000 := by
  rw [← show ((([(11, 1), (19, 1), (1181, 1), (1831, 1), (53551, 1), (3370641025715603, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950447 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_11, prime_sixtyNineBO_19, prime_sixtyNineBO_1181, prime_sixtyNineBO_1831, prime_sixtyNineBO_53551, prime_sixtyNineBO_3370641025715603]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950448 : Nat.totient 81576415003094740058283950448 = 26833965862174012150015131648 := by
  rw [← show ((([(2, 4), (3, 1), (139, 1), (263, 1), (449, 1), (103539601359502903057, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950448 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_2, prime_sixtyNineBO_3, prime_sixtyNineBO_139, prime_sixtyNineBO_263, prime_sixtyNineBO_449, prime_sixtyNineBO_103539601359502903057]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950449 : Nat.totient 81576415003094740058283950449 = 81544411701798900615342290800 := by
  rw [← show ((([(2549, 1), (32003301295839442941657101, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950449 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_2549, prime_sixtyNineBO_32003301295839442941657101]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950450 : Nat.totient 81576415003094740058283950450 = 31833608919934908649690713600 := by
  rw [← show ((([(2, 1), (5, 2), (41, 1), (29429, 1), (4043899, 1), (334375885506319, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950450 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_2, prime_sixtyNineBO_5, prime_sixtyNineBO_41, prime_sixtyNineBO_29429, prime_sixtyNineBO_4043899, prime_sixtyNineBO_334375885506319]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950451 : Nat.totient 81576415003094740058283950451 = 42768685767984553778657034240 := by
  rw [← show ((([(3, 1), (7, 1), (13, 1), (173, 1), (3697, 1), (220681, 1), (300893, 1), (7036057619, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950451 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_3, prime_sixtyNineBO_7, prime_sixtyNineBO_13, prime_sixtyNineBO_173, prime_sixtyNineBO_3697, prime_sixtyNineBO_220681, prime_sixtyNineBO_300893, prime_sixtyNineBO_7036057619]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950452 : Nat.totient 81576415003094740058283950452 = 40165386562194353822307582720 := by
  rw [← show ((([(2, 2), (83, 1), (307, 1), (293453, 1), (2727404814486332041, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950452 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_2, prime_sixtyNineBO_83, prime_sixtyNineBO_307, prime_sixtyNineBO_293453, prime_sixtyNineBO_2727404814486332041]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950453 : Nat.totient 81576415003094740058283950453 = 81576007017060092931847889856 := by
  rw [← show ((([(206237, 1), (6558037, 1), (60314838659790037, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950453 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_206237, prime_sixtyNineBO_6558037, prime_sixtyNineBO_60314838659790037]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950454 : Nat.totient 81576415003094740058283950454 = 26613577622823442309905350400 := by
  rw [← show ((([(2, 1), (3, 2), (47, 1), (9603409, 1), (14740571, 1), (681168443591, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950454 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_2, prime_sixtyNineBO_3, prime_sixtyNineBO_47, prime_sixtyNineBO_9603409, prime_sixtyNineBO_14740571, prime_sixtyNineBO_681168443591]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950455 : Nat.totient 81576415003094740058283950455 = 65192487743851324197805578240 := by
  rw [← show ((([(5, 1), (1069, 1), (8837, 1), (299857, 1), (5759673424637371, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950455 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_5, prime_sixtyNineBO_1069, prime_sixtyNineBO_8837, prime_sixtyNineBO_299857, prime_sixtyNineBO_5759673424637371]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950456 : Nat.totient 81576415003094740058283950456 = 40788206674049448419197077504 := by
  rw [← show ((([(2, 3), (49291009, 1), (206874480402436933423, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950456 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_2, prime_sixtyNineBO_49291009, prime_sixtyNineBO_206874480402436933423]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950457 : Nat.totient 81576415003094740058283950457 = 54229099710918214583312313600 := by
  rw [← show ((([(3, 1), (421, 1), (2087, 1), (37128541, 1), (833548611678917, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950457 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_3, prime_sixtyNineBO_421, prime_sixtyNineBO_2087, prime_sixtyNineBO_37128541, prime_sixtyNineBO_833548611678917]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950458 : Nat.totient 81576415003094740058283950458 = 31781889702955298568325608000 := by
  rw [← show ((([(2, 1), (7, 1), (11, 1), (29611, 1), (569797, 1), (31395735542919031, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950458 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_2, prime_sixtyNineBO_7, prime_sixtyNineBO_11, prime_sixtyNineBO_29611, prime_sixtyNineBO_569797, prime_sixtyNineBO_31395735542919031]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950459 : Nat.totient 81576415003094740058283950459 = 76043549707946202073149085056 := by
  rw [← show ((([(23, 1), (53, 1), (149, 1), (449132664595221851216389, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950459 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_23, prime_sixtyNineBO_53, prime_sixtyNineBO_149, prime_sixtyNineBO_449132664595221851216389]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950460 : Nat.totient 81576415003094740058283950460 = 21051772743922841620740556800 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (31, 1), (102533, 1), (12021788057, 1), (35581064731, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950460 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_2, prime_sixtyNineBO_3, prime_sixtyNineBO_5, prime_sixtyNineBO_31, prime_sixtyNineBO_102533, prime_sixtyNineBO_12021788057, prime_sixtyNineBO_35581064731]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950461 : Nat.totient 81576415003094740058283950461 = 81576415003094740058283950460 := by
  rw [← show ((([(81576415003094740058283950461, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950461 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_81576415003094740058283950461]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950462 : Nat.totient 81576415003094740058283950462 = 37405856147099341065874053120 := by
  rw [← show ((([(2, 1), (17, 1), (43, 1), (467, 1), (6907, 1), (8291, 1), (632923, 1), (3296500253, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950462 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_2, prime_sixtyNineBO_17, prime_sixtyNineBO_43, prime_sixtyNineBO_467, prime_sixtyNineBO_6907, prime_sixtyNineBO_8291, prime_sixtyNineBO_632923, prime_sixtyNineBO_3296500253]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950463 : Nat.totient 81576415003094740058283950463 = 52901312288425325351518556160 := by
  rw [← show ((([(3, 2), (37, 1), (4289, 1), (67763, 1), (46941031, 1), (17956392383, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950463 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_3, prime_sixtyNineBO_37, prime_sixtyNineBO_4289, prime_sixtyNineBO_67763, prime_sixtyNineBO_46941031, prime_sixtyNineBO_17956392383]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950464 : Nat.totient 81576415003094740058283950464 = 37650501101258274690063747072 := by
  rw [← show ((([(2, 7), (13, 1), (247739, 1), (197886840030987219709, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950464 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_2, prime_sixtyNineBO_13, prime_sixtyNineBO_247739, prime_sixtyNineBO_197886840030987219709]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950465 : Nat.totient 81576415003094740058283950465 = 55926582371002480504315866624 := by
  rw [← show ((([(5, 1), (7, 1), (5113, 1), (94727, 1), (4812236858329330949, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950465 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_5, prime_sixtyNineBO_7, prime_sixtyNineBO_5113, prime_sixtyNineBO_94727, prime_sixtyNineBO_4812236858329330949]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950466 : Nat.totient 81576415003094740058283950466 = 25574586956481368413158396480 := by
  rw [← show ((([(2, 1), (3, 1), (19, 1), (167, 1), (797, 1), (5376318287488599375131, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950466 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_2, prime_sixtyNineBO_3, prime_sixtyNineBO_19, prime_sixtyNineBO_167, prime_sixtyNineBO_797, prime_sixtyNineBO_5376318287488599375131]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950467 : Nat.totient 81576415003094740058283950467 = 80953178067284395175530847880 := by
  rw [← show ((([(131, 1), (156823, 1), (3970850737547832043559, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950467 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_131, prime_sixtyNineBO_156823, prime_sixtyNineBO_3970850737547832043559]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950468 : Nat.totient 81576415003094740058283950468 = 40788207500234026859596671360 := by
  rw [← show ((([(2, 2), (31056779657, 1), (656671553715872281, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950468 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_2, prime_sixtyNineBO_31056779657, prime_sixtyNineBO_656671553715872281]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950469 : Nat.totient 81576415003094740058283950469 = 49050940654374012216171288000 := by
  rw [← show ((([(3, 1), (11, 1), (127, 1), (3589991, 1), (12641171, 1), (428910115519, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950469 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_3, prime_sixtyNineBO_11, prime_sixtyNineBO_127, prime_sixtyNineBO_3589991, prime_sixtyNineBO_12641171, prime_sixtyNineBO_428910115519]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950470 : Nat.totient 81576415003094740058283950470 = 32630565989620566174020656960 := by
  rw [← show ((([(2, 1), (5, 1), (2808783641, 1), (2904332459514447167, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950470 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_2, prime_sixtyNineBO_5, prime_sixtyNineBO_2808783641, prime_sixtyNineBO_2904332459514447167]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950471 : Nat.totient 81576415003094740058283950471 = 80735421033968429392985806848 := by
  rw [← show ((([(97, 1), (3688728073799, 1), (227990231938657, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950471 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_97, prime_sixtyNineBO_3688728073799, prime_sixtyNineBO_227990231938657]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950472 : Nat.totient 81576415003094740058283950472 = 23307546790013204559828008448 := by
  rw [← show ((([(2, 3), (3, 3), (7, 1), (65891129, 1), (818815161375170989, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950472 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_2, prime_sixtyNineBO_3, prime_sixtyNineBO_7, prime_sixtyNineBO_65891129, prime_sixtyNineBO_818815161375170989]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950473 : Nat.totient 81576415003094740058283950473 = 78763427644428006351076992528 := by
  rw [← show ((([(29, 1), (10458599, 1), (268963350415569243163, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950473 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_29, prime_sixtyNineBO_10458599, prime_sixtyNineBO_268963350415569243163]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950474 : Nat.totient 81576415003094740058283950474 = 40738268309936650174828270080 := by
  rw [← show ((([(2, 1), (821, 1), (157867, 1), (8506776979, 1), (36994320929, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950474 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_2, prime_sixtyNineBO_821, prime_sixtyNineBO_157867, prime_sixtyNineBO_8506776979, prime_sixtyNineBO_36994320929]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950475 : Nat.totient 81576415003094740058283950475 = 43505288512328271217032729600 := by
  rw [← show ((([(3, 1), (5, 2), (20399, 1), (32296256431, 1), (1650981814817, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950475 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_3, prime_sixtyNineBO_5, prime_sixtyNineBO_20399, prime_sixtyNineBO_32296256431, prime_sixtyNineBO_1650981814817]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950476 : Nat.totient 81576415003094740058283950476 = 40628724079103851165424611200 := by
  rw [← show ((([(2, 2), (331, 1), (1163, 1), (31481, 1), (1682861583759080083, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950476 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_2, prime_sixtyNineBO_331, prime_sixtyNineBO_1163, prime_sixtyNineBO_31481, prime_sixtyNineBO_1682861583759080083]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950477 : Nat.totient 81576415003094740058283950477 = 74348125065597440198496513600 := by
  rw [← show ((([(13, 1), (79, 1), (144621886931, 1), (549237458000821, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950477 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_13, prime_sixtyNineBO_79, prime_sixtyNineBO_144621886931, prime_sixtyNineBO_549237458000821]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950478 : Nat.totient 81576415003094740058283950478 = 27192138334364389840325449920 := by
  rw [← show ((([(2, 1), (3, 1), (71438978425273, 1), (190317239508181, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950478 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_2, prime_sixtyNineBO_3, prime_sixtyNineBO_71438978425273, prime_sixtyNineBO_190317239508181]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950479 : Nat.totient 81576415003094740058283950479 = 65065611295121869382300467200 := by
  rw [← show ((([(7, 1), (17, 1), (151, 1), (257, 1), (1213, 1), (1256369, 1), (11591231265179, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950479 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_7, prime_sixtyNineBO_17, prime_sixtyNineBO_151, prime_sixtyNineBO_257, prime_sixtyNineBO_1213, prime_sixtyNineBO_1256369, prime_sixtyNineBO_11591231265179]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950480 : Nat.totient 81576415003094740058283950480 = 29663662667694251628187107840 := by
  rw [← show ((([(2, 4), (5, 1), (11, 1), (60757, 1), (1525757881304637177203, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950480 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_2, prime_sixtyNineBO_5, prime_sixtyNineBO_11, prime_sixtyNineBO_60757, prime_sixtyNineBO_1525757881304637177203]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950481 : Nat.totient 81576415003094740058283950481 = 54361435729251283735625802720 := by
  rw [← show ((([(3, 2), (2381, 1), (620545218803, 1), (6134642754463, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950481 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_3, prime_sixtyNineBO_2381, prime_sixtyNineBO_620545218803, prime_sixtyNineBO_6134642754463]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950482 : Nat.totient 81576415003094740058283950482 = 39014781284224066085875812240 := by
  rw [← show ((([(2, 1), (23, 1), (1506877, 1), (1176871321384713868171, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950482 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_2, prime_sixtyNineBO_23, prime_sixtyNineBO_1506877, prime_sixtyNineBO_1176871321384713868171]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950483 : Nat.totient 81576415003094740058283950483 = 81555556804423531993835395320 := by
  rw [← show ((([(3911, 1), (20858198671208064448551253, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950483 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_3911, prime_sixtyNineBO_20858198671208064448551253]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950484 : Nat.totient 81576415003094740058283950484 = 26746365574785160674847196640 := by
  rw [← show ((([(2, 2), (3, 1), (61, 1), (111443189894938169478529987, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950484 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_2, prime_sixtyNineBO_3, prime_sixtyNineBO_61, prime_sixtyNineBO_111443189894938169478529987]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950485 : Nat.totient 81576415003094740058283950485 = 61733737924208719395018854400 := by
  rw [← show ((([(5, 1), (19, 1), (1049, 1), (2069, 1), (16223, 1), (24387869551319401, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950485 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_5, prime_sixtyNineBO_19, prime_sixtyNineBO_1049, prime_sixtyNineBO_2069, prime_sixtyNineBO_16223, prime_sixtyNineBO_24387869551319401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950486 : Nat.totient 81576415003094740058283950486 = 34368755864578629155534660256 := by
  rw [← show ((([(2, 1), (7, 1), (59, 1), (368994403, 1), (267648485123377037, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950486 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_2, prime_sixtyNineBO_7, prime_sixtyNineBO_59, prime_sixtyNineBO_368994403, prime_sixtyNineBO_267648485123377037]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950487 : Nat.totient 81576415003094740058283950487 = 53508201760424233002339059040 := by
  rw [← show ((([(3, 1), (71, 1), (487, 1), (786422718407175676107277, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950487 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_3, prime_sixtyNineBO_71, prime_sixtyNineBO_487, prime_sixtyNineBO_786422718407175676107277]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950488 : Nat.totient 81576415003094740058283950488 = 40788207384439095846438374496 := by
  rw [← show ((([(2, 3), (348294839, 1), (29277068545327605349, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950488 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_2, prime_sixtyNineBO_348294839, prime_sixtyNineBO_29277068545327605349]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950489 : Nat.totient 81576415003094740058283950489 = 81442022227142359926392213556 := by
  rw [← show ((([(607, 1), (134392775952380131891736327, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950489 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_607, prime_sixtyNineBO_134392775952380131891736327]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950490 : Nat.totient 81576415003094740058283950490 = 20044992906652733393397004800 := by
  rw [← show ((([(2, 1), (3, 2), (5, 1), (13, 1), (709, 1), (2851, 1), (34493344144497192683, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950490 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_2, prime_sixtyNineBO_3, prime_sixtyNineBO_5, prime_sixtyNineBO_13, prime_sixtyNineBO_709, prime_sixtyNineBO_2851, prime_sixtyNineBO_34493344144497192683]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950491 : Nat.totient 81576415003094740058283950491 = 70015872716427662761651200000 := by
  rw [← show ((([(11, 1), (31, 1), (41, 1), (51169, 1), (182711, 1), (1710691, 1), (364823819, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950491 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_11, prime_sixtyNineBO_31, prime_sixtyNineBO_41, prime_sixtyNineBO_51169, prime_sixtyNineBO_182711, prime_sixtyNineBO_1710691, prime_sixtyNineBO_364823819]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950492 : Nat.totient 81576415003094740058283950492 = 40781981244868764110957083200 := by
  rw [← show ((([(2, 2), (6551, 1), (3113128339302959092439473, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950492 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_2, prime_sixtyNineBO_6551, prime_sixtyNineBO_3113128339302959092439473]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950493 : Nat.totient 81576415003094740058283950493 = 46615079795853177670990687920 := by
  rw [← show ((([(3, 1), (7, 3), (3216691, 1), (24645628453965733987, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950493 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_3, prime_sixtyNineBO_7, prime_sixtyNineBO_3216691, prime_sixtyNineBO_24645628453965733987]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950494 : Nat.totient 81576415003094740058283950494 = 40659529574902487112146838528 := by
  rw [← show ((([(2, 1), (317, 1), (4808737, 1), (890685119, 1), (30041397797, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950494 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_2, prime_sixtyNineBO_317, prime_sixtyNineBO_4808737, prime_sixtyNineBO_890685119, prime_sixtyNineBO_30041397797]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950495 : Nat.totient 81576415003094740058283950495 = 65220521466071015573667211744 := by
  rw [← show ((([(5, 1), (1607, 1), (10152634101194118239985557, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950495 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_5, prime_sixtyNineBO_1607, prime_sixtyNineBO_10152634101194118239985557]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950496 : Nat.totient 81576415003094740058283950496 = 25583892856212216834819829760 := by
  rw [← show ((([(2, 5), (3, 1), (17, 1), (2939, 1), (28565507207, 1), (595391918411, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950496 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_2, prime_sixtyNineBO_3, prime_sixtyNineBO_17, prime_sixtyNineBO_2939, prime_sixtyNineBO_28565507207, prime_sixtyNineBO_595391918411]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950497 : Nat.totient 81576415003094740058283950497 = 81576415002942410097867987780 := by
  rw [← show ((([(535526311231, 1), (152329424889651487, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950497 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_535526311231, prime_sixtyNineBO_152329424889651487]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950498 : Nat.totient 81576415003094740058283950498 = 40583241634705423446080960100 := by
  rw [← show ((([(2, 1), (199, 1), (204965866841946583061014951, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950498 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_2, prime_sixtyNineBO_199, prime_sixtyNineBO_204965866841946583061014951]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950499 : Nat.totient 81576415003094740058283950499 = 54187943539961848991784279840 := by
  rw [← show ((([(3, 3), (277, 1), (10907396042665428541019381, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950499 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_3, prime_sixtyNineBO_277, prime_sixtyNineBO_10907396042665428541019381]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950500 : Nat.totient 81576415003094740058283950500 = 27211935779919000224464896000 := by
  rw [← show ((([(2, 2), (5, 3), (7, 1), (37, 1), (24781, 1), (414857, 1), (750209, 1), (81676163, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950500 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_2, prime_sixtyNineBO_5, prime_sixtyNineBO_7, prime_sixtyNineBO_37, prime_sixtyNineBO_24781, prime_sixtyNineBO_414857, prime_sixtyNineBO_750209, prime_sixtyNineBO_81676163]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_sixtyNineBO_81576415003094740058283950501 : Nat.totient 81576415003094740058283950501 = 79840745634626172297683259808 := by
  rw [← show ((([(47, 1), (82809689, 1), (20959726153797832547, 1)] : List FactorBlock).map factorBlockValue).prod) = 81576415003094740058283950501 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_sixtyNineBO_47, prime_sixtyNineBO_82809689, prime_sixtyNineBO_20959726153797832547]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64SixtyNineBO : certifiedKill 1 81576415003094740058283950399 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_sixtyNineBO_81576415003094740058283950400, phi_sixtyNineBO_81576415003094740058283950401, phi_sixtyNineBO_81576415003094740058283950402,
    phi_sixtyNineBO_81576415003094740058283950403, phi_sixtyNineBO_81576415003094740058283950404, phi_sixtyNineBO_81576415003094740058283950405,
    phi_sixtyNineBO_81576415003094740058283950406, phi_sixtyNineBO_81576415003094740058283950407, phi_sixtyNineBO_81576415003094740058283950408,
    phi_sixtyNineBO_81576415003094740058283950409, phi_sixtyNineBO_81576415003094740058283950410, phi_sixtyNineBO_81576415003094740058283950411,
    phi_sixtyNineBO_81576415003094740058283950412, phi_sixtyNineBO_81576415003094740058283950413, phi_sixtyNineBO_81576415003094740058283950414,
    phi_sixtyNineBO_81576415003094740058283950415, phi_sixtyNineBO_81576415003094740058283950416, phi_sixtyNineBO_81576415003094740058283950417,
    phi_sixtyNineBO_81576415003094740058283950418, phi_sixtyNineBO_81576415003094740058283950419, phi_sixtyNineBO_81576415003094740058283950420,
    phi_sixtyNineBO_81576415003094740058283950421, phi_sixtyNineBO_81576415003094740058283950422, phi_sixtyNineBO_81576415003094740058283950423,
    phi_sixtyNineBO_81576415003094740058283950424, phi_sixtyNineBO_81576415003094740058283950425, phi_sixtyNineBO_81576415003094740058283950426,
    phi_sixtyNineBO_81576415003094740058283950427, phi_sixtyNineBO_81576415003094740058283950428, phi_sixtyNineBO_81576415003094740058283950429,
    phi_sixtyNineBO_81576415003094740058283950430, phi_sixtyNineBO_81576415003094740058283950431, phi_sixtyNineBO_81576415003094740058283950432,
    phi_sixtyNineBO_81576415003094740058283950433, phi_sixtyNineBO_81576415003094740058283950434, phi_sixtyNineBO_81576415003094740058283950435,
    phi_sixtyNineBO_81576415003094740058283950436, phi_sixtyNineBO_81576415003094740058283950437, phi_sixtyNineBO_81576415003094740058283950438,
    phi_sixtyNineBO_81576415003094740058283950439, phi_sixtyNineBO_81576415003094740058283950440, phi_sixtyNineBO_81576415003094740058283950441,
    phi_sixtyNineBO_81576415003094740058283950442, phi_sixtyNineBO_81576415003094740058283950443, phi_sixtyNineBO_81576415003094740058283950444,
    phi_sixtyNineBO_81576415003094740058283950445, phi_sixtyNineBO_81576415003094740058283950446, phi_sixtyNineBO_81576415003094740058283950447,
    phi_sixtyNineBO_81576415003094740058283950448, phi_sixtyNineBO_81576415003094740058283950449, phi_sixtyNineBO_81576415003094740058283950450,
    phi_sixtyNineBO_81576415003094740058283950451, phi_sixtyNineBO_81576415003094740058283950452, phi_sixtyNineBO_81576415003094740058283950453,
    phi_sixtyNineBO_81576415003094740058283950454, phi_sixtyNineBO_81576415003094740058283950455, phi_sixtyNineBO_81576415003094740058283950456,
    phi_sixtyNineBO_81576415003094740058283950457, phi_sixtyNineBO_81576415003094740058283950458, phi_sixtyNineBO_81576415003094740058283950459,
    phi_sixtyNineBO_81576415003094740058283950460, phi_sixtyNineBO_81576415003094740058283950461, phi_sixtyNineBO_81576415003094740058283950462,
    phi_sixtyNineBO_81576415003094740058283950463, phi_sixtyNineBO_81576415003094740058283950464, phi_sixtyNineBO_81576415003094740058283950465,
    phi_sixtyNineBO_81576415003094740058283950466, phi_sixtyNineBO_81576415003094740058283950467, phi_sixtyNineBO_81576415003094740058283950468,
    phi_sixtyNineBO_81576415003094740058283950469, phi_sixtyNineBO_81576415003094740058283950470, phi_sixtyNineBO_81576415003094740058283950471,
    phi_sixtyNineBO_81576415003094740058283950472, phi_sixtyNineBO_81576415003094740058283950473, phi_sixtyNineBO_81576415003094740058283950474,
    phi_sixtyNineBO_81576415003094740058283950475, phi_sixtyNineBO_81576415003094740058283950476, phi_sixtyNineBO_81576415003094740058283950477,
    phi_sixtyNineBO_81576415003094740058283950478, phi_sixtyNineBO_81576415003094740058283950479, phi_sixtyNineBO_81576415003094740058283950480,
    phi_sixtyNineBO_81576415003094740058283950481, phi_sixtyNineBO_81576415003094740058283950482, phi_sixtyNineBO_81576415003094740058283950483,
    phi_sixtyNineBO_81576415003094740058283950484, phi_sixtyNineBO_81576415003094740058283950485, phi_sixtyNineBO_81576415003094740058283950486,
    phi_sixtyNineBO_81576415003094740058283950487, phi_sixtyNineBO_81576415003094740058283950488, phi_sixtyNineBO_81576415003094740058283950489,
    phi_sixtyNineBO_81576415003094740058283950490, phi_sixtyNineBO_81576415003094740058283950491, phi_sixtyNineBO_81576415003094740058283950492,
    phi_sixtyNineBO_81576415003094740058283950493, phi_sixtyNineBO_81576415003094740058283950494, phi_sixtyNineBO_81576415003094740058283950495,
    phi_sixtyNineBO_81576415003094740058283950496, phi_sixtyNineBO_81576415003094740058283950497, phi_sixtyNineBO_81576415003094740058283950498,
    phi_sixtyNineBO_81576415003094740058283950499, phi_sixtyNineBO_81576415003094740058283950500, phi_sixtyNineBO_81576415003094740058283950501]

end TotientTailPeriodKiller
end Erdos249257
